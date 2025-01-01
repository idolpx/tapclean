/*---------------------------------------------------------------------------
  palace_f2.c

  Part of project "Final TAP". 
  
  A Commodore 64 tape remastering and data extraction utility.

  (C) 2001-2006 Stewart Wilson, Subchrist Software.
   
  
   
   This program is free software; you can redistribute it and/or modify it under 
   the terms of the GNU General Public License as published by the Free Software 
   Foundation; either version 2 of the License, or (at your option) any later 
   version.
   
   This program is distributed in the hope that it will be useful, but WITHOUT ANY 
   WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A 
   PARTICULAR PURPOSE. See the GNU General Public License for more details.
   
   You should have received a copy of the GNU General Public License along with 
   this program; if not, write to the Free Software Foundation, Inc., 51 Franklin 
   St, Fifth Floor, Boston, MA 02110-1301 USA


  Note : Exactly the same as Palace F1 but block size is 1 byte smaller (262).

---------------------------------------------------------------------------*/

#include "../mydefs.h"
#include "../main.h"

#include <string.h>
#include <stdio.h>
#include <stdlib.h>

//#define PAL_F2_DEBUG

/* Try to find the CBM block with the Palace load orchestrator and main loader in it */
void find_and_copy_palace_loader (int *ib, int **buf, int *bufsz)
{
   /*
    * Example from Barbarian:
    *
    * SEI
    * LDA $D011
    * AND #$EF
    * STA $D011
    */
   unsigned char mainldr[9] = {0x78,0xAD,0x11,0xD0,0x29,0xEF,0x8D,0x11,0xD0};
   int i, j, k, cnt = 0;  /* Counters */

   /* Assume CBM block not found */
   *ib = -1;
   *buf = NULL;
   *bufsz = 0;

   /*
    * First we check if this is the genuine format/a known variant.
    * We use CBM DATA index # 3 to check as we assume the tape image contains
    * a single game. We also scan CBM DATA index # 4 to override load/end addr.
    * For compilations we should search and find the relevant file using the
    * search code found e.g. in Biturbo.
    */
   for (i=3; i<=4; i++)
   {
#ifdef PAL_F2_DEBUG
      printf("\nLooking for Palace loader in CBM DATA block index: %d", i);
#endif

      *ib = find_decode_block(CBM_DATA, i);

      if (*ib == -1) continue;
      if (blk[*ib]->cx < 9) continue;

      /* Look for the loader signature */
      for (j=0; j<sizeof(mainldr) / sizeof(mainldr[0]); j++)
         if (blk[*ib]->dd[j] != mainldr[j])
            break;

      /* Signature found? */
      if (j == 9)
      {
#ifdef PAL_F2_DEBUG
         printf("\nPalace loader found in CBM DATA block index: %d", i);
#endif

         /* Only allocate the buffer and copy the CBM DATA block once */
         if (*buf == NULL)
         {
            *bufsz = blk[*ib]->cx;

            *buf = (int *) malloc (*bufsz * sizeof(int));
            if (*buf != NULL)
            {
#ifdef PAL_F2_DEBUG
               printf("\nCopying %d bytes to an 'int' buffer", *bufsz);
#endif
               /* Make an 'int' copy for use in find_seq() */
               for (k = 0; k < *bufsz; k++)
                  (*buf)[k] = blk[*ib]->dd[k];
            }
            else
            {
#ifdef PAL_F2_DEBUG
               printf("\nBuffer allocation failed. Aborting search.");
#endif

               *ib = -1;

               return;
            }
         }

         /* Override load and end addresses of the CBM DATA blocks 3 and 4 */
         blk[*ib]->cs = 0x03e0;
         blk[*ib]->ce = blk[*ib]->cs + blk[*ib]->cx - 1;

#ifdef PAL_F2_DEBUG
         printf("\nOverridden CBM DATA block info at index: %d", i);
#endif

         /* Update the count of CBM DATA blocks found and patched */
         cnt++;
      }
   }

   if (cnt == 0)
      *ib = -1;
}

void get_palace_block_info (int *buf, int bufsz, int entrypointoffset, int blkindex, unsigned int *s, int *sb)
{
   /* Load snippets usually found in the loader orchestrator */
   int seq_load[18] = {
      /*
       * Example from Barbarian:
       *
       * LDA #$00 ; Load address LSB
       * STA $0080
       * LDA #$44 ; MSB of the same
       * STA $0081
       * LDA #$04 ; Number of sub-blocks
       * STA $0101
       * JSR $052E ; Load     
       */
      0xA9,XX,0x8D,0x80,0x00,0xA9,XX,0x8D,0x81,0x00,0xA9,XX,0x8D,0x01,0x01,0x20,XX,XX
   };

   int index, offset, deltaoffset, sumoffsets;

   index = 1;
   offset = 0;
   deltaoffset = 0;
   sumoffsets = entrypointoffset;

   /* Assume block info not found */
   *s = 0;
   *sb = 0;

#ifdef PAL_F2_DEBUG
   printf("\n---------------\nIndex: %d", blkindex);
#endif

   do
   {
      sumoffsets += (offset + deltaoffset);

#ifdef PAL_F2_DEBUG
      if (index == blkindex)
         printf("\nScanning for seq at index: %d", sumoffsets);
#endif

      offset = find_seq(buf + sumoffsets, bufsz - sumoffsets, seq_load, sizeof(seq_load) / sizeof(seq_load[0]));

      if (offset == -1) break;

#ifdef PAL_F2_DEBUG
      if (index == blkindex)
      {
         int i;

         printf("\nFound %d-th occurrence at relative offset: %d, absolute offset: %d", index, offset, sumoffsets + offset);

         printf("\nSequence:");
         for (i=0; i<sizeof(seq_load) / sizeof(seq_load[0]); i++)
            printf("%02X ", buf[sumoffsets + offset +i]);
      }
#endif

      index++;

      deltaoffset = sizeof(seq_load) / sizeof(seq_load[0]);
   }
   while (index <= blkindex);

   if (offset == -1)
   {
#ifdef PAL_F2_DEBUG
      printf("\nNo further file details found");
#endif
   }
   else
   {
      *s  = buf[sumoffsets + offset +  1];
      *s |= buf[sumoffsets + offset +  6] << 8;
      *sb = buf[sumoffsets + offset + 11];
   }
}

/*---------------------------------------------------------------------------
*/
void palacef2_search(void)
{
   int i,j,k,sof,sod,eod,eof,tmp,blocks;
   int z;
   int fsync[4]= {0x4A,0x50,0x47,0x29};    /* file sync sequence. */
   int bsync[5]= {0x4A,0x50,0x47,0x10};    /* block sync sequence. followed by block #. */

   int ib=-1, fa=-1;    /* condition variables */
   int *buf=NULL, bufsz=0;
   int b=1;
   unsigned int s=0;

   if(!quiet)
      msgout("  Palace Tape F2");

   for(i=20; i<tap.len-8; i++)
   {
      if((z=find_pilot(i,PAL_F2))>0)
      {
         sof=i;
         i=z;
         if(readttbyte(i, ft[PAL_F2].lp, ft[PAL_F2].sp, ft[PAL_F2].tp, ft[PAL_F2].en)==ft[PAL_F2].sv)
         {
            for(j=0,k=0; j<4; j++)  /* check file sync sequence... */
            {
               if(readttbyte(i+(j*8), ft[PAL_F2].lp, ft[PAL_F2].sp, ft[PAL_F2].tp, ft[PAL_F2].en)==fsync[j])
                  k++;
            }

            if(k==4)  /* file syncs are present, check block sync sequence... */
            {
               sod= i+32;   /* sod points at 1st byte of first blocks sync. */
               tmp= sod;
               blocks=0;

               do
               {
                  for(j=0,k=0; j<4; j++)  /* check block sync sequence... */
                  {
                     if(readttbyte(tmp+(j*8), ft[PAL_F2].lp, ft[PAL_F2].sp, ft[PAL_F2].tp, ft[PAL_F2].en)==bsync[j])
                        k++;
                  }
                  if(k==4)    /* block syncs are present... */
                  {
                     tmp+=(262*8);  /* each block is 262 bytes long. */
                     blocks++;
                  }
               }
               while(k==4);   /* while there was a block last time. */

               tmp-=8;   /* tmp should now point at last blocks checkbyte. */
               eod=tmp;
               eof=eod+7;

               /* When we're sure this is a Palace F2 block, try to find the load orchestrator counterpart in a CBM DATA block */
               if (fa == -1)
               {
                  find_and_copy_palace_loader(&ib, &buf, &bufsz);
                  fa=0; /* Only search and copy the orchestrator once */
               }

               /* If we were able to find the load orchestrator CBM DATA block, scan it for block information */
               if (ib != -1)
               {
                  int subblocks = 0;

                  get_palace_block_info(buf, bufsz, 0, b++, &s, &subblocks);

                  /* Check if we were able to extract the relevant information for this block */
                  if (subblocks && subblocks == blocks)
                  {
                     addblockdef(PAL_F2, sof,sod,eod,eof, blocks | (s << 8));
                  }
                  else
                  {
                     addblockdef(PAL_F2, sof,sod,eod,eof, blocks);
#ifdef PAL_F2_DEBUG
                     if (subblocks && subblocks != blocks)
                        printf("\nSubblock count mismatch, read: %d, decoded from data: %d", subblocks, blocks);
#endif
                  }
               }
               /* Fall back to the legacy behaviour */
               else
               {
                  addblockdef(PAL_F2, sof,sod,eod,eof, blocks);
               }

               i=eof;  /* optimize search */
            }
         }
      }
      else
      {
         if(z<0)    /* find_pilot() failed (too few/many), set i to failure point. */
            i=(-z);
      }
   }

   if (ib != -1)
      free (buf);
}
/*---------------------------------------------------------------------------
*/
int palacef2_describe(int row)
{
   int i,j,s,b,cb,goodchecks,ddi,total_blocks;

   total_blocks= blk[row]->xi & 255;
   blk[row]->cx= 256*total_blocks;

   /* If we were able to extract block information from the orchestrator, use it here */
   if (blk[row]->xi >> 8)
   {
      blk[row]->cs = (blk[row]->xi >> 8);
      blk[row]->ce = blk[row]->cs + blk[row]->cx - 1;
   }

   if(blk[row]->dd!=NULL)
      free(blk[row]->dd);
   blk[row]->dd= (unsigned char*)malloc(blk[row]->cx);

   sprintf(lin,"\n - Total Blocks : %d",total_blocks);
   strcat(info,lin);

   s= blk[row]->p2 +(5*8);   /* note : skips 1st block header. */

   /* test checkbyte for each block + extract data... */
   goodchecks=0;
   ddi=0;
   for(i=0; i<total_blocks; i++)
   {
      cb=0;
      for(j=0; j<256; j++)
      {
         b= readttbyte(s+(i*262*8)+(j*8), ft[PAL_F2].lp, ft[PAL_F2].sp, ft[PAL_F2].tp, ft[PAL_F2].en);
         blk[row]->dd[ddi++]=b;
         if(b==-1)
            blk[row]->rd_err++;
         cb^=b;
      }
      b= readttbyte(s+(i*262*8)+(j*8), ft[PAL_F2].lp, ft[PAL_F2].sp, ft[PAL_F2].tp, ft[PAL_F2].en);  /* read checkbyte. */
      if(cb==b)
         goodchecks++;
   }
   sprintf(lin,"\n - Good Checkbytes : %d of %d",goodchecks,total_blocks);
   strcat(info,lin);

   blk[row]->cs_exp= total_blocks;   /* fake the overall checkbyte as a */
   blk[row]->cs_act= goodchecks;     /* count of good checkbytes. */
   
   /* get pilot & trailer length.. */
   blk[row]->pilot_len= ((blk[row]->p2- blk[row]->p1)>>3)-4;
   blk[row]->trail_len=0;

   return 0;
}
