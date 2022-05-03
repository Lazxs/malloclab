/*
 * mm_ver0.c - The easiest for starter.
 * 
 * It's a simple version based on textbook, using implicit list/first fit, 
 * implementing realloc() with malloc() and free().
 *
 * running on x64 available
 * 45+9=54points
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ver0",
    /* First member's full name */
    "Lazxs",
    /* First member's email address */
    "@github",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t))) //sizeof(size_t) is 8 in this machine, including footer and header

/*********************************************************
 * CONST&MACRO TO DO LINKED LIST
 ********************************************************/

#define WSIZE      4
#define DSIZE      8
#define CHUNKSIZE (1<<12) //4KB CHUNKSIZE of Virtual Memory

#define MAX(x,y) ((x)>(y)? (x):(y))

#define PACK(size,alloc) ((size) | (alloc))

#define GET(p) (*(unsigned int *)(p))
#define PUT(p,val) (*(unsigned int *)(p)=(val))

#define GET_SIZE(p) (GET(p) & ~0x7) //单位byte，即char*
#define GET_ALLOC(p) (GET(p) & 0X1)
//Given Block Pointer bp
#define HDRP(bp) ((char*)(bp) - WSIZE)
#define FTRP(bp) ((char*)(bp)+GET_SIZE(HDRP(bp))-DSIZE) //必须有头才能有尾，可能是一个漏洞
#define NEXT_BLKP(bp) ((char*)(bp)+GET_SIZE((char*)(bp) - WSIZE))
#define PREV_BLKP(bp) ((char*)(bp)-GET_SIZE((char*)(bp) - DSIZE))

/*********************************************************
 * END of CONST&MACRO to DO LINKED LIST ****
 ********************************************************/

static void* extend_heap(size_t words);
static void* coalesce(void* bp);
static void  remove_free_block(void* bp);
static void* find_fit(size_t size);
static void  place(void* bp, size_t size);
static void  divide(void* bp, size_t size, size_t avail_size);

void* heap_listp=0;


/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    
    if((heap_listp=mem_sbrk(4*WSIZE))==(void*)-1){
        return -1;
    }

    PUT(heap_listp,0);
    PUT(heap_listp+(1*WSIZE),PACK(DSIZE,1));
    PUT(heap_listp+(2*WSIZE),PACK(DSIZE,1));
    PUT(heap_listp+(3*WSIZE),PACK(0,1));
    heap_listp+=(2*WSIZE);

    if(extend_heap(CHUNKSIZE/WSIZE)==NULL)
        return -1;
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment(at least 4 words).
 */
void *mm_malloc(size_t size)
{
    size_t asize; /* Adjusted block size */
    size_t extendsize;  /* Amount to extend heap if no fit */
    char* bp;
   
    if(size<=0)
        return NULL;
    
    asize = ALIGN(size + SIZE_T_SIZE);
    if((bp=find_fit(asize))!=NULL) {
        place(bp, asize);
        return bp;
    }
    /* Not fit found */
    extendsize=MAX(asize,CHUNKSIZE); //CHUNKSIZE是单位吗
    if((bp=extend_heap(extendsize/WSIZE))==NULL)
        return NULL;
    place(bp,asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    if(bp==0) return;

    size_t size=GET_SIZE(HDRP(bp));

    PUT(HDRP(bp),PACK(size,0));
    PUT(FTRP(bp),PACK(size,0));

    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size)
{
    if(bp==NULL) return mm_malloc(size);
    if(size==0){
        mm_free(bp);
        return NULL;
    }

    size_t cur_size=GET_SIZE(HDRP(bp));
    size_t asize = ALIGN(size + SIZE_T_SIZE);
    if(asize==cur_size){
        return bp;
    }else{       
        
        void* newbp = mm_malloc(size); 
        mm_free(bp); //必须先malloc再free，否则原来blk中content可能会被footer破坏
        memcpy(newbp, bp, (cur_size<size?cur_size:size));  
        
        return newbp;            
    }
}

/*********************************************************
 * Assitant Functions
 ********************************************************/
/*
 * extend_heap - initial heap or expand heap area, return header of new area
 */
static void* extend_heap(size_t words){
     char* bp;
     size_t size;

     size=(words%2)?(words+1)*WSIZE:words*WSIZE;
     if((long)(bp=mem_sbrk(size))==-1)
        return NULL;
    
    PUT(HDRP(bp),PACK(size,0));          //free block header
    PUT(FTRP(bp),PACK(size,0));          //free block footer
    PUT(HDRP(NEXT_BLKP(bp)),PACK(0,1));  //next block header

    return coalesce(bp);
}

/*
 * coalesce - Coalescing the prev or next block of ptr bp, return bptr of coalesced blk.
 */
static void* coalesce(void* bp){
    size_t  prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));  //0|1
    size_t  next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t  size = GET_SIZE(HDRP(bp));


    /*coalesce the block and change the point*/
    if(prev_alloc && next_alloc){
        return bp;		//case1
    }
    else if(prev_alloc && !next_alloc)  //case2
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size,0));
        PUT(FTRP(bp), PACK(size,0));
    }
    else if(!prev_alloc && next_alloc)	//case 3
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp),PACK(size,0));
        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
        bp = PREV_BLKP(bp);
    }
    else	//case 4
    {
        size += GET_SIZE(FTRP(NEXT_BLKP(bp))) + GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(NEXT_BLKP(bp)),PACK(size,0));
        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

/*
 * remove_free_block - Removing the freed blk from free-blk-list.
 */
static void remove_free_block(void* bp){

}

/*
 * find_fit - find first-fit blk from free-blk-list.
 */
static void* find_fit(size_t size){
    void *bp;
    for(bp = heap_listp; GET_SIZE(HDRP(bp))>0; bp = NEXT_BLKP(bp)){
        if(!GET_ALLOC(HDRP(bp)) && (size <= GET_SIZE(HDRP(bp)))){
            return bp;
        }
    }
    return NULL;
}

/*
 * place - put size into free blk(malloked).
 */
static void  place(void* bp, size_t size){
    size_t avail_size;
    avail_size=GET_SIZE(HDRP(bp));
    if((size+16)<=avail_size){
        divide(bp,size,avail_size);
    }else{
        PUT(HDRP(bp), PACK(avail_size,1));
        PUT(FTRP(bp), PACK(avail_size,1));
    }
}

/*
 * divide - make utilized of the free blk to be placed.  AND IT SHOULD MAY BE INLINED
 */
static void divide(void* bp, size_t size, size_t avail_size) {
    PUT(HDRP(bp), PACK(size,1));
    PUT(FTRP(bp), PACK(size,1));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(avail_size-size,0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(avail_size-size,0));
}
/*********************************************************
 * End of Assitant Functions
 ********************************************************/













