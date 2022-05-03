/*
 * mm_ver1.6.c - model for segregatedImproved Utilization(little)
 * 
 * 分组（实际上只改变find_fit&add2list搜索起点）
 * version based on ver1.5, using TWO segregated list, (size-ranking)best fit.
 * 
 * To Modify:
 * add to list()
 * 
 *
 * my explicit-empty-list design as follows:
           
     +----------+----------+           +----------+----------+          +----------+----------+
memo:|   NULL   |0xf9610000|  .......  |   root   |0xf9610f00| .......  |0xf9610000|   NULL   |
     +----------+----------+           +----------+----------+          +----------+----------+  
addr:    root     root+0x4              0xf9610000 0xf9610004            0xf9610f00 0xf9610f04
expl: <constant/start point>           <LastIn & FisrtOut Blk>          <FirstIn Blk & end tag>
 
 * 45+13=58 points 
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
    "ver1.6",
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

#define GET(p)     (*(unsigned int *)(p)) //warning
#define PUT(p,val) (*(unsigned int *)(p)=(val))

#define GET_SIZE(p) (GET(p) & ~0x7) //单位byte，即char*
#define GET_ALLOC(p) (GET(p) & 0X1)
//Given Block Pointer bp
#define HDRP(bp) ((char*)(bp) - WSIZE)
#define FTRP(bp) ((char*)(bp)+GET_SIZE(HDRP(bp))-DSIZE) 
#define NEXT_BLKP(bp) ((char*)(bp)+GET_SIZE((char*)(bp) - WSIZE))
#define PREV_BLKP(bp) ((char*)(bp)-GET_SIZE((char*)(bp) - DSIZE))

#define SUCC_BLKP(bp) ((char*)(bp)+WSIZE)  //dereference 
#define PRED_BLKP(bp) ((char*)(bp))

/*********************************************************
 * END of CONST&MACRO to DO LINKED LIST ****
 ********************************************************/

static void* extend_heap(size_t words);
static void* coalesce(void* bp);
static void  remove_free_block(void* bp);
static void* find_fit(size_t size);
static void  place(void* bp, size_t size);
static void  divide(void* bp, size_t size, size_t avail_size);
/* LIFO maintainence */
static void  add_to_empty_list(void* newbp);
static void  delete_from_empty_list(void* alloc_bp);
/* heap consistency */
static void  mm_checker();
static void  mm_error(char* s);
static void  pred_to_root(void* bp);

void* heap_listp = 0;
void* root       = 0; //leader of LIFO
void* root1024   = 0;
void* root16384  = 0;

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    
    if((heap_listp=mem_sbrk(10*WSIZE))==(void*)-1){
        return -1;
    }

    PUT(heap_listp,0);
    PUT(heap_listp+(1*WSIZE),NULL); //root(0)
    PUT(heap_listp+(2*WSIZE),NULL); 
    PUT(heap_listp+(3*WSIZE),NULL); //root1024
    PUT(heap_listp+(4*WSIZE),NULL);
    PUT(heap_listp+(5*WSIZE),NULL); //root16384
    PUT(heap_listp+(6*WSIZE),NULL);
    PUT(heap_listp+(7*WSIZE),PACK(DSIZE,1));
    PUT(heap_listp+(8*WSIZE),PACK(DSIZE,1));
    PUT(heap_listp+(9*WSIZE),PACK(0,1));
    /* global constant */
    root     =heap_listp+(1*WSIZE); 
    root1024 =heap_listp+(3*WSIZE); 
    root16384=heap_listp+(5*WSIZE);   
    /* link the segregated */
    /*PUT(SUCC_BLKP(root),root1024);
    PUT(PRED_BLKP(root1024),root);
    PUT(SUCC_BLKP(root1024),root16384);
    PUT(PRED_BLKP(root16384),root1024); */      

    heap_listp+=(8*WSIZE);//序言块起点
    

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
   
    if(size<=0){
        mm_checker();
        return NULL;
    }
    
    asize = ALIGN(size + SIZE_T_SIZE);
    if((bp=find_fit(asize))!=NULL) {
        place(bp, asize);
        mm_checker();
        return bp;
    }
    /* No fit found */
    extendsize=MAX(asize,CHUNKSIZE); 
    if((bp=extend_heap(extendsize/WSIZE))==NULL)     //需要find_fit()失败后连接
        return NULL;
    place(bp,asize);
    mm_checker();
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
    add_to_empty_list(bp);

    coalesce(bp);
    mm_checker();
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
        memcpy(newbp, bp, (cur_size<size?cur_size:size));  
        mm_free(bp); //必须先malloc再free，否则原来blk中content可能会被footer破坏        
        
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

    /* add to empty list */
    add_to_empty_list(bp);

    return coalesce(bp);
}

/*
 * coalesce - Coalescing the prev or next block of ptr bp, return bptr of coalesced blk.
 */
static void* coalesce(void* bp){
    size_t  prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));  //0|1
    size_t  next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));


    /*coalesce the block and change the point*/
    if(prev_alloc && next_alloc){
        return bp;		//case1
    }
    else if(prev_alloc && !next_alloc)  //case2后空
    {
        delete_from_empty_list(bp);  //necessary, cuz bp happen to be unchanged.
        delete_from_empty_list(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size,0));
        PUT(FTRP(bp), PACK(size,0));
        add_to_empty_list(bp);
    }
    else if(!prev_alloc && next_alloc)	//case 3前空
    {
        delete_from_empty_list(bp);
        delete_from_empty_list(PREV_BLKP(bp));

        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp),PACK(size,0));
        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
        bp = PREV_BLKP(bp);

        add_to_empty_list(bp);
    }
    else	//case 4前后空
    {
        delete_from_empty_list(bp);
        delete_from_empty_list(NEXT_BLKP(bp));
        delete_from_empty_list(PREV_BLKP(bp));

        size += GET_SIZE(FTRP(NEXT_BLKP(bp))) + GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(NEXT_BLKP(bp)),PACK(size,0));
        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
        bp = PREV_BLKP(bp);

        add_to_empty_list(bp);
    }
    
    return bp;
}

/*
 * remove_free_block - Removing the freed blk from free-blk-list.
 */
static void remove_free_block(void* bp){

}

/*
 * find_fit - find first-fit blk from empty list.
 */
static void* find_fit(size_t size){                           //改了     (非常丑陋)                
    void *bp;
    if(size<1024){ //define start pos        
        for(bp = GET(SUCC_BLKP(root)); bp!=NULL; bp = GET(SUCC_BLKP(bp))){ 
            if(size <= GET_SIZE(HDRP(bp))){
                return bp;
            }
        }
    }
    if(size<16384){
        for(bp = GET(SUCC_BLKP(root1024)); bp!=NULL; bp = GET(SUCC_BLKP(bp))){ 
            if(size <= GET_SIZE(HDRP(bp))){
                return bp;
            }
        }
    }
    for(bp = GET(SUCC_BLKP(root16384)); bp!=NULL; bp = GET(SUCC_BLKP(bp))){ 
        if(size <= GET_SIZE(HDRP(bp))){
            return bp;
        }
    }

/*
    for(; bp!=NULL; bp = GET(SUCC_BLKP(bp))){ 
        if(size <= GET_SIZE(HDRP(bp))){
            return bp;
        }
    }*/
    return NULL;    
}


/*
 * place - put size into free blk(malloked).
 */
static void  place(void* bp, size_t size){                                           //不用改
    size_t avail_size;
    avail_size=GET_SIZE(HDRP(bp));
    if((size+16)<=avail_size){       //one free -> one busy + one free
        divide(bp,size,avail_size);
    }else{
        PUT(HDRP(bp), PACK(avail_size,1));
        PUT(FTRP(bp), PACK(avail_size,1));
        delete_from_empty_list(bp);
    }
}

/*
 * divide - make utilized of the free blk to be placed.  AND IT SHOULD MAY BE INLINED
 */
static void divide(void* bp, size_t size, size_t avail_size) {                                           //不用改
    PUT(HDRP(bp), PACK(size,1));
    PUT(FTRP(bp), PACK(size,1));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(avail_size-size,0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(avail_size-size,0));
    /* change */ 
    delete_from_empty_list(bp);
    add_to_empty_list(NEXT_BLKP(bp));
}

/*
 * add_to_empty_list - call the func when new/modified freed blk appeared.(blk2list)
 * List is maintained by global variant "root",  at the beginning of memory, 
 * also at the top of LIFO list.
 *
 * called by extend_heap()/free()/coalesce().   not called by divide cuz one-of-two-pieces get malloc immediately.
 */
static void  add_to_empty_list(void* newbp){  //new name more readable                                        //改了
    void* frontbp;                                     
    if(GET_SIZE(HDRP(newbp))<1024){ //define start pos
        frontbp=root;   
    }else if(GET_SIZE(HDRP(newbp))<16384){
        frontbp=root1024;   
    }else{
        frontbp=root16384;   
    }   

    void* backbp=GET(SUCC_BLKP(frontbp));
    while(backbp!=NULL&&GET_SIZE(HDRP(backbp))<GET_SIZE(HDRP(newbp))){ //size递增
        frontbp=backbp;
        backbp=GET(SUCC_BLKP(frontbp));
    }

    //判断结束while的原因
    if(backbp!=NULL){ //插在backbp前，size比backbp小     root(....somebp...frontbp) newbp backbp....
        PUT(PRED_BLKP(newbp),frontbp);   
        PUT(SUCC_BLKP(newbp), backbp);  
        PUT(SUCC_BLKP(frontbp),newbp);
        PUT(PRED_BLKP(backbp) ,newbp);    
    }else{  //newbp是最大的                              root(....somebp...frontbp) newbp....
        PUT(PRED_BLKP(newbp),frontbp);
        PUT(SUCC_BLKP(frontbp),newbp);
        PUT(SUCC_BLKP(newbp),NULL);//IN USE OF FIND_FIT() BOUND & delete, end of list.        
    }
}

/*
 * delete_from_empty_list - call the func when empty blk get occupied.
 * called by malloc()/free()
 * (coalesce()/place()/realloc() is called inside the above)
 */
static void  delete_from_empty_list(void* alloc_bp){                                                                         //不用改
    if((void*)GET(SUCC_BLKP(alloc_bp))==NULL){ //alloc_bp is end.
        PUT(SUCC_BLKP(GET(PRED_BLKP(alloc_bp))),NULL); 
    }else{    
        PUT(PRED_BLKP(GET(SUCC_BLKP(alloc_bp))),GET(PRED_BLKP(alloc_bp))); 
        PUT(SUCC_BLKP(GET(PRED_BLKP(alloc_bp))),GET(SUCC_BLKP(alloc_bp)));
    }
}

/*
 * mm_checker - check heap consistency and find out where is troublemaker.
 * remember to ban it for thru scores
 * use printf at short.rep
 */
static void  mm_checker(){
    //free_check and coalesce_check correctness
    printf("---------heap---------\n");
    void* bp = heap_listp;
    while(GET_SIZE(HDRP(bp))>0){
        printf("%p,%p\n",bp,HDRP(bp));
        bp = NEXT_BLKP(bp);
    }
    return;
    printf("---------empty--------\n");
    void* bp_LIFO=GET(SUCC_BLKP(root));
    while(bp_LIFO!=NULL){        
        printf("%p,%p\n",bp_LIFO,HDRP(bp_LIFO)); 
        /* 1.Is every block in the free list marked as free? */
        if(GET_ALLOC(HDRP(bp_LIFO))!=0&&GET_ALLOC(FTRP(bp_LIFO))!=0){ 
            mm_error("Not Freed");
            exit(1);
        }

        /* 2.Are there any contiguous free blocks that somehow escaped coalescing? */
        if(GET_ALLOC(HDRP(PREV_BLKP(bp_LIFO)))==0||GET_ALLOC(HDRP(NEXT_BLKP(bp_LIFO)))==0){
            mm_error("Not Coalesced");
            exit(1);
        }
        bp_LIFO=GET(SUCC_BLKP(bp_LIFO)); 
    }
    printf("---------empty--------\n\n");
    return;


    //void* bp = heap_listp;
    while(GET_SIZE(HDRP(bp))>0){
        size_t size;
        /* 3.Is every free block actually in the free list? */
        if(GET_ALLOC(HDRP(bp))==0){
            pred_to_root(bp);
        }

        /* 5.Do any allocated blocks overlap? */
        else if(GET_ALLOC(HDRP(bp))==1&&(size=GET_SIZE(HDRP(bp)))!=0){            
            unsigned int* ptr=GET(root);
            do{
                if(ptr>=HDRP(bp)&&ptr<=FTRP(bp)) mm_error("blk overlap");
                ptr=GET(SUCC_BLKP(bp));
            } while(ptr!=NULL); //look_through_empty_list(bp);            
        }
        
        else{
            mm_error("unkonwn");
            exit(1);
        }
        bp = NEXT_BLKP(bp);
    }

    return ;
    /* comment on 5.
     * intresting implementation, check if
     * every free blk in List not overlap with allocated blk
     */    
}

static void  mm_error(char* s){
    printf("**\nheap consistency check failed due to %s.\n",s);
}

static void  pred_to_root(void* bp){
    void* bp_LIFO=GET(root);
    do{
        if(bp_LIFO==bp) return;
    } while(GET(SUCC_BLKP(bp_LIFO))!=NULL);
    mm_error("some free blks not in list");
    exit(1);
}
/*********************************************************
 * End of Assitant Functions
 ********************************************************/
