/*

mm.c -
This is our memory allocator.  It contains the following features:

  •Allocated Blocks contain header,footer, and payload
  •Explicit Free List for free blocks
    -Minimum block size is 16 bytes (header,prev,next,footer)
    -prev and next pointers stored in free block payload area
    -new free blocks are inserted at beginning of explicit free list
  •Placement Policty


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
  "TEAM --->>> (Abraham McIlvaine and Benjamin Steenkamer)",
  /* First member's full name */
  "Abraham McIlvaine",
  /* First member's email address */
  "abemac@udel.edu",
  /* Second member's full name (leave blank if none) */
  "Benjamin Steenkamer",
  /* Second member's email address (leave blank if none) */
  "bsteen@udel.edu"
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
#define WSIZE 4
#define DSIZE 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define MIN_BLOCK_SIZE 16
#define ONLY_SMALL_BLK_SIZE 1500 //
#define BEST_FIT_THRESHOLD 25
#define MIN_CHUNK (1<<9)
#define MAX_CHUNK (1<<30)
#define DEFAULT_CHUNK (1<<11)
#define CHUNK_UPDATE_AMT 1024
#define PADDING 512
#define MAX(x,y) ((x) > (y)? (x) : (y))
#define PACK(size,alloc) ((size) | (alloc))
#define GET(p) (*(unsigned int *)(p))
#define PUT(p,val) (*(unsigned int *)(p) = (val))
#define ONLY_SMALL 0x2
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)


#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define PREV(bp) ((char *) (bp))
#define NEXT(bp) ((char *) (bp)+WSIZE)

#define DEBUGx
static int CHUNK_SIZE = DEFAULT_CHUNK; //512KB
static void * free_list_head=NULL;
static void * only_small_blk=NULL;
static unsigned long long free_list_size=0;
static char * heap_listp=NULL;
static void * extend_heap(size_t words);
static void * coalesce(void * bp);
static void * find_fit(size_t asize);
static void place(void* bp, size_t asize);
static void del_free_list_node(void* bp);
static void ins_free_list_node(void *bp);
static void copy(const int* b1,const int* b2);
static void createFreeBlock(const void * bp,size_t asize);
static void reserveOnlySmallBlock();
static void createAllocBlock(const void * bp,size_t asize);
static void createAllocBlockWithData(const void * bp,size_t size,const void * data);
static void printfreelist();
// /*
// * mm_init - initialize the malloc package.
// */
static void printblock(void *bp)
{
    size_t hsize, halloc, fsize, falloc;

    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));

    if (hsize == 0) {
	     printf("%p: EOL\n", bp);
	      return;
    }

     printf("%p: header: [%i:%c] footer: [%i:%c]\n", bp,
	hsize, (halloc ? 'a' : 'f'),
	fsize, (falloc ? 'a' : 'f'));
}
static void  printheap(){
  void * bp;
  for(bp=heap_listp;GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
    printblock(bp);
  }
  printf("\t\t\t\t\t\t\t");
  printfreelist();
}

static void printfreelist(){
  void* bp;
  printf("Free List [");
  for(bp=free_list_head;bp!=NULL; bp = GET(NEXT(bp))){
      printf("%p : %i, ",bp, GET_SIZE(HDRP(bp)));

  }
  printf("\b\b]\n");

}

int mm_init(void)
{
  free_list_head=NULL;
  heap_listp=NULL;
  if((heap_listp = mem_sbrk(4*WSIZE)) == (void *) -1){
    return -1;
  }
  CHUNK_SIZE =DEFAULT_CHUNK;
  PUT(heap_listp,0);
  free_list_size=0;
  PUT(heap_listp + (1*WSIZE), PACK(DSIZE,3));
  PUT(heap_listp + (2*WSIZE), PACK(DSIZE,1));
  PUT(heap_listp + (3*WSIZE), PACK(0,1));
  heap_listp += (2*WSIZE);
  if((extend_heap(CHUNK_SIZE/WSIZE)) == NULL){
    return -1;
  }
  reserveOnlySmallBlock();
  #ifdef DEBUG
    printf("\nHeap initialized\n");
    printheap();
  #endif
  return 0;
}

static void * extend_heap(size_t words){
  char * bp;
  size_t size;

  size = (words % 2) ? (words+1) * WSIZE: words*WSIZE;
  if(size < MIN_BLOCK_SIZE){
    size=MIN_BLOCK_SIZE;
  }
  if((long)(bp = mem_sbrk(size))== -1){
    return NULL;
  }
  createFreeBlock(bp,size);
  PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1));
  return coalesce(bp);

}




static void * coalesce(void * bp){
  size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  size_t size= GET_SIZE(HDRP(bp));

  if (prev_alloc && next_alloc) {/* Case 1 */
    return bp;
  }

  else if (prev_alloc && !next_alloc) {/* Case 2 */
    del_free_list_node(NEXT_BLKP(bp));
    size+= GET_SIZE(HDRP(NEXT_BLKP(bp)));
    PUT(HDRP(bp), PACK(size,0));
    PUT(FTRP(bp), PACK(size,0));
  }
  else if (!prev_alloc && next_alloc) { /* Case 3 */
    del_free_list_node(PREV_BLKP(bp));
    int prev2_alloc =(GET(HDRP(PREV_BLKP(bp))))&2;
    PUT(PREV(PREV_BLKP(bp)),GET(PREV(bp)));
    PUT(NEXT(PREV_BLKP(bp)),GET(NEXT(bp)));
    void * next = GET(NEXT(bp));
    if(next!=NULL)
      PUT(PREV(next),PREV_BLKP(bp));
    size+= GET_SIZE(HDRP(PREV_BLKP(bp)));
    PUT(FTRP(bp), PACK(size,0));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
    bp = PREV_BLKP(bp);
    if(prev2_alloc){

    }
    free_list_head = bp;

  }
  else {/* Case 4 */
    size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
    del_free_list_node(PREV_BLKP(bp));
    del_free_list_node(NEXT_BLKP(bp));
    PUT(PREV(PREV_BLKP(bp)),GET(PREV(bp)));
    PUT(NEXT(PREV_BLKP(bp)),GET(NEXT(bp)));
    if(NEXT(bp)!=NULL && GET(NEXT(bp))!=NULL)
      PUT(PREV(GET(NEXT(bp))),PREV_BLKP(bp));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0));
    bp = PREV_BLKP(bp);
    free_list_head = bp;

  }
  return bp;
}
static void del_free_list_node(void* bp){
  void * prev = GET(PREV(bp));
  void * next = GET(NEXT(bp));
  if(bp == free_list_head){
    free_list_head = next;
  }
  if(prev!=NULL){
    PUT(NEXT(prev),next);
  }
  if(next!=NULL){
    PUT(PREV(next),prev);
  }
 --free_list_size;
}

static void ins_free_list_node(void *bp){
  if(free_list_head!=NULL){
    PUT(PREV(free_list_head),bp);
  }
  PUT(NEXT(bp),free_list_head);
  PUT(PREV(bp),NULL);
  free_list_head=bp;
  ++free_list_size;
}

static void createFreeBlock(const void * bp,size_t size){
  PUT(HDRP(bp),PACK(size,0));
  PUT(FTRP(bp),PACK(size,0));
  ins_free_list_node(bp);


}
static void reserveOnlySmallBlock(){
  void* bp = mm_malloc(ONLY_SMALL_BLK_SIZE);
  PUT(HDRP(bp),PACK(GET_SIZE(HDRP(bp)),1) );
  PUT(FTRP(bp),PACK(GET_SIZE(HDRP(bp)),1) );
  only_small_blk=bp;
}

static void createAllocBlock(const void * bp,size_t size){
  PUT(HDRP(bp),PACK(size,1));
  PUT(FTRP(bp),PACK(size,1));
  del_free_list_node(bp);

}
static void createAllocBlockWithData(const void * bp,size_t size,const void * data){
  del_free_list_node(bp);
  PUT(HDRP(bp),PACK(size,1));
  copy(data,bp);
  PUT(FTRP(bp),PACK(size,1));
}
/*
* mm_malloc - Allocate a block by incrementing the brk pointer.
*     Always allocate a block whose size is a multiple of the alignment.
*/
void *mm_malloc(size_t size)
{
  #ifdef DEBUG
    printf("malloc %i\n",size);
    printheap();
  #endif
  size_t asize;
  size_t extendsize;
  char * bp;
  if(size==0){
    return NULL;
  }

  asize = ALIGN(size) + 8;
  if(asize < MIN_BLOCK_SIZE){
    asize = MIN_BLOCK_SIZE;
  }
  if(asize < 100){//special spot for small items
    //printf("%i\n",asize);
    int csize = GET_SIZE(HDRP(only_small_blk));
    if(asize < csize && (csize - asize) >= MIN_BLOCK_SIZE){
      void * ret_val = only_small_blk;
      PUT(HDRP(only_small_blk),PACK(asize,1));
      PUT(FTRP(only_small_blk),PACK(asize,1));
      only_small_blk=NEXT_BLKP(only_small_blk);
      PUT(HDRP(only_small_blk),PACK(csize-asize,1));
      PUT(FTRP(only_small_blk),PACK(csize-asize,1));
      return ret_val;
      //allocated so doesn't get messed with
    }else if(asize <=csize){
      void * ret_val = only_small_blk;
      PUT(HDRP(only_small_blk),PACK(csize,1));
      PUT(FTRP(only_small_blk),PACK(csize,1));
      reserveOnlySmallBlock();
      return ret_val;
    }else if(asize > csize){
      // printf("here");
      // mm_free(only_small_blk);
      // reserveOnlySmallBlock();
      // void * ret_val = only_small_blk;
      // PUT(HDRP(only_small_blk),PACK(asize,1));
      // PUT(FTRP(only_small_blk),PACK(asize,1));
      // only_small_blk=NEXT_BLKP(only_small_blk);
      // PUT(HDRP(only_small_blk),PACK(csize-asize,1));
      // PUT(FTRP(only_small_blk),PACK(csize-asize,1));
      // return ret_val;
    }
  }
  if((bp= find_fit(asize)) != NULL){
    place(bp,asize);
    return bp;
  }

  extendsize = MAX(asize,CHUNK_SIZE);
  if(asize<(CHUNK_SIZE+PADDING)){
    CHUNK_SIZE+=CHUNK_UPDATE_AMT;
  }else if ((asize-PADDING) > CHUNK_SIZE){
    CHUNK_SIZE-=CHUNK_UPDATE_AMT;
  }
  if(CHUNK_SIZE > MAX_CHUNK){
    CHUNK_SIZE=MAX_CHUNK;
  }else if(CHUNK_SIZE < MIN_CHUNK){
    CHUNK_SIZE=MIN_CHUNK;
  }
  if((bp=extend_heap(extendsize/WSIZE)) == NULL){
    return NULL;
  }

  place(bp,asize);
  return bp;

}

static void * find_fit(size_t asize){
  if(free_list_size < BEST_FIT_THRESHOLD){
    void* bp;
    void * ret_loc = NULL;
    unsigned int cur_size=-1;
    unsigned int tmp_size;
    for(bp=free_list_head;bp!=NULL; bp = GET(NEXT(bp))){
      tmp_size= GET_SIZE(HDRP(bp));
      if(asize <= tmp_size){
        if(tmp_size < cur_size){
          cur_size=tmp_size;
          ret_loc = bp;
        }

      }
    }
    return ret_loc;
  }
  else{
    void* bp;

    for(bp=free_list_head;bp!=NULL; bp = GET(NEXT(bp))){
      if(asize <= GET_SIZE(HDRP(bp))){
        return bp;
      }
    }
    return NULL;
  }

}
static void place(void* bp, size_t asize){
  size_t csize = GET_SIZE(HDRP(bp));
  if((csize - asize) >= MIN_BLOCK_SIZE){
    createAllocBlock(bp,asize);
    bp=NEXT_BLKP(bp);
    createFreeBlock(bp,csize-asize);

  }else{
    createAllocBlock(bp,csize);
  }
  #ifdef DEBUG
  printf("Placed %i\n",asize);
  printheap();
  #endif

}
static void place2(void* bp, size_t asize){
  size_t csize = GET_SIZE(HDRP(bp));
  if((csize - asize) >= MIN_BLOCK_SIZE){
    PUT(HDRP(bp),PACK(asize,1));
    PUT(FTRP(bp),PACK(asize,1));
    bp=NEXT_BLKP(bp);
    createFreeBlock(bp,csize-asize);

  }else{
    PUT(HDRP(bp),PACK(csize,1));
    PUT(FTRP(bp),PACK(csize,1));
  }
  #ifdef DEBUG
  printf("Placed %i\n",asize);
  printheap();
  #endif

}
/*
* mm_free - Freeing a block does nothing.
*/
void mm_free(void *ptr)
{
  size_t size = GET_SIZE(HDRP(ptr));
  #ifdef DEBUG
  printf("freeing %i\n",size);
  printheap();
  #endif
  createFreeBlock(ptr,size);
  coalesce(ptr);
  #ifdef DEBUG
  printf("freed %i\n",size);
  printheap();
  #endif

}

/*
* mm_realloc - Implemented simply in terms of mm_malloc and mm_free
*/
void *mm_realloc(void *ptr, size_t size)
{
  #ifdef DEBUG
    printf("re-malloc %i\n",size);
    printheap();
  #endif
  if(ptr==NULL){
    #ifdef DEBUG
      printf("re-alloacted %i\n",size);
      printheap();
    #endif
    return mm_malloc(size);
  }
  if(size==0){
    mm_free(ptr);
    return NULL;
  }
  size_t asize;
  if(size < MIN_BLOCK_SIZE){
    asize = MIN_BLOCK_SIZE;
  }else{
    asize = ALIGN(size) +8;
  }

  size_t cur_size = GET_SIZE(HDRP(ptr));

  if(asize < cur_size){
    place2(ptr,asize);
    #ifdef DEBUG
      printf("re-alloacted %i\n",size);
      printheap();
    #endif
    return ptr;
  }
  else if(!GET_ALLOC(HDRP(NEXT_BLKP(ptr)))){//next block is free
    size_t next_blk_size = GET_SIZE(HDRP(NEXT_BLKP(ptr)));




    int extra_space = asize - cur_size;
    if( next_blk_size>=extra_space ){//block is large enough
      if((next_blk_size-extra_space) >= MIN_BLOCK_SIZE ){
        del_free_list_node(NEXT_BLKP(ptr));
        PUT(HDRP(ptr),PACK(asize,1));
        PUT(FTRP(ptr),PACK(asize,1));
        void * freeptr= NEXT_BLKP(ptr);
        createFreeBlock(freeptr,next_blk_size-extra_space);
        #ifdef DEBUG
          printf("re-alloacted %i\n",size);
          printheap();
        #endif
        return ptr;
      }
      else if(next_blk_size == (asize - cur_size)){//block is just large enough
        del_free_list_node(NEXT_BLKP(ptr));
        PUT(HDRP(ptr),PACK(asize,1));
        PUT(FTRP(ptr),PACK(asize,1));
        #ifdef DEBUG
          printf("re-alloacted %i\n",size);
          printheap();
        #endif
        return ptr;
      }
     }

  }
  else if(!GET_ALLOC(FTRP(PREV_BLKP(ptr)))){//prev block is free
    size_t prev_blk_size = GET_SIZE(HDRP(PREV_BLKP(ptr)));
    void * prev_blk = PREV_BLKP(ptr);
    int total_size = cur_size + prev_blk_size;
    if( total_size >= asize ){//block is large enough
      if((total_size-asize) >= MIN_BLOCK_SIZE ){
        createAllocBlockWithData(prev_blk,asize,ptr);
        void * freeptr= NEXT_BLKP(prev_blk);
        createFreeBlock(freeptr,total_size-asize);

        #ifdef DEBUG
          printf("re-alloacted %i\n",size);
          printheap();
        #endif
        return prev_blk;

      }
      else if(GET_SIZE(HDRP(prev_blk)) == (asize - cur_size)){//block is just large enough
        createAllocBlockWithData(prev_blk,asize,ptr);
        #ifdef DEBUG
          printf("re-alloacted %i\n",size);
          printheap();
        #endif
        return prev_blk;

      }

     }

  }
  else if(asize==cur_size){
    return ptr;
  }
  //need to copy to new location
  int * new = (int *)mm_malloc(size);
  copy(ptr,new);
  mm_free(ptr);
  #ifdef DEBUG
    printf("re-alloacted %i\n",size);
    printheap();
  #endif
  return new;


}
static void copy(const int* b1, const int* b2){
  int * end= FTRP(b2);
  while(b2!=end){
    PUT(b2,GET(b1));
    b2++;
    b1++;
  }
}