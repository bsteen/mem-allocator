/*
Abraham McIlvaine and Benjamin Steenkamer
CISC 361-010
Lab 2

mm.c - Dynamic Storage Allocator

This is our memory allocator.  It contains the following features:
•Allocated Blocks contain header,footer, and payload
•Explicit Free List for free blocks
-Minimum block size is 16 bytes (header,prev,next,footer)
-prev and next pointers stored in free block payload area
-new free blocks are inserted at beginning of explicit free list
•Placement Policy
-if the free list size is less than BEST_FIT_THRESHOLD, then the allocator
uses a best fit search of the free list to place an allocated block
-otherwise, it uses first fit
-the free block found is deleted from the free list
•Dynamic Chunk Sizing (size of heap extension)
-This is another feature we added for both throughput and space efficiency
-The chunk size will gravitate towards the average request size
-This helps with external fragmentation (prevents allocating excessively large chunks)
•Grouping Small blocks
-We reserve special places in the heap for small blocks only
-This prevents small splinters from forming in between larger blocks
and being unusable after freeing
-When grouped, small blocks with coalesce into a larger one and it is more
likely that the block can be re-used
•Immediate Coalescing is used to combine free blocks and reduce external fragmentation
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
    "Abraham McIlvaine and Benjamin Steenkamer",
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
#define ONLY_SMALL_BLK_SIZE 1500 //size of reserved block for small blocks only
#define BEST_FIT_THRESHOLD 25 //threshold size of free list for choosing first fit instead of best fit
#define MIN_CHUNK (1<<9)//min chunk size for extending heap
#define MAX_CHUNK (1<<30)//max chunk size for extending heap
#define DEFAULT_CHUNK (1<<11)//default chunk size for extending heap
#define CHUNK_UPDATE_AMT 1024 //how much to change CHUNK_SIZE at a time
#define MAX(x,y) ((x) > (y)? (x) : (y))//max of two things
#define PACK(size,alloc) ((size) | (alloc))//used for making headers and footers
#define GET(p) (*(unsigned int *)(p))//gets p because b is a void *
#define PUT(p,val) (*(unsigned int *)(p) = (val))//puts val into p pointer
#define GET_SIZE(p) (GET(p) & ~0x7)//Extracts size from pointer
#define GET_ALLOC(p) (GET(p) & 0x1)//Extracts alloc bit from pointer
#define HDRP(bp) ((char *)(bp) - WSIZE)//location of header
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)//location of footer
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))//location of next block
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))//location of prev block
#define PREV(bp) ((char *) (bp))//prev pointer for free list location
#define NEXT(bp) ((char *) (bp)+WSIZE)//next pointer for free list location
#define DEBUGx //if DEBUG is defined, prints out heap at each step

static int CHUNK_SIZE = DEFAULT_CHUNK;//Chunks size variable
static void * free_list_head=NULL;//head of free list
static void * only_small_blk=NULL;//location of block reserved from small blocks
static unsigned long long free_list_size=0;//keeps track of the free list size
static char * heap_listp=NULL;//start of heap

static void * extend_heap(size_t words);
static void * coalesce(void * bp);
static void * find_fit(size_t asize);
static void place(void* bp, size_t asize);
static void del_free_list_node(void* bp);
static void ins_free_list_node(void *bp);
static void copy(const int* b1,const int* b2);
static void createFreeBlock(void * bp,size_t asize);
static void reserveOnlySmallBlock();
static void createAllocBlock(void * bp,size_t asize);
static void createAllocBlockWithData(void * bp,size_t size, void * data);
static void printfreelist();
static void place_into_allocated_block(void* bp, size_t asize);
int mm_check();

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
    for(bp=free_list_head;bp!=NULL; bp = (void*)GET(NEXT(bp))){
        printf("%p : %i, ",bp, GET_SIZE(HDRP(bp)));

    }
    printf("\b\b]\n");

}

/*   mm_init
•initializes the heap. Creates one free block of DEFAULT_CHUNK size and also
allocates space for only small blocks.
•returns -1 on error, 0 otherwise
*/
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
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE,1));//prolouge block header
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE,1));//prolouge block footer
    PUT(heap_listp + (3*WSIZE), PACK(0,1));//epilogue block (size 0, allocated)
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

/* mm_malloc
•allocates a block according to all policies listed the the header comment of this file
•Placement Policy
-if the free list size is less than BEST_FIT_THRESHOLD, then the allocator
uses a best fit search of the free list to place an allocated block
-otherwise, it uses first fit
-the free block found is deleted from the free list
•Dynamic Chunk Sizing (size of heap extension)
-This is another feature we added for both throughput and space efficiency
-The chunk size will gravitate towards the average request size
-This helps with external fragmentation (prevents allocating excessively large chunks)
•Grouping Small blocks
-We reserve special places in the heap for small blocks only
-This prevents small splinters from forming in between larger blocks
and being unusable after freeing
-When grouped, small blocks with coalesce into a larger one and it is more
likely that the block can be re-used
•Immediate Coalescing is used
•return blocks are 8 byte aligned
•returns a pointer to the newly allocated block of at least size bytes
*/
void *mm_malloc(size_t size)
{
    // if(!mm_check()){ //Check heap consistency
    //     exit(1);
    // }

    #ifdef DEBUG
    printf("malloc %i\n",size);
    printheap();
    #endif

    size_t asize;
    size_t extendsize;
    char * bp;
    if(size==0){ //Do not allocate block for size of 0
        return NULL;
    }

    asize = ALIGN(size) + 8;//alignes to double word
    if(asize < MIN_BLOCK_SIZE){
        asize = MIN_BLOCK_SIZE; //Maintain minimum block size
    }

    if(asize < 100){//special spot for small items
        int csize = GET_SIZE(HDRP(only_small_blk));
        if(asize < csize && (csize - asize) >= MIN_BLOCK_SIZE){
            void * ret_val = only_small_blk;
            PUT(HDRP(only_small_blk),PACK(asize,1));
            PUT(FTRP(only_small_blk),PACK(asize,1));
            only_small_blk=NEXT_BLKP(only_small_blk);
            PUT(HDRP(only_small_blk),PACK(csize-asize,1)); //the block is allocated to create a container for small blocks
            PUT(FTRP(only_small_blk),PACK(csize-asize,1));
            return ret_val;
        }else if(asize <=csize){ //Create a new small block container if the old one is full
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
    if((bp= find_fit(asize)) != NULL){//looks for block to place it in
        place(bp,asize);
        return bp;
    }

    //if here, find fit failed to find a usable free block
    //need to extend the heap
    extendsize = MAX(asize,CHUNK_SIZE);
    if(asize<(CHUNK_SIZE+CHUNK_UPDATE_AMT)){//dynamic updating of chunk size
        CHUNK_SIZE+=CHUNK_UPDATE_AMT;
    }else if ((asize-CHUNK_UPDATE_AMT) > CHUNK_SIZE){
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

/* mm_free
•frees a block pointed to by ptr and adds it to the free list
•Also, it coalesces the newly created free block.
•only guaranteed to work of the pointer points to a valid allocated block
*/
void mm_free(void *ptr)
{
    // if(!mm_check()){ //Check heap consistency
    //     exit(1);
    // }

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

/*  mm_realloc
•realloactes the block ptr to be the new size
•if ptr = null, equivalent to mm_malloc(size)
•if size==0, equivalent to mm_free(ptr)
•othersize, it either expands or shrinks the size of the block pointed to
by ptr so that the returned block is at least equal to size
•contents of the block are preserved up to minimum size of the old block and new block
•considers if the prev block is free, the next block is free
•if can't use prev or next block, moves block to a new space
•Returns a pointer to the newly reallocated block that is at least "size" bytes
*/
void *mm_realloc(void *ptr, size_t size)
{
    // if(!mm_check()){ //Check heap consistency
    //     exit(1);
    // }
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
        asize = ALIGN(size) + 8;
    }

    size_t cur_size = GET_SIZE(HDRP(ptr));


    if(asize < cur_size){ //The block size is being decreased
        place_into_allocated_block(ptr,asize);
        #ifdef DEBUG
        printf("re-alloacted %i\n",size);
        printheap();
        #endif
        return ptr;
    }
    else if(!GET_ALLOC(HDRP(NEXT_BLKP(ptr)))){//increasing block size and next block is free
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
    else if(!GET_ALLOC(FTRP(PREV_BLKP(ptr)))){//increasing block size and prev block is free
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

    //need to copy old data to new block
    int * new = (int *)mm_malloc(size);
    copy(ptr,new);
    mm_free(ptr);

    #ifdef DEBUG
    printf("re-alloacted %i\n",size);
    printheap();
    #endif

    return new;
}

/*mm_check
Used to check for invariants or inconsistencies in the heap.
CHECKS the following:
•check if every block in the free list is marked as free
•are any contiguous free blocks that escaped coalescing?
•is every free block ACTUALLY in the FREE LIST?
•DO pointers in the free list point to valid free blocks?
•do the pointers in the heap block point to valid heap addresses?
return a value of 1 only if the heap is consistent. If any of the tests fail,
an error message describing the error is printed and zero is returned.
•Test DOUBLE WORD ALIGNMENT
•Make sure the the free list has an end (block with next=NULL)

Returns 1 if all tests pass and 0 if one of the tests fails.
*/
int mm_check(){

    void *bp;
    char last_free=0;
    int free_cnt_1=0;//valid free blocks in free list
    int free_cnt_2=0;//free blocks counted by traversing heap

    //check if every block in the free list is marked as free.
    //Traverse the free list and verify that the allocate bit in every block's
    //header is set to zero.
    //Do pointers in the free list point to valid free blocks?
    for(bp = free_list_head; bp!=NULL; bp = (void*)GET(NEXT(bp))){
        if(GET_ALLOC(HDRP(bp)) && GET_ALLOC(FTRP(bp))){//checks validity of header and footer
            printf("Allocated block with heap address %p is incorrectly placed in the free list\n", bp);
            return 0;
        }
        //also checks size for inconsistencies
        if(GET_SIZE(HDRP(bp))!= GET_SIZE(FTRP(bp))){
            printf("Free block invalid: size inconsistencies in header/footer at address %p",bp);
            return 0;
        }

        ++free_cnt_1;

        //If the iterations of this loop exceed the size of the free list, the free list is circular
        //If a list is circular, infinite loops will occur
        if(free_cnt_1 > free_list_size){//make sure list is not circular
            printf("ERROR! Free list is circular. NO NULL PTR TO SHOW END OF LIST!\n");
            return 0;
        }
    }

    //this loops traverses the entire heap and checks multiple things

    for(bp = heap_listp; GET_SIZE(HDRP(bp))!=0; bp = NEXT_BLKP(bp)){
        //are any contiguous free blocks that escaped coalescing?
        //checks if two free blocks are adjacent to each other
        if(last_free && !GET_ALLOC(HDRP(bp))){
            printf("Free Blocks Escaped Coalescing at address %p\n", bp);
            return 0;
        }
        last_free = !GET_ALLOC(HDRP(bp));

        //update free_cnt_2; will be compared to free_cnt_1 later
        if(!GET_ALLOC(HDRP(bp))){
            ++free_cnt_2;
        }

        //do the pointers in the heap block point to valid addresses within the heap?
        if(bp  < mem_heap_lo() || bp > mem_heap_hi() ){
            //Pointer is outside the points of the heap
            printf("Invalid address! Address %p lies out of heap range [%p,%p]\n",bp,mem_heap_lo(),mem_heap_hi() );
            return 0;
        }
        //test if DOUBLE WORLD ALIGNMENT is maintained in the heap
        if(((unsigned int)bp & 7)){//is the bottom three bits 0? (multiple of 8)
            printf("Block at add address (%p) is NOT DOUBLE WORD ALIGNED!\n", bp);
            return 0;
        }
    }

    //is every free block ACTUALLY in the FREE LIST?
    if(free_cnt_1!=free_cnt_2){//checks count of free blocks by traversing free list vs. traversing heap directly
        printf("Not All Free blocks in free list\n");
        return 0;
    }

    return 1; //If this point is reached, the heap passed all the tests
}


/*HELPER FUNCTIONS ARE BELOW THIS LINE*/
/*------------------------------------*/

/*  extend_heap
•Extends heap. Calls mem_sbrk function to allocate more space on the heap.
 Returns a pointer to the new free block just created.  Also re-creates the epilogue block
 of the heap.
*/
static void * extend_heap(size_t words){
    char * bp;
    size_t size;

    //Maintain block alignment and minimum size.
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


/*  coalesce
•merges free blocks together to create larger free blocks and reduces external
fragmentation.
•For example, if FFF -> F
AFF -> AF
FFA -> FA
AFA -> AFA
•this gets called whenever the heap is extended, or a block is freed (immediate coalescing)
•updates free_list pointers and block headers/footers
•Returns a pointer to the updated free block
*/
static void * coalesce(void * bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size= GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {/* Case 1 prev and next block allocated*/
        return bp;
    }

    else if (prev_alloc && !next_alloc) {/* Case 2 prev block allocated, next block free*/
        del_free_list_node(NEXT_BLKP(bp));
        size+= GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size,0));
        PUT(FTRP(bp), PACK(size,0));
    }
    else if (!prev_alloc && next_alloc) { /* Case 3 prev block free, next block allocated*/
        del_free_list_node(PREV_BLKP(bp));
        PUT(PREV(PREV_BLKP(bp)),GET(PREV(bp)));
        PUT(NEXT(PREV_BLKP(bp)),GET(NEXT(bp)));
        void * next = (void *)GET(NEXT(bp));
        if(next!=NULL)
        PUT(PREV(next), (unsigned int)PREV_BLKP(bp));
        size+= GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size,0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        bp = PREV_BLKP(bp);
        free_list_head = bp;
    }
    else {/* Case 4 both prev and next blocks free*/
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        del_free_list_node(PREV_BLKP(bp));
        del_free_list_node(NEXT_BLKP(bp));
        PUT(PREV(PREV_BLKP(bp)),GET(PREV(bp)));
        PUT(NEXT(PREV_BLKP(bp)),GET(NEXT(bp)));

        if(NEXT(bp) != NULL && (void*)GET(NEXT(bp)) != NULL)
        PUT(PREV(GET(NEXT(bp))),(unsigned int)PREV_BLKP(bp));

        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0));
        bp = PREV_BLKP(bp);
        free_list_head = bp;

    }
    return bp;
}

/*   del_free_list_node
•deletes a node from the free list. Updates next and prev pointers by connecting
the next and previous blocks together and decreases the size of the free list
*/
static void del_free_list_node(void* bp){
    void * prev = (void*)GET(PREV(bp));
    void * next = (void*)GET(NEXT(bp));
    if(bp == free_list_head){
        free_list_head = next;
    }
    if(prev!=NULL){
        PUT(NEXT(prev), (unsigned int)next);
    }
    if(next!=NULL){
        PUT(PREV(next), (unsigned int)prev);
    }

    --free_list_size;
}

/*   ins_free_list_node
•inserts a node into the free list at the beginning
•updates the free_list_head pointer to point to bp and increases the
size of the free list
*/
static void ins_free_list_node(void *bp){
    if(free_list_head!=NULL){
        PUT(PREV(free_list_head), (unsigned int)bp);
    }
    PUT(NEXT(bp), (unsigned int)free_list_head);
    PUT(PREV(bp), (unsigned int)NULL);
    free_list_head=bp;
    ++free_list_size;
}

/*   createFreeBlock
•marks a block as free by updating header and footer, and then
adds to the free list
*/
static void createFreeBlock(void * bp,size_t size){
    PUT(HDRP(bp),PACK(size,0));
    PUT(FTRP(bp),PACK(size,0));
    ins_free_list_node(bp);
}

/*  reserveOnlySmallBlock
•creates a section in the heap that only small items can be places
newly created section is marked as allocated so that it doesn't get
coalesced.
•only_small_blk pointer is updated.
This area helps prevent external fragmentation caused by small block splinters.
*/
static void reserveOnlySmallBlock(){
    void* bp = mm_malloc(ONLY_SMALL_BLK_SIZE);
    PUT(HDRP(bp),PACK(GET_SIZE(HDRP(bp)),1) );
    PUT(FTRP(bp),PACK(GET_SIZE(HDRP(bp)),1) );
    only_small_blk=bp;
}

/*  createAllocBlock
•marks a block as allocated by updating header and footer
•deletes block from the free list
*/
static void createAllocBlock(void * bp,size_t size){
    PUT(HDRP(bp),PACK(size,1));
    PUT(FTRP(bp),PACK(size,1));
    del_free_list_node(bp);
}

/*  createAllocBlockWithData
•same as createAllocBlock, but also copies data from old block into new block
•calls copy function
*/
static void createAllocBlockWithData(void * bp,size_t size, void * data){
    del_free_list_node(bp);
    PUT(HDRP(bp),PACK(size,1));
    copy(data,bp);
    PUT(FTRP(bp),PACK(size,1));
}

/* copy
•copies contents from b1 to b2
•stops at FTRP(b2)
•used to copy data from one block to another (realloc)
*/
static void copy(const int* b1, const int* b2){
    int *end= (int*)FTRP(b2);
    while(b2!=end){
        PUT(b2,GET(b1));
        b2++;
        b1++;
    }
}

/*  find_fit
finds a usable free block
•Placement Policy
-if the free list size is less than BEST_FIT_THRESHOLD, then the allocator
uses a best fit search of the free list to place an allocated block
-otherwise, it uses first fit
-the free block found is deleted from the free list

•returns a pointer to the free block that can be used
*/
static void * find_fit(size_t asize){
    if(free_list_size < BEST_FIT_THRESHOLD){
        void* bp;
        void * ret_loc = NULL;
        unsigned int cur_size=-1;
        unsigned int tmp_size;
        for(bp=free_list_head;bp!=NULL; bp = (void*)GET(NEXT(bp))){
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

        for(bp=free_list_head;bp!=NULL; bp = (void*)GET(NEXT(bp))){
            if(asize <= GET_SIZE(HDRP(bp))){
                return bp;
            }
        }
        return NULL;
    }
}

/*   place
•places block of size asize into bp, which is the usable block returned by
findfit.
•if the block is large enough (the remaining part of the block
is >= MIN_BLOCK_SIZE), it is split into a free block and and allocated
block.
•Otherwise, the entire block is allocated.
*/
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


/* place_into_allocated_block
•same as place, but used if the block placing into a block that is currently
allocated. (used for special cases of realloc only)
*/
static void place_into_allocated_block(void* bp, size_t asize){
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
