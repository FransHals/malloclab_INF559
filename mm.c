/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
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
    "Anan Task Force",
    /* First member's full name */
    "Aneta Zdeb",
    /* First member's email address */
    "aneta.zdeb@polytechnique.edu",
    /* Second member's full name (leave blank if none) */
    "Andi SAI",
    /* Second member's email address (leave blank if none) */
    "andi.sai@polytechnique.edu"
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* Basic constants and macros */
#define WSIZE		4		/* Word and header/footer size (bytes) */
#define DSIZE		8		/* Double word size (bytes) */
#define CHUNKSIZE	(1<<12)		/* Extend heap by this amount (bytes) */
#define INITCHUNKSIZE	(1<<6)		

#define MAX(x, y) ((x) > (y)? (x) : (y))
#define MIN(x, y) ((x) < (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a worrd at address p */
#define GET(p)			(*(unsigned int *)(p))
#define PUT(p, val)		(*(unsigned int *)(p) = (val)) | GET_TAG(p))
#define PUT_NOTAG(p, val)	(*(unsigned int *)(p) = (val))

/* Set predecedent or successive pointer for free blocks */
#define SET_BP(p, bp) 	(*(unsigned int *)(p) = (unsigned int)(bp))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)	(GET(p) & ~0x7)
#define GET_ALLOC(p)	(GET(p) & 0x1)
#define GET_TAG(p)	(GET(p) & 0x2)
#define SET_RATAG(p)	(GET(p) |= 0x2)
#define REMOVE_RATAG(p)	(GET(p) &= ~0x2)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)	((char *)(bp) - WSIZE)
#define FTRP(bp)	((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) 	((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) 	((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Given block ptr bp, compute address of previous and next entries of free block*/
#define PRED_BP(bp)	((char *)(bp))
#define SUCC_BP(bp)	((char *)(bp) + WSIZE)

/* Compute the address of previous and next block on the segregated list */
#define PRED(bp)	(*(char **)(bp))
#define SUCC(bp)	(*(char **)(SUCC_PTR(bp)))

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define LISTLIMIT	20
#define REALLOC_BUFFER	(1<<7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Private global variables */
void *segregated_free_lists[LISTLIMIT];
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *place(void *bp, size_t size);
static void insert_node(void *bp, size_t size);
static void delete_node(void *bp);

static char *mem_heap;      /* Points to first byte of heap */
static char *mem_brk;       /* Points to last byte of heap plus one */
static char *mem_max_addr;  /* Max legal heap addr plus one */
static char *heap_listp;    /* Points to the prologue block or next block */

/* --------------------------------Helper Functions-------------------------------------- */

/* 
 * Extends the heap with a new free block 
 */
static void *extend_heap(size_t words)
{
	char *bp;
	size_t size;
	
	/* Allocate an even number of words to maintain alignment */
	size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
	if ((long)(bp = mem_sbrk(size)) == -1)
		return NULL;
	
	/* Initialize free block header/footer and the epilogue header */
	PUT_NOTAG(HDRP(bp), PACK(size, 0);			/* Free block header */
	PUT_NOTAG(FTRP(bp), PACK(size, 0);			/* Free block footer */
	PUT_NOTAG(HDRP(NEXT_BLKP(bp)), PACK(0, 1));	/* New epilogue header */
	insert_node(bp, size);
			  
	/* Coalesce if the previous block was free */
	return coalesce(bp);
}	

static void insert_node(void *bp, size_t size)
{
	int list = 0;
	void *search_bp = bp;
	void *insert_bp = NULL;
	
	/* Select segregated list */
	while ((list < LISTLIMIT - 1) && (size > 1)) {
		size >>= 1;
		list ++;
	}
	
	/* Search list and order by size increasingly */
	search_bp = segregated_free_list[list];
	while ((search_bp != NULL) && (size > GET_SIZE(HDRP(search_bp)))) {
		insert_bp = search_bp;
		search_bp = PRED(search_bp);
	}
	
	/* Initialize previous and next pointer */
	if (search_bp != NULL) {
		if (insert_bp != NULL) {
			SET_BP(PRED_BP(bp), search_bp);
			SET_BP(SUCC_BP(search_bp), bp);
			SET_BP(SUCC_BP(bp), insert_bp);
			SET_BP(PRED_BP(insert_bp), bp);
		} else {
			SET_BP(PRED_BP(bp), search_bp);
			SET_BP(SUCC_BP(search_bp), bp);
			SET_BP(SUCC_bp), NULL);
			segregated_free_lists[list] = bp;
		}
	}
	
	return;
}
			  
static void delete_note(void *bp)
{
	
	
	
/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
//    mem_heap = (char *)Malloc(MAX_HEAP);
//    mem_brk = (char *)mem_heap;
//    mem_max_addr = (char *)(mem_heap + MAX_HEAP);
//    return 0;
	/* Create the initial empty heap */
	if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
		return 01;
	PUT(heap_listp, 0);				/* Alignment padding */
	PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));	/* Prologue header */
	PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));	/* Prologue footer */
	PUT(heap_listp + (3*WSIZE), PACK(0, 1));	/* Epilogue header */
	heap_listp += (2*WSIZE);
	
	/* Extend the empty heap with a free block of CHUNKSIZE bytes */
	if (extend_heap(CHUNKSIZE/WSIZE == NULL)
	    return -1;
	return 0;
}
		

static void *coalesce(void *bp)
{
	size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));
	
	if (prev_alloc && next_alloc) {			/* Case 1 */
		return bp;
	}
	
	else if(prev_alloc && !next_alloc) {	/* Case 2 */
		size += GET_SIZE(HDRP(NEXT)BLKP(bp)));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
	}
	
	else if(!prev_alloc && next_alloc) {	/* Case 3 */
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		PUT(FTRP(bp), PACK(size, 0);
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	}
	
	else {									/* Case 4 */
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
			GET_SIZE(FTRP(NEXT_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	}
	return bp;
}
	
			
/*
 * A first-fit search of the implicit free list
 */
static void *find_fit(size_t size){
}

/*
 * Place the requested block at the beginning of the free block,
 * splitting only if the size of the remainder would equal or
 * exceed the minimum block size
 */
static void place(void *bp, size_t size){
}

/*
 * mem_sbrk - Simple model of sbrk function. Extends the heap
 *  by incr bytes and returns the start addr of the new area.
 *  In this model, the heap cannot be shrunk.
 */
void *mem_sbrk(int incr)
{
    char *old_brk = mem_brk;
    
    if ( (incr < 0) || ((mem_brk + incr) > mem_max_addr)) {
        errno = ENOMEM;
        fprintf(stderr, "ERROR: mem_sbrk failed. Ran out of memory...\n");
        return (void *)-1;
    }
    mem_brk += incr;
    return (void *)old_brk;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
//    int newsize = ALIGN(size + SIZE_T_SIZE);
//    void *p = mem_sbrk(newsize);
//    if (p == (void *)-1)
//	return NULL;
//    else {
//        *(size_t *)p = size;
//        return (void *)((char *)p + SIZE_T_SIZE);
//    }
	size_t asize;		/* Adjusted block size */
	size_t extendsize;  /* Amount to extend heap if no fit */
	char *bp;
	
	/* Ignore spurious request */
	if (size == 0)
		return NULL;
	
	/* Adjust block size to include overhead and alignment reqs */
	if (size <= DSIZE)
		asize = 2*DSIZE;
	else
		asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
	
	/* Search the free list for a fit */
	if ((bp = find_fit(asize)) != NULL) {
		place(bp, asize);
		return bp;
	}
	
	/* No fit found. Get more memory and place the block */
	extendsize = MAX(asize, CHUNKSIZE);
	if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
		return NULL;
	place(bp, asize);
	return bp;
}
		
/*
 * mm_free - Frees a block and uses boundary-tag coalescing to merge it
 * with any adjacent free blocks in constant time.
 */
void mm_free(void *ptr)
{
	size_t size = GET_SIZE(HDRP(bp));
	
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	coalesce(bp);
}		

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}
