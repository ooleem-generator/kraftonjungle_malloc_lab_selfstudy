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
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

// WSIZE를 4로 잡으면 int의 사이즈가 딱 1워드, 정렬 기준이 2워드 (책의 사각형 하나가 1워드) -> 32비트 기준
#define WSIZE 4 
#define DSIZE 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define CHUNKSIZE (1<<12) // 4KB

#define MAX(x,y) ((x) > (y) ? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc))

#define GET(p) (*(unsigned int *)(p)) // 주소 p로 가서 1워드만큼의 정보를 읽어옴
#define PUT(p, val) (*(unsigned int *)(p) = (val)) // 주소 p로 가서 1워드만큼을 val로 덮어씀

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

static char *heap_listp;

void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);



/*
 * mm_init - initialize the malloc package.
 mm init: Before calling mm malloc mm realloc or mm free, the application program 
 (i.e., the trace-driven driver program that you will use to evaluate your implementation) 
 calls mm init to perform any necessary initializations, such as allocating the initial heap area. 
 The return value should be -1 if there was a problem in performing the initialization, 0 otherwise.
 */
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) // 맨 처음에 일단 4워드 필요
        return -1; // 할당에 실패했을 경우 -1 리턴
    
    PUT(heap_listp, 0); // 패딩 블록 초기화
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); // 프롤로그 헤더 초기화
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); // 프롤로그 푸터 초기화
    PUT(heap_listp + (3*WSIZE), PACK(0, 1)); // 에필로그 헤더 초기화
    
    heap_listp += (2*WSIZE); // 포인터 위치 -> 프롤로그 헤더-푸터 사이로

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) // 워드 수만큼의 free 블록을 받아온다
        return -1;

    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 Always allocate a block whose size is a multiple of the alignment.
 The mm malloc routine returns a pointer to an allocated block payload of at least size bytes.
 The entire allocated block should lie within the heap region and should not overlap with any other allocated chunk.
 We will comparing your implementation to the version of malloc supplied in the standard C library (libc).
 Since the libc malloc always returns payload pointers that are aligned to 8 bytes,
 your malloc implementation should do likewise and always return 8-byte aligned pointers.
 * 
 */
// void *mm_malloc(size_t size)
// {
//     size_t extendsize;

//     if (size == 0)
//         return NULL;

//     int newsize = ALIGN(size + SIZE_T_SIZE);
//     void *p = mem_sbrk(newsize);
//     if (p == (void *)-1)
//         return NULL;
//     else
//     {
//         *(size_t *)p = size;
//         return (void *)((char *)p + SIZE_T_SIZE);
//     }
// }

void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0)
        return NULL;
    
    if (size <= DSIZE)
        asize = 2*DSIZE; // 최소한 DSIZE만큼의 payload는 있어야 하기 때문에, 헤더+푸터 = DSIZE니까
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE); // N보다 크면서 N에 제일 가까운 M의 배수 -> (N+(M-1)/M)*M
    
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;

}


/*
 * mm_free - Freeing a block does nothing.
 The mm free routine frees the block pointed to by ptr. It returns nothing.
 This routine is only guaranteed to work when the passed pointer (ptr) was returned by
 an earlier call to mm malloc or mm realloc and has not yet been freed.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 The mm realloc routine returns a pointer to an allocated region of at least size bytes with the following constraints.
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

void *extend_heap(size_t words) {

    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */

    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    
    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    /* Coalesce if the prevoius block was free */
    return coalesce(bp);

}

static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {
        return bp;
    }

    else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }    

    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;

}

static void *find_fit(size_t asize) {
    
    char *find_bp;
    find_bp = heap_listp;

    while (GET_SIZE(HDRP(find_bp)) != 0) {
        find_bp = NEXT_BLKP(find_bp);
        if (GET_ALLOC(HDRP(find_bp)) == 0 && GET_SIZE(HDRP(find_bp)) >= asize) {
            return find_bp; 
        }
    }

    return NULL;

}

static void place(void *bp, size_t asize) {
    
    size_t old_freeblk_size = GET_SIZE(HDRP(bp));
    size_t rest_freeblk_size = old_freeblk_size - asize;

    if (rest_freeblk_size >= 2*DSIZE) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        PUT(FTRP(bp)+WSIZE, PACK(rest_freeblk_size, 0));
        PUT(FTRP(bp)+rest_freeblk_size, PACK(rest_freeblk_size, 0));
    }  
    else {
        PUT(HDRP(bp), GET(HDRP(bp)) | 0x1);
        PUT(FTRP(bp), GET(FTRP(bp)) | 0x1);
    }

}

