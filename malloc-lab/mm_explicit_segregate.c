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
#define ALIGNMENT 16

// WSIZE를 4로 잡으면 int의 사이즈가 딱 1워드, 정렬 기준이 2워드 (책의 사각형 하나가 1워드) -> 32비트 기준
#define WSIZE 8
#define DSIZE 16

#define GROUP_1 1
#define GROUP_2 2
#define GROUP_3 3
#define GROUP_4 4

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define CHUNKSIZE (1<<8) // 4KB

#define MAX(x,y) ((x) > (y) ? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc))

#define GET(p) (*(unsigned long *)(p)) // 주소 p로 가서 1워드만큼의 정보를 읽어옴
#define PUT(p, val) (*(unsigned long *)(p) = (val)) // 주소 p로 가서 1워드만큼을 val로 덮어씀

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define NEXT_FREEBLKP(bp) (GET((char *)(bp) + WSIZE))
#define PREV_FREEBLKP(bp) (GET((char *)(bp)))


static char *heap_listp;

void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize, int group);
static void place(void *bp, size_t asize, int old_freeblk_group);
static void last_free_check_update(void *bp, int group);
static void *prev_freebp(void *bp, int group);
static void *next_freebp(void *bp, int group);
static int group_checker(size_t size);


/*
 * mm_init - initialize the malloc package.
 mm init: Before calling mm malloc mm realloc or mm free, the application program 
 (i.e., the trace-driven driver program that you will use to evaluate your implementation) 
 calls mm init to perform any necessary initializations, such as allocating the initial heap area. 
 The return value should be -1 if there was a problem in performing the initialization, 0 otherwise.
 */

int mm_init(void)
{
    if ((heap_listp = mem_sbrk(12*WSIZE)) == (void *)-1) // 맨 처음에 일단 12워드 필요
        return -1; // 할당에 실패했을 경우 -1 리턴
    
    PUT(heap_listp, 0); // 패딩 블록 초기화
    PUT(heap_listp + (1*WSIZE), PACK(6*DSIZE, 1)); // 프롤로그 헤더 초기화

    /* 32-64 group */
    PUT(heap_listp + (2*WSIZE), heap_listp + 2*WSIZE); // 프롤로그 last_freeblk 초기화 -> 맨 처음에는 자기 자신의 주소를 저장해야 함
    PUT(heap_listp + (3*WSIZE), heap_listp + 12*WSIZE); // 프롤로그 init_freeblk 초기화
    
    /* 64-128 group */
    PUT(heap_listp + (4*WSIZE), heap_listp + 4*WSIZE); // 프롤로그 last_freeblk 초기화 -> 맨 처음에는 자기 자신의 주소를 저장해야 함
    PUT(heap_listp + (5*WSIZE), heap_listp + 12*WSIZE); // 프롤로그 init_freeblk 초기화
    
    /* 128-256 group */
    PUT(heap_listp + (6*WSIZE), heap_listp + 6*WSIZE); // 프롤로그 last_freeblk 초기화 -> 맨 처음에는 자기 자신의 주소를 저장해야 함
    PUT(heap_listp + (7*WSIZE), heap_listp + 12*WSIZE); // 프롤로그 init_freeblk 초기화    
    
    /*over 256 group */
    PUT(heap_listp + (8*WSIZE), heap_listp + 8*WSIZE); // 프롤로그 last_freeblk 초기화 -> 맨 처음에는 자기 자신의 주소를 저장해야 함
    PUT(heap_listp + (9*WSIZE), heap_listp + 12*WSIZE); // 프롤로그 init_freeblk 초기화    

    PUT(heap_listp + (10*WSIZE), PACK(6*DSIZE, 1)); // 프롤로그 푸터 초기화
    PUT(heap_listp + (11*WSIZE), PACK(0, 1)); // 에필로그 헤더 초기화
    
    heap_listp += (2*WSIZE); // 포인터 위치 -> 프롤로그 블록 포인터 위치

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

void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0)
        return NULL;
    
    if (size <= DSIZE)
        asize = 2*DSIZE; // 최소한 DSIZE+DSIZE만큼은 있어야 하기 때문에, 헤더+푸터 = DSIZE, pred+succ = DSIZE니까
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE); // N보다 크면서 N에 제일 가까운 M의 배수 -> (N+(M-1)/M)*M
    
    int group = group_checker(asize);

    while (group <= GROUP_4) {
        if ((bp = find_fit(asize, group)) != NULL) {
            place(bp, asize, group);
            return bp;
        }
        group += 1;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    
    group = group_checker(GET_SIZE(HDRP(bp)));
    place(bp, asize, group);
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
    assert(size != 0);

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
    //copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    copySize = GET_SIZE(HDRP(oldptr));
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}


// void *mm_realloc(void *bp, size_t size)
// {
//     void *new_bp;
//     size_t copy_size;
//     size_t asize;

//     if (size == 0)
//         return NULL;
    
//     if (size <= DSIZE)
//         asize = 2*DSIZE; // 최소한 DSIZE+DSIZE만큼은 있어야 하기 때문에, 헤더+푸터 = DSIZE, pred+succ = DSIZE니까
//     else
//         asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE); // N보다 크면서 N에 제일 가까운 M의 배수 -> (N+(M-1)/M)*M

//     copy_size = GET_SIZE(HDRP(bp));

//     if (asize < copy_size) {
//         place(bp, asize);
        
//         return bp;
//     }

//     else {
//         new_bp = mm_malloc(size);
//         if (new_bp == NULL)
//             return NULL;
//         memcpy(new_bp, bp, copy_size);
//         mm_free(bp);

//         return new_bp;
//     }
// }


void *extend_heap(size_t words) {

    char *bp;
    size_t size;
    char *update_bp = heap_listp+WSIZE;

    /* Allocate an even number of words to maintain alignment */

    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    
    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    
    char *epilogue_bp = NEXT_BLKP(bp);
    PUT(HDRP(epilogue_bp), PACK(0, 1));

    // 이제 bp는 힙을 늘리기 전 에필로그 블럭 주소를 의미한다 
    for (int i = 0; i < 4; i++) {
        if (GET(update_bp) == bp) {
            PUT(update_bp, epilogue_bp);
        }
        update_bp += DSIZE;
    }

    /* Coalesce if the prevoius block was free */
    return coalesce(bp);

}


static void *coalesce(void *bp) { 
    /*
    병합이 일어나는 상황 -> extend_heap, free 
    extend_heap에서 호출된 경우에는 무조건 뒤에가 에필로그 블록

    만약 뒤에가 에필로그 블럭이면 무조건 연결리스트 맨 뒤에 있게하면됨
    이 경우엔 시간을 줄일 수 있음 -> 프롤로그 블럭에 연결리스트 마지막 블럭 정보를 포함하게 했으니까

    */
    char *old_prev_bp;
    char *old_next_bp;
    size_t prev_alloc = GET_ALLOC(bp - DSIZE);
    size_t next_alloc = GET_ALLOC(bp + GET_SIZE(HDRP(bp)) - WSIZE);
    size_t size = GET_SIZE(HDRP(bp));
    size_t old_prev_size;
    size_t old_next_size;
    int old_prev_group;
    int old_next_group;
    int new_group;

    if (prev_alloc && next_alloc) {
        /* 앞뒤 둘다 할당된 블럭일때 (Case 1)
        이 경우는 병합 불가
        새로 생성되는 free 블록의 사이즈가 size로 확정되어짐 */

        new_group = group_checker(size);
        
        PUT(bp, prev_freebp(bp, new_group));
        PUT(bp+WSIZE, next_freebp(bp, new_group));

        // 그 다음에, 해당하는 곳으로 가서 연결해줘야함
        // 단, next_free가 에필로그 블록일 경우는 연결할 필요 없음

        PUT(PREV_FREEBLKP(bp)+WSIZE, bp);
        if (GET_SIZE(HDRP(NEXT_FREEBLKP(bp))) != 0) {
            PUT(NEXT_FREEBLKP(bp), bp);
        }

        last_free_check_update(bp, new_group); // 이제 

        return bp;
    }

    else if (prev_alloc && !next_alloc) { 
        /* 뒤에꺼 합침 (Case 2)

        뒷블럭 사이즈 그룹에서 뒷블럭이 없어짐
        합쳐진블럭 사이즈 그룹에 지금 블럭이 새로 추가됨 */

        // 뒷블럭 사이즈 그룹 확인
        old_next_bp = NEXT_BLKP(bp);

        old_next_size = GET_SIZE(HDRP(old_next_bp));
        old_next_group = group_checker(old_next_size);

        // 합쳐진블럭 사이즈 그룹 확인
        size += old_next_size;
        new_group = group_checker(size);
        
        
        // 일단 뒷블럭 사이즈 그룹 연결관계 정리해주기 - 뒷블럭이 없어짐
        PUT(PREV_FREEBLKP(old_next_bp)+WSIZE, NEXT_FREEBLKP(old_next_bp));
        if (GET_SIZE(HDRP(NEXT_FREEBLKP(old_next_bp))) != 0) {
            PUT(NEXT_FREEBLKP(old_next_bp), PREV_FREEBLKP(old_next_bp));
        }

        last_free_check_update(PREV_FREEBLKP(old_next_bp), old_next_group);

        //
        
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));

        PUT(bp, prev_freebp(bp, new_group));
        PUT(bp+WSIZE, next_freebp(bp, new_group));

        PUT(PREV_FREEBLKP(bp)+WSIZE, bp);
        if (GET_SIZE(HDRP(NEXT_FREEBLKP(bp))) != 0) {
            PUT(NEXT_FREEBLKP(bp), bp);
        }
        
        last_free_check_update(bp, new_group);

    }    

    else if (!prev_alloc && next_alloc) { 
        /* 앞에꺼 합침 (Case 3)

        앞블럭 사이즈 그룹에서 앞블럭이 없어짐
        합쳐진블럭 사이즈 그룹에 지금 블럭이 새로 추가됨 */ 
        
        // 앞블럭 사이즈 그룹 확인
        old_prev_bp = PREV_BLKP(bp);

        old_prev_size = GET_SIZE(HDRP(old_prev_bp));
        old_prev_group = group_checker(old_prev_size);

        // 합쳐진블럭 사이즈 그룹 확인
        size += old_prev_size;
        new_group = group_checker(size);


        // 일단 앞블럭 사이즈 그룹 연결관계 정리해주기 - 앞블럭이 없어짐
        PUT(PREV_FREEBLKP(old_prev_bp)+WSIZE, NEXT_FREEBLKP(old_prev_bp));
        if (GET_SIZE(HDRP(NEXT_FREEBLKP(old_prev_bp))) != 0) {
            PUT(NEXT_FREEBLKP(old_prev_bp), PREV_FREEBLKP(old_prev_bp));
        }

        last_free_check_update(PREV_FREEBLKP(old_prev_bp), old_prev_group);

        // 이제 bp를 PREV_BLKP(bp)로 변경
        bp = PREV_BLKP(bp);

        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));

        PUT(bp, prev_freebp(bp, new_group));
        PUT(bp+WSIZE, next_freebp(bp, new_group));

        PUT(PREV_FREEBLKP(bp)+WSIZE, bp);
        if (GET_SIZE(HDRP(NEXT_FREEBLKP(bp))) != 0) {
            PUT(NEXT_FREEBLKP(bp), bp);
        }
        
        last_free_check_update(bp, new_group);

    }

    else {
        /* 앞뒤 합침 (Case 4)

        앞블럭 사이즈 그룹에서 앞블럭이 없어짐
        뒷블럭 사이즈 그룹에서 뒷블럭이 없어짐
        합쳐진블럭 사이즈 그룹에 지금 블럭이 새로 추가됨 */ 

        // 앞블럭 사이즈 그룹 확인
        old_prev_bp = PREV_BLKP(bp);

        old_prev_size = GET_SIZE(HDRP(old_prev_bp));
        old_prev_group = group_checker(old_prev_size);

        // 뒷블럭 사이즈 그룹 확인
        old_next_bp = NEXT_BLKP(bp);

        old_next_size = GET_SIZE(HDRP(old_next_bp));
        old_next_group = group_checker(old_next_size);

        // 합쳐진블럭 사이즈 그룹 확인
        size += (old_prev_size+old_next_size);
        new_group = group_checker(size);

        // 일단 앞블럭 사이즈 그룹 연결관계 정리해주기 - 앞블럭이 없어짐
        PUT(PREV_FREEBLKP(old_prev_bp)+WSIZE, NEXT_FREEBLKP(old_prev_bp));
        if (GET_SIZE(HDRP(NEXT_FREEBLKP(old_prev_bp))) != 0) {
            PUT(NEXT_FREEBLKP(old_prev_bp), PREV_FREEBLKP(old_prev_bp));
        }

        last_free_check_update(PREV_FREEBLKP(old_prev_bp), old_prev_group);

        // 일단 뒷블럭 사이즈 그룹 연결관계 정리해주기 - 뒷블럭이 없어짐
        PUT(PREV_FREEBLKP(old_next_bp)+WSIZE, NEXT_FREEBLKP(old_next_bp));
        if (GET_SIZE(HDRP(NEXT_FREEBLKP(old_next_bp))) != 0) {
            PUT(NEXT_FREEBLKP(old_next_bp), PREV_FREEBLKP(old_next_bp));
        }

        last_free_check_update(PREV_FREEBLKP(old_next_bp), old_next_group);

        // 이제 bp를 PREV_BLKP(bp)로 변경
        bp = PREV_BLKP(bp);

        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));

        PUT(bp, prev_freebp(bp, new_group));
        PUT(bp+WSIZE, next_freebp(bp, new_group));

        PUT(PREV_FREEBLKP(bp)+WSIZE, bp);
        if (GET_SIZE(HDRP(NEXT_FREEBLKP(bp))) != 0) {
            PUT(NEXT_FREEBLKP(bp), bp);
        }
        
        last_free_check_update(bp, new_group);
        
    }

    return bp;

}


static void *find_fit(size_t asize, int group) {

    char *find_bp = heap_listp; // seg fault 방지용

    switch (group)
    {
        case GROUP_1:
            find_bp = heap_listp;
        break;

        case GROUP_2:
            find_bp = heap_listp + DSIZE;
        break;

        case GROUP_3:
            find_bp = heap_listp + 2*DSIZE;
        break;

        case GROUP_4:
            find_bp = heap_listp + 3*DSIZE;
        break;

    }

    while (GET_SIZE(HDRP(find_bp)) != 0) {
        find_bp = NEXT_FREEBLKP(find_bp);
        if (GET_SIZE(HDRP(find_bp)) >= asize) {
            return find_bp; 
        }
    }

    return NULL;

}


static void place(void *bp, size_t asize, int old_freeblk_group) {
    
    size_t old_freeblk_size = GET_SIZE(HDRP(bp));
    size_t rest_freeblk_size = old_freeblk_size - asize;

    if (rest_freeblk_size >= 2*DSIZE) {
        int rest_freeblk_group = group_checker(rest_freeblk_size);

        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        
        // old_freeblk_group의 연결관계 정리
        PUT(PREV_FREEBLKP(bp)+WSIZE, NEXT_FREEBLKP(bp));
        if (GET_SIZE(HDRP(NEXT_FREEBLKP(bp))) != 0) {
            PUT(NEXT_FREEBLKP(bp), PREV_FREEBLKP(bp));
        }
        last_free_check_update(PREV_FREEBLKP(bp), old_freeblk_group);

        // 현재 위치에서 bp 할일 끝, 이제 rest_free블록으로 이동
        bp += asize;

        PUT(HDRP(bp), PACK(rest_freeblk_size, 0));
        PUT(FTRP(bp), PACK(rest_freeblk_size, 0));        
        PUT(bp, prev_freebp(bp, rest_freeblk_group)); //
        PUT(bp+WSIZE, next_freebp(bp, rest_freeblk_group)); //
        
        // rest_freeblk_group의 연결관계 새로 설정
        PUT(PREV_FREEBLKP(bp)+WSIZE, bp);
        if (GET_SIZE(HDRP(NEXT_FREEBLKP(bp))) != 0) {
            PUT(NEXT_FREEBLKP(bp), bp);
        }
        last_free_check_update(bp, rest_freeblk_group);
    }  
    else {
        PUT(HDRP(bp), GET(HDRP(bp)) | 0x1);
        PUT(FTRP(bp), GET(FTRP(bp)) | 0x1);

        PUT(PREV_FREEBLKP(bp)+WSIZE, NEXT_FREEBLKP(bp));
        if (GET_SIZE(HDRP(NEXT_FREEBLKP(bp))) != 0) {
            PUT(NEXT_FREEBLKP(bp), PREV_FREEBLKP(bp));
        }
        last_free_check_update(PREV_FREEBLKP(bp), old_freeblk_group);
    }

}

static void last_free_check_update(void *bp, int group) { // bp 기준으로 자기 자신이 last_free인지 체크하는 함수
    assert(group != 0);

    if (GET_SIZE(HDRP(NEXT_FREEBLKP(bp))) == 0) { // next_free가 에필로그 블록이면 last_free이다
        switch (group)
        {
            case GROUP_1:
                PUT(heap_listp, bp);
            break;

            case GROUP_2:
                PUT(heap_listp+DSIZE, bp);
            break;

            case GROUP_3:
                PUT(heap_listp+2*DSIZE, bp);
            break;

            case GROUP_4:
                PUT(heap_listp+3*DSIZE, bp);
            break;

        }
        
         // 따라서 heap_listp에다가 bp 주소를 넣어줌
    }

}

static void *prev_freebp(void *bp, int group) { // bp 기준으로 prev_free 찾아주는 함수
    assert(group != 0);
    char *find_freebp = heap_listp; // seg fault 방지용

    switch (group)
    {
        case GROUP_1:
            find_freebp = heap_listp;
        break;

        case GROUP_2:
            find_freebp = heap_listp + DSIZE;
        break;

        case GROUP_3:
            find_freebp = heap_listp + 2*DSIZE;
        break;

        case GROUP_4:
            find_freebp = heap_listp + 3*DSIZE;
        break;

    }

    if (GET_SIZE(HDRP(NEXT_BLKP(bp))) == 0) {
        // 만약 다음 블록이 에필로그 블록이면, prev_free가 free 블럭 리스트의 마지막이었다는 얘기
        return GET(find_freebp);
        
    }

    while (NEXT_FREEBLKP(find_freebp) < bp) {
        find_freebp = NEXT_FREEBLKP(find_freebp);
    }
    return find_freebp;

}

static void *next_freebp(void *bp, int group) { // bp 기준으로 next_free 찾아주는 함수
    assert(group != 0);

    char *find_freebp = heap_listp; // seg fault 방지용

    switch (group)
    {
        case GROUP_1:
            find_freebp = heap_listp;
        break;

        case GROUP_2:
            find_freebp = heap_listp + DSIZE;
        break;

        case GROUP_3:
            find_freebp = heap_listp + 2*DSIZE;
        break;

        case GROUP_4:
            find_freebp = heap_listp + 3*DSIZE;
        break;

    }

    if (GET_SIZE(HDRP(NEXT_BLKP(bp))) == 0) {
    // 만약 다음 블럭이 에필로그 블럭이면, 바로 에필로그 블럭 포인터 반환하면 됨
        return NEXT_BLKP(bp);
    }

    while (NEXT_FREEBLKP(find_freebp) < bp) {
        find_freebp = NEXT_FREEBLKP(find_freebp);
        if (GET_SIZE(HDRP(find_freebp)) == 0) { // 버그 대응을 위한 이중체크
            return find_freebp;
        }

    }
    return NEXT_FREEBLKP(find_freebp);

}

static int group_checker(size_t size) {
    assert(size >= 32);

    if (size < 32) return 0;
    else if (size >= 32 && size < 64) return GROUP_1;
    else if (size >= 64 && size < 128) return GROUP_2;
    else if (size >= 128 && size < 256) return GROUP_3;
    else return GROUP_4;
    
}