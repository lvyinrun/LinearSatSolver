#ifndef XALLOC_H_INCLUDED
#define XALLOC_H_INCLUDED


#include <errno.h>
#include <stdlib.h>
//=================================================================================================
// Simple layer on top of malloc/realloc to catch out-of-memory situtaions and provide some typing:

class OutOfMemoryException{};

static inline void* xrealloc(void *ptr, size_t size)
{
    void* mem = realloc(ptr, size);
    if (mem == NULL && errno == ENOMEM){
        throw OutOfMemoryException();
    }else
        return mem;
}

//=================================================================================================
#endif // XALLOC_H_INCLUDED
