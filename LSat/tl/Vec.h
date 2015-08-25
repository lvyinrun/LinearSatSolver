#ifndef VEC_H_INCLUDED
#define VEC_H_INCLUDED

#include <stdlib.h>
#include <assert.h>
#include <limits>
#include <new>

#include <../tl/Xalloc.h>
//=================================================================================================
// Automatically resizable arrays
//
// NOTE! Don't use this vector on datatypes that cannot be re-located in memory (with realloc)

template<class T, class _Size = int>
class vec {
public:
    typedef _Size Size;
private:
    T*   data;
    Size sz;
    Size cap;
	static inline Size max(Size x, Size y){ return (x > y) ? x : y; }
public:
	// Constructors:
    // Constructors:
    vec()                        : data(NULL), sz(0), cap(0)    { }
    explicit vec(Size size)      : data(NULL), sz(0), cap(0)    { growTo(size); }
    vec(Size size, const T& pad) : data(NULL), sz(0), cap(0)    { growTo(size, pad); }
   ~vec()                                                       { clear(true); }

    // Pointer to first element:
    operator T*       (void)           { return data; }

	// Size operations:
    Size     size     (void) const   { return sz; }
	void     shrink   (Size nelems)  { assert(nelems <= sz); for (Size i = 0; i < nelems; i++) sz--, data[sz].~T(); }
    void     shrink_  (Size nelems)  { assert(nelems <= sz); sz -= nelems; }
    int      capacity (void) const   { return cap; }
    void     capacity (Size min_cap);
    void     growTo   (Size size);
    void     growTo   (Size size, const T& pad);
    void     clear    (bool dealloc = false);

    //stack interface
	void     push  (void)              { if (sz == cap) capacity(sz+1); new (&data[sz]) T(); sz++; }
    //void     push  (const T& elem)     { if (sz == cap) capacity(sz+1); data[sz++] = elem; }
    void     push  (const T& elem)     { if (sz == cap) capacity(sz+1); new (&data[sz++]) T(elem); }
    void     push_ (const T& elem)     { assert(sz < cap); data[sz++] = elem; }
    void     pop   (void)              { assert(sz > 0); sz--, data[sz].~T(); }
        // NOTE: it seems possible that overflow can happen in the 'sz+1' expression of 'push()', but
    // in fact it can not since it requires that 'cap' is equal to INT_MAX. This in turn can not
    // happen given the way capacities are calculated (below). Essentially, all capacities are
    // even, but INT_MAX is odd.

    const T& last  (void) const        { return data[sz-1]; }
    T&       last  (void)              { return data[sz-1]; }

	// Vector interface:
    const T& operator [] (Size index) const { return data[index]; }
    T&       operator [] (Size index)       { return data[index]; }

	// Duplicatation (preferred instead):
    void copyTo(vec<T>& copy) const
    {
		copy.clear();
		copy.growTo(sz);
		for (Size i = 0; i < sz; i++)
			copy[i] = data[i];
		//printf("%s\n","copy over");
    }
    void moveTo(vec<T>& dest) { dest.clear(true); dest.data = data; dest.sz = sz; dest.cap = cap; data = NULL; sz = 0; cap = 0; }

};

template<class T, class _Size>
void vec<T,_Size>::capacity(Size min_cap) {
    if (cap >= min_cap) return;
    Size add = max((min_cap - cap + 1) & ~1, ((cap >> 1) + 2) & ~1);   // NOTE: grow by approximately 3/2
    const Size size_max = std::numeric_limits<Size>::max();
    if ( ((size_max <= std::numeric_limits<int>::max()) && (add > size_max - cap))
    ||   (((data = (T*)::realloc(data, (cap += add) * sizeof(T))) == NULL) && errno == ENOMEM) )
        throw OutOfMemoryException();
 }


template<class T, class _Size>
void vec<T,_Size>::clear(bool dealloc) {
    if (data != NULL){
        for (Size i = 0; i < sz; i++) data[i].~T();
        sz = 0;
        //这里为什么不能正常的析构
        //if (dealloc) free(data), data = NULL, cap = 0;
      } }


template<class T, class _Size>
void vec<T,_Size>::growTo(Size size, const T& pad) {
    if (sz >= size) return;
    capacity(size);
    for (Size i = sz; i < size; i++) data[i] = pad;
    sz = size; }


template<class T, class _Size>
void vec<T,_Size>::growTo(Size size) {
    if (sz >= size) return;
    capacity(size);
    for (Size i = sz; i < size; i++) new (&data[i]) T();
    sz = size; }


#endif // VEC_H_INCLUDED
