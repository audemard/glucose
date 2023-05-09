#ifndef COSOCO_DOMAINITERATOR_H
#define COSOCO_DOMAINITERATOR_H


#include <iterator>

namespace Glucose {


template <typename T>
class VecIterator : public std::iterator<std::random_access_iterator_tag, T> {
    friend class VecIterator<const T>;

   protected:
    T * ptr_;
    int shift;

   public:
    inline VecIterator(T *ptr = nullptr, int _shift = 1) : ptr_(ptr), shift(_shift) { }


    inline VecIterator(const VecIterator &pos) : ptr_(pos.ptr_), shift(pos.shift) { }


    inline ~VecIterator() { }


   public:
    inline VecIterator &operator=(const VecIterator &other) {
        ptr_  = other.ptr_;
        shift = other.shift;
        return *this;
    }


    inline VecIterator &operator+=(int n) {
        ptr_ += (shift * n);
        return *this;
    }


    inline VecIterator &operator-=(int n) {
        ptr_ -= (shift * n);
        return *this;
    }


    inline VecIterator &operator++() {
        ptr_ += shift;
        return *this;
    }


    inline VecIterator &operator--() {
        ptr_ -= shift;
        return *this;
    }


    inline VecIterator operator+(int n) {
        VecIterator pos(*this);
        pos.ptr_ += (shift * n);
        return pos;
    }


    inline VecIterator operator-(int n) {
        VecIterator pos(*this);
        pos.ptr_ -= (shift * n);
        return pos;
    }


    inline bool operator==(const VecIterator &other) const { return (ptr_ == other.ptr_ && shift == other.shift); }


    inline bool operator!=(const VecIterator &other) const { return (ptr_ != other.ptr_ || shift != other.shift); }


    inline bool operator<(const VecIterator &other) const { return (ptr_ < other.ptr_ && shift == other.shift); }


    inline bool operator>(const VecIterator &other) const { return (ptr_ > other.ptr_ && shift == other.shift); }


    inline bool operator<=(const VecIterator &other) const { return (ptr_ <= other.ptr_ && shift == other.shift); }


    inline bool operator>=(const VecIterator &other) const { return (ptr_ >= other.ptr_ && shift == other.shift); }


    inline int operator-(const VecIterator &other) {
        assert(other.shift == shift);
        return (std::distance(other.ptr_, ptr_) / shift);
    }


    inline T &operator*() { return *ptr_; }


    inline T *operator->() { return ptr_; }


    inline T *ptr() { return ptr_; }
};
}   // namespace Glucose
#endif   // COSOCO_DOMAINITERATOR_H
