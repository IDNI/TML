// LICENSE
// This software is free for use and redistribution while including this
// license notice, unless:
// 1. is used for commercial or non-personal purposes, or
// 2. used for a product which includes or associated with a blockchain or other
// decentralized database technology, or
// 3. used for a product which includes or associated with the issuance or use
// of cryptographic or electronic currencies/coins/tokens.
// On all of the mentioned cases, an explicit and written permission is required
// from the Author (Ohad Asor).
// Contact ohad@idni.org for requesting a permission. This license may be
// modified over time by the Author.
#ifndef __MEMORY_MAP_H__
#define __MEMORY_MAP_H__
#include <stdio.h>
#include <stdlib.h>
#include <exception>
#ifdef _WIN32
#include <windows.h>
#else
#include <unistd.h>
#include <fcntl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#endif

#include "defs.h"

enum mmap_mode { MMAP_NONE, MMAP_READ, MMAP_WRITE };

class memory_map {
public:
	bool silent = true; // true to disable printing messages to o::err()
	bool error = false;
	std::string error_message = "";
	memory_map() : mode_(MMAP_NONE),state_(CLOSED),filename_(""),size_(0) {}
	size_t size() const { return size_; }
	std::string file_name() const { return filename_; }
	void clear_error() { error = false, error_message = ""; }
	void* data() {
		if (state_ != MAPPED) {
			//err("not MAPPED, cannot retrieve data pointer");
			return 0;
		}
		return data_;
	}
	char operator[](const size_t i) noexcept {
		return (static_cast<char*>(data_))[i];
	}
private:
	mmap_mode mode_;
	enum { CLOSED, UNMAPPED, MAPPED } state_;
	std::string filename_;
	size_t size_;
	void* data_ = 0;
	bool temporary_ = false;
#ifdef _WIN32
	HANDLE fh_;
	HANDLE mh_;
	inline void create_temp() {
		filename_ = temp_filename(), temporary_ = true;
	}
#else
	int fd_;
	int truncate() {
		if (state_==MAPPED) return err("cannot truncate mapped file");
		if (size_ && size_ != (size_t)file_size()) {
			if (::ftruncate(fd_, size_) == -1)
				return err(errno, "error truncate failed");
		}
		return size_;
	}
	inline void seek_beginning() {
		FILE *file = fdopen(fd_, "w");
		fseek(file, 0, SEEK_SET);
	}
	inline int fill() {
		int w = ::write(fd_, std::string(size_, 0).c_str(), size_);
		if (w == -1) err(errno, "memory_map: create (fill)");
		else seek_beginning();
		return w;
	}
	bool file_exists() {
 		struct stat s;
    		return filename_=="" ? false : stat(filename_.c_str(),&s) == 0;
	}
#endif
	size_t file_size() {
#ifdef _WIN32
		LARGE_INTEGER file_size;
		if (::GetFileSizeEx(fh_, &file_size) != 0)
			return static_cast<size_t>(file_size.QuadPart);
#else
		struct stat s;
		if (::stat(filename_.c_str(), &s) != -1)
			return s.st_size;
#endif
		return err(errno, "cannot get file stats"), 0;
	}
	int err(int err_code, std::string message, int return_value = -1) {
		return err(message, return_value, err_code);
	}
	int err(std::string message, int return_value = -1, int err_code = 0){
		error = true; std::stringstream ss; ss << "error: ";
		if (err_code) ss << '[' << err_code << "] ";
		ss << message << std::endl; error_message = ss.str();
		return return_value;
	}
};

template <typename T>
class memory_map_allocator {
public:
	typedef T value_type;
	memory_map_allocator() : fn(""), m(MMAP_NONE) { }
	memory_map_allocator(std::string fn, mmap_mode m = MMAP_WRITE) :
		fn(fn), m(m) { }
	memory_map_allocator(const memory_map_allocator<T>& a) :
		fn(a.fn), m(a.m) { }
	T* allocate(size_t n, const void* hint = 0) {
		//DBG(o::dbg()<<"allocate n="<<n<<" fn="
		//	<<s2ws(fn)<<" m="<<m<<std::endl;)
		if (m == MMAP_NONE) return (T*) nommap.allocate(n, hint);
		if (n == 0) return 0;
		//if (hint != 0) return 0; // not supported
		mm = std::make_unique<memory_map>();
		//o::dbg() << "mm.data() = " << mm->data() << std::endl;
		return (T*) mm->data();
	}
	void deallocate(T* p, size_t n) {
		//DBG(o::dbg()<<"deallocate n="<<n<<
		//	" fn="<<s2ws(std::string(fn))<<" m="<<m<<std::endl;)
		if (m == MMAP_NONE) return (void) nommap.deallocate(p, n);
		if (!p || !n) return;
	}
private:
	std::string fn;
	mmap_mode m;
	std::unique_ptr<memory_map> mm;
	std::allocator<T> nommap;
};

#endif
