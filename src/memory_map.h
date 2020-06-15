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
#include <sys/mman.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>   // TODO: MSVC mmap impl
#include <exception>

#include "defs.h"
#include "output.h"

enum mmap_mode { MMAP_NONE, MMAP_READ, MMAP_WRITE };

class memory_map {
public:
	bool silent = false; // true to disable printing messages to o::err()
	bool error = false;
	std::wstring error_message = L"";
	memory_map() : mode_(MMAP_NONE),state_(CLOSED),filename_(""),size_(0) {}
	memory_map(std::string filename, size_t s=0, mmap_mode m = MMAP_READ,
		bool do_open=1, bool do_map=1)
		: mode_(m), state_(CLOSED), filename_(filename), size_(s)
	{
		if (mode_ == MMAP_NONE) return;
		int oflag = m == MMAP_READ ? O_RDONLY : O_RDWR;
		DBG(std::wcout<<L"memory_map "//<<s2ws(std::string(filename_))
		 	<<" size: "<<size_<<" mode: "<<mode_
		 	<<" oflag: "<<oflag
		 	<<" do_open: "<<do_open<<" do_map: "<<do_map;)
		if (!size_) size_ = (size_t)file_size(); // autodetect map size
		DBG(std::wcout<<L" new_size: "<<size_<<std::endl;)
		if (do_open || do_map) if (open(oflag) == -1) return;
		if (do_map) map();
	}
	~memory_map() { if (state_ != CLOSED) close(); }
	size_t size() { return size_; }
	void reset_error() { error = false, error_message = L""; }
	void* data() {
		if (state_ != MAPPED) {
			err(L"not MAPPED, cannot retrieve data pointer");
			return 0;
		}
		return data_;
	}
	int open(int oflag = O_RDONLY, int open_mode = 0644) {
		//DBG(std::wcout<<L"memory_map: open "<<s2ws(std::string(filename_))<<" size: "
		//	<<size_<<" mode: "<<mode_<<" oflag: "<<oflag<<std::endl;)
		if (mode_  == MMAP_NONE) return err(L"none mmap - cannot");
		if (state_ != CLOSED)    return err(L"file is already opened");
		if ((oflag & O_WRONLY || oflag & O_RDWR) && !file_exists())
			create();
		else {
			fd_ = ::open(filename_.c_str(), oflag, open_mode);
    			if (fd_ == -1) return err(errno,
			    		L"cannot open file for memory map");
			if (oflag & O_WRONLY || oflag & O_RDWR)
				if (truncate() == -1) return -1;
		}
		//DBG(std::wcout<<L"memory_map: changing state to UNMAPPED (open)" << std::endl;)
		state_ = UNMAPPED;
		return fd_;
	}
	int map() {
		int prot = mode_==MMAP_READ ? PROT_READ : PROT_READ|PROT_WRITE;
		//DBG(std::wcout<<L"memory_map: map "<<s2ws(std::string(filename_))
		//	<<" size: "<<size_<<" prot: "<<prot
		//	<<std::endl;)
		if (state_ != UNMAPPED)
			return err(L"file is not opened or already mapped");
		data_ = ::mmap(0, size_, prot, MAP_SHARED, fd_, 0);
		if (data_ == MAP_FAILED) return data_=0,err(errno, L"mmap err");
		//DBG(std::wcout<<L"memory_map: changing state to MAPPED data: "<<&data_<<std::endl;)
		state_ = MAPPED;
		return 0;
	}
	int sync() {
		int r = ::msync(data_, size_, MS_SYNC);
		if (r == -1) return err(errno, L"memory_map: sync");
		return r;
	}
	int unmap() {
		if (state_ != MAPPED)
			return err(L"file not mapped. it cannot be unmapped\n");
		if (sync() == -1) return -1;
		int r = ::munmap(data_, size_);
		data_ = 0;
		//DBG(std::wcout << L"memory_map: changing state to UNMAPPED (unmap)" << std::endl;)
		state_ = UNMAPPED;
		return r;
	}
	int unlink() {
		if (state_ != CLOSED) return err(
			L"file is not closed. it cannot be deleted\n");
		return ::unlink(filename_.c_str());
	}
	int close() {
		if (state_ == CLOSED) return -1;
		else if (state_ == MAPPED && unmap() == -1) return -1;
		if (fd_ != -1) ::close(fd_), fd_ = -1;
		//DBG(std::wcout << L"memory_map: changing state to CLOSED" << std::endl;)
		state_ = CLOSED;
		if (temporary) temporary = false, unlink();
		return 0;
	}
	char operator[](const size_t i) noexcept {
		return (static_cast<char*>(data_))[i];
	}
private:
	mmap_mode mode_;
	enum { CLOSED, UNMAPPED, MAPPED } state_;
	std::string filename_;
	size_t size_;
	int fd_ = -1;
	void* data_ = 0;
	bool temporary = false;
	int truncate() {
		if (state_==MAPPED) return err(L"cannot truncate mapped file");
		if (size_ && size_ != (size_t)file_size()) {
			//DBG(std::wcout<<L"memory_map: truncate "
			//	<<s2ws(std::string(filename_))
			//	<<L" to size: "<<size_<<L"\n";)
			if (::ftruncate(fd_, size_) == -1)
				return err(errno, L"error truncate failed");
		}
		return size_;
	}
	inline void seek_beginning() {
		FILE *file = fdopen(fd_, "w");
		fseek(file, 0, SEEK_SET);
	}
	inline int fill() {
		int w = ::write(fd_, std::string(size_, 0).c_str(), size_);
		if (w == -1) err(errno, L"memory_map: create (fill)");
		else seek_beginning();
		return w;
	}
	inline void create_temp() {
		temporary = true,
		fd_ = temp_fileno(),
		filename_ = filename(fd_);
	}
	void create() {
		if (filename_ == "") create_temp();
		else fd_ = ::open(filename_.c_str(), O_CREAT|O_RDWR, 0644);
    		if (fd_ == -1) { err(errno, L"memory_map: create"); return; }
		if (fill() == -1) return;
		DBG(std::wcout<<L"memory_map: create "
			<<s2ws(std::string(filename_))
			<<L" created with size: "<<size_<<L"\n";)
	}
	bool file_exists() {
 		struct stat s;
    		return filename_=="" ? false : stat(filename_.c_str(), &s) == 0;
	}
	off_t file_size() {
		struct stat s;
		bool stat_nok = ::stat(filename_.c_str(), &s) == -1;
		if (stat_nok) {
			// DBG(std::wcout<<L"stat nok "<<s2ws(std::string(filename_))<<std::endl;)
			err(errno, L"cannot get file stats");
			return 0;
		}
		//DBG(std::wcout<<L"stats size: "<<s.st_size<<std::endl;)
		return s.st_size;
	}
	int err(int err_code, std::wstring message, int return_value = -1) {
		return err(message, return_value, err_code);
	}
	int err(std::wstring message, int return_value = -1, int err_code = 0) {
		error = true; std::wstringstream ss; ss << L"error: ";
		if (err_code) ss << L'[' << err_code << L"] ";
		ss << message << std::endl; error_message = ss.str();
		if (!silent) o::err() << error_message;
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
	T* allocate(size_t n, const void *hint=0) {
		DBG(std::wcout<<L"allocate n= "<<n<<L" fn="
			<<s2ws(fn)<<L" m="<<m<<std::endl;)
		if (m == MMAP_NONE) return (T*) nommap.allocate(n, hint);
		if (n == 0) return 0;
		if (hint != 0) return 0;
		mm = std::make_unique<memory_map>(fn, n*sizeof(T), m);
		//std::wcout << L"mm.data() = " << mm->data() << std::endl;
		return (T*) mm->data();
	}
	void deallocate(T* p, size_t n) {
		DBG(std::wcout<<L"deallocate n= "<<n<<
			L" fn="<<s2ws(std::string(fn))<<L" m="<<m<<std::endl;)
		if (m == MMAP_NONE) return (void) nommap.deallocate(p, n);
		if (!p || !n) return;
		mm->close();
	}
private:
	std::string fn;
	mmap_mode m;
	std::unique_ptr<memory_map> mm;
	std::allocator<T> nommap;
};

#endif
