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

#ifndef __ASYNC_READER_H__
#define __ASYNC_READER_H__

#include <thread>
#include <queue>
#include <atomic>
#include <mutex>

template <typename T>
class async_reader {
public:
	async_reader() {
		eof = false;
		t = std::thread([&] { read_in_thread(); });
	}
	~async_reader() { t.detach(); }
	bool readable() {
		std::lock_guard<std::mutex> lk(m);
		return q.size();
	}
	T read() {
		std::lock_guard<std::mutex> lk(m);
		if (q.empty()) return {};
		auto l = std::move(q.front());
		q.pop();
		return l;
	}
	inline bool running() { return !eof || readable(); }
protected:
	std::atomic_bool eof;
	std::queue<T> q;
	std::thread t;
	std::mutex m;
	// threaded method enqueuing T-typed entities
	// typically: auto e = read(...); m.lock(); q.emplace(e); m.unlock();
	virtual void read_in_thread() = 0;
};

#endif
