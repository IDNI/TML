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

#include <sys/socket.h>
#include <arpa/inet.h>
#include <netinet/in.h>
#include <unistd.h>
#include <string.h>
#include <fcntl.h>

#include <iostream>
#include <deque>
#include <string>
#include <sstream>
#include <memory>
#include <mutex>

#include "async_reader.h"

#define BUFLEN 4096

typedef std::shared_ptr<struct sockaddr> sp_sockaddr;
typedef std::pair<sp_sockaddr, std::string> udp_message;

class udp : public async_reader<udp_message> {
	std::string addr;
	uint16_t port;
	sa_family_t family;
	// size_t buflen = BUFLEN;
	bool closed=true;
	bool error_=false;
	std::wstring error_message_;
	int s, b;
	bool create_socket() {
		s = socket(family, SOCK_DGRAM, IPPROTO_UDP);
		if (s == -1) {
			error_ = true;
			error_message_ = L"socket_error";
			return false;
		}
		fcntl(s, F_SETFL, fcntl(s, F_GETFL, 0) | O_NONBLOCK);
		return true;
	}

	bool bind_socket() {
		struct sockaddr_in sin;
		memset((char *) &sin, 0, sizeof(sin));
		sin.sin_family = family;
		sin.sin_port = htons(port);
		sin.sin_addr.s_addr = inet_addr(addr.c_str());

		b = bind(s, (struct sockaddr*) &sin, sizeof(sin));
		if (b == -1) {
			error_ = true;
			error_message_ = L"bind error";
			return false;
		}
		closed = false;
		return true;
	}
	void sleep() {
		m.unlock();
		std::this_thread::sleep_for(std::chrono::milliseconds(50));
	}
public:
	udp(const std::string& addr, uint16_t port,
		sa_family_t family = AF_INET)
	:
		async_reader(), addr(addr), port(port), family(family)
	{
		// std::lock_guard<std::mutex> lk(m);
		if (!create_socket()) return;
		if (!bind_socket())   return;
		// std::wcout<<L"socket bound"<<std::endl;
	}
	bool send(udp_message m) {
		return send(m.second, m.first.get());
	}
	bool send(std::string msg, struct sockaddr * to) {
		ssize_t sent_len = sendto(s, msg.c_str(), msg.size(), 0,
					to, sizeof(struct sockaddr));
		if (sent_len == -1) return false;
		// std::lock_guard<std::mutex> lk(m);
		// std::wcout << L"sent: " << sent_len << L" bytes to: " <<
		// 	inet_ntoa(((struct sockaddr_in *)&to)->sin_addr) << L':' <<
		// 	ntohs(((struct sockaddr_in *)&to)->sin_port) << std::endl;
		return true;
	}
	void close() { if (!closed) ::close(s), eof = closed = true; }
	bool error() { return error_; }
	std::wstring error_message() { return error_message_; }
	~udp() { close(); }
private:
	socklen_t clen = sizeof(struct sockaddr *);
protected:
	void read_in_thread() {
		sp_sockaddr client;
		ssize_t recv_len;
		char buf[BUFLEN+1];
		buf[BUFLEN] = '\0';
		for(;;) {
			if (closed) goto skip;
			client = std::make_shared<struct sockaddr>();
			recv_len = recvfrom(s, buf, BUFLEN, 0, client.get(),
									&clen);
			if (recv_len == -1) goto skip;
			// m.lock(); std::wcout << L"received: " << recv_len << L" bytes from: " <<
			// 	inet_ntoa(((struct sockaddr_in *)&client)->sin_addr) << L':' <<
			// 	ntohs(((struct sockaddr_in *)&client)->sin_port) << std::endl;
			if (recv_len > 0) {
				m.lock();
				q.emplace(std::move(client),
						std::string(buf, recv_len));
			}
skip:
			sleep();
		}
	}
};
