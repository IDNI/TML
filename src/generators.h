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

#ifndef __GENERATORS_H__
#define __GENERATORS_H__

#include <coroutine>
#include <exception>
#include <vector>
#include <algorithm>
#include <ranges>
#include <iostream>
 

template<typename T>
struct generator {
    // The class name 'Generator' is our choice and it is not required for coroutine magic.
    // Compiler recognizes coroutine by the presence of 'co_yield' keyword.
    // You can use name 'MyGenerator' (or any other name) instead as long as you include
    // nested struct promise_type with 'MyGenerator get_return_object()' method.
    // Note: You need to adjust class constructor/destructor names too when choosing to
    // rename class.
    //
    // Obtained from https://en.cppreference.com/w/cpp/language/coroutines
 
    struct promise_type;
    using handle_type = std::coroutine_handle<promise_type>;

    struct promise_type { // required
        T value_;
        std::exception_ptr exception_;

        generator get_return_object() {
            return generator(handle_type::from_promise(*this));
        }

        std::suspend_always initial_suspend() const { return {}; }
        std::suspend_always final_suspend() const noexcept { return {}; }
        void unhandled_exception() { exception_ = std::current_exception(); } // saving
                                                                            // exception

        template<std::convertible_to<T> From> // C++20 concept

        std::suspend_always yield_value(From &&from) {
            value_ = std::forward<From>(from); // caching the result in promise
            return {};
        }
        void return_void() const {}
    };
    
    handle_type h_;

    explicit generator(handle_type h) : h_(h) {}
    ~generator() { h_.destroy(); }

    explicit operator bool() {
        fill(); // The only way to reliably find out whether or not we finished coroutine,
        // whether or not there is going to be a next value generated (co_yield) in
        // coroutine via C++ getter (operator () below) is to execute/resume coroutine
        // until the next co_yield point (or let it fall off end).
        // Then we store/cache result in promise to allow getter (operator() below to
        // grab it without executing coroutine).
        return !h_.done();
    }

    T operator()() {
        fill();
        full_ = false; 
        // we are going to move out previously cached
        // result to make promise empty again
        return std::move(h_.promise().value_);
    }

private:
    bool full_ = false;

    void fill() {
        if (!full_) {
            h_();
            if (h_.promise().exception_)
                // propagate coroutine exception in called context
                std::rethrow_exception(h_.promise().exception_);
            full_ = true;
        }
    }
};

std::vector<size_t> monotone_perm(size_t n) {
    if (n <= 1) return std::vector<size_t> {0};
    auto x = monotone_perm(n - 1);
    x.emplace_back(n - 1);
    std::rotate(x.rbegin(), x.rend() + 1, x.rend());
    return x;
}

generator<std::vector<std::vector<size_t>>> p (size_t n, size_t l, bool r = false) {
    if (n == 1 || l == 0) {
        auto t = r 
            ? std::vector<std::vector<size_t>> {{1}, {0}}
            : std::vector<std::vector<size_t>> {{0}, {1}};
        co_yield t;
        co_return;
    }
    if (l >= n) co_return;
    // TODO simplify this code (ideally only a call to a function with the while)
    auto pi = monotone_perm(n - 1);
    if (!r) {
        auto ps1 = p(n - 1, l - 1, false);
        while (ps1) {
            auto x = ps1();
            std::vector<std::vector<size_t>> t{1};
            for (auto k: pi) {
                t.emplace_back(x[k]);
            }
            co_yield t;
        }
        auto ps0 = p(n - 1, l, false);
        while (ps0) {
            auto x = ps0();
            x.insert(x.begin(), std::vector<size_t> {1});
            co_yield x;
        }
    } else { /* r is true */
        auto ps0 = p(n - 1, l, true);
        while (ps0) {
            auto x = ps0();
            x.insert(x.begin(), std::vector<size_t> {0});
            co_yield x;
        }
        auto ps1 = p(n - 1, l - 1, true);
        while (ps1) {
            auto x = ps1();
            std::vector<std::vector<size_t>> t{1};
            for (auto k: pi) {
                t.emplace_back(x[k]);
            }
            co_yield t;
        }
    }
    co_return;
}

/*!
 * Monotone Gray Code generator following C.D. Savage & P. Winkler "Monotone Gray
 * Codes and Middle Levels Problem", J. of Combinatorial Theory, Series A 70,
 * pp. 230-248 (1995).
 *
 */
generator<std::vector<std::vector<size_t>>> 
monotone_gray_code_generator (size_t n) {
    for (size_t l = 0; l < n; ++l) {
        auto ps = p(n, l, l % 2 != 0);
        while (ps) {
            co_yield ps();
        }
    }
    co_return;
}

#endif // __GENERATORS_H__
