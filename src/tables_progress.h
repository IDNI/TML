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

#ifndef __TABLES_PROGRESS_H_
#define __TABLES_PROGRESS_H_

#include "defs.h"
#include "tables.h"

/*! This class monitors the progress of the execution of tables. Right now it is
 * a straightforward consumer as all the functions return void. In a more complex 
 * scenario they could return a boolean to point if the execution should continue
 * or a more complex object to fine tune the forthcoming execution. */
struct tables_progress : public progress {
public:
	tables_progress(dict_t &d, ir_builder &ir) : dict(d), ir_handler(ir) {};
	~tables_progress() override = default;
	void notify_update(tables &ts, spbdd_handle& x, const rule& r) override;

	//#ifdef BIT_TRANSFORM
	//void notify_decompress(table tbl, term r);
	//#endif

private:
	/* This objects are part of tables rightnow, the main task of this class
	 * is to remove them from tables. The label REMOVE_IR_BUILDER_FROM_TABLES
	 * control wheter this class is used or not. */
	dict_t dict;
	ir_builder ir_handler;

	void add_tml_update(tables &ts, const term& t, bool neg);
};

#endif // __TABLES_PROGRESS_H_