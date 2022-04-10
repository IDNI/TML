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

std::vector<std::string> data_options_input = {
	"--no-info", "--no-debug", "--no-benchmarks",
	"--run", "false", "--transformed"
};
size_t data_options_expected_length = 376;
char data_options_expected[] =
"\x0d\x00\x00\x00\x00\x00\x00\x00" "\x01\x0c\x00\x00\x00\x00\x00\x00"
"\x00\x62\x64\x64\x2d\x6d\x61\x78" "\x2d\x73\x69\x7a\x65\x00\x00\x00"
"\x00\x08\x03\x0a\x00\x00\x00\x00" "\x00\x00\x00\x62\x65\x6e\x63\x68"
"\x6d\x61\x72\x6b\x73\x00\x05\x00" "\x00\x00\x00\x00\x00\x00\x40\x6e"
"\x75\x6c\x6c\x00\x03\x05\x00\x00" "\x00\x00\x00\x00\x00\x64\x65\x62"
"\x75\x67\x00\x05\x00\x00\x00\x00" "\x00\x00\x00\x40\x6e\x75\x6c\x6c"
"\x00\x03\x04\x00\x00\x00\x00\x00" "\x00\x00\x64\x75\x6d\x70\x00\x07"
"\x00\x00\x00\x00\x00\x00\x00\x40" "\x73\x74\x64\x6f\x75\x74\x00\x03"
"\x05\x00\x00\x00\x00\x00\x00\x00" "\x65\x72\x72\x6f\x72\x00\x07\x00"
"\x00\x00\x00\x00\x00\x00\x40\x73" "\x74\x64\x65\x72\x72\x00\x03\x04"
"\x00\x00\x00\x00\x00\x00\x00\x69" "\x6e\x66\x6f\x00\x05\x00\x00\x00"
"\x00\x00\x00\x00\x40\x6e\x75\x6c" "\x6c\x00\x02\x08\x00\x00\x00\x00"
"\x00\x00\x00\x6f\x70\x74\x69\x6d" "\x69\x7a\x65\x00\x01\x03\x06\x00"
"\x00\x00\x00\x00\x00\x00\x6f\x75" "\x74\x70\x75\x74\x00\x07\x00\x00"
"\x00\x00\x00\x00\x00\x40\x73\x74" "\x64\x6f\x75\x74\x00\x03\x0b\x00"
"\x00\x00\x00\x00\x00\x00\x72\x65" "\x70\x6c\x2d\x6f\x75\x74\x70\x75"
"\x74\x00\x07\x00\x00\x00\x00\x00" "\x00\x00\x40\x73\x74\x64\x6f\x75"
"\x74\x00\x02\x03\x00\x00\x00\x00" "\x00\x00\x00\x72\x75\x6e\x00\x00"
"\x03\x0b\x00\x00\x00\x00\x00\x00" "\x00\x74\x72\x61\x6e\x73\x66\x6f"
"\x72\x6d\x65\x64\x00\x00\x00\x00" "\x00\x00\x00\x00\x00\x00\x03\x08"
"\x00\x00\x00\x00\x00\x00\x00\x75" "\x64\x70\x2d\x61\x64\x64\x72\x00"
"\x09\x00\x00\x00\x00\x00\x00\x00" "\x31\x32\x37\x2e\x30\x2e\x30\x2e"
"\x31\x00\x01\x08\x00\x00\x00\x00" "\x00\x00\x00\x75\x64\x70\x2d\x70"
"\x6f\x72\x74\x00\x8b\x18\x00\x00";
std::string data_options_read_expected =
	"--bdd-max-size 134217728 "
	"--benchmarks \"@null\" "
	"--debug \"@null\" "
	"--dump \"@stdout\" "
	"--error \"@stderr\" "
	"--info \"@null\" "
	"--optimize  "
	"--output \"@stdout\" "
	"--repl-output \"@stdout\" "
	"--run false "
	"--transformed \"\" "
	"--udp-addr \"127.0.0.1\" "
	"--udp-port 6283";

size_t data_rules_expected_length = 34;
char data_rules_expected[] =
"\x0c\x00\x00\x00" "\x03" "\x01" "\x00\x00\x00\x00\x00\x00\x00\x00"
"\x01\x00\x00\x00" "\xff\xff\xff\xff" "\x00\x00\x00\x00"
"\x00\x00\x00\x00\x00\x00\x00\x00"
;

size_t data_dict_expected_length = 193;
char data_dict_expected[] = "\x29\x00\x00\x00\x00\x00\x00\x00"
	"\x72\x65\x6C\x31\x72\x65\x6C\x32\x73\x79\x6D\x62\x6F\x6C"
	"\x31\x73\x79\x6D\x62\x6F\x6C\x32\x73\x79\x6D\x62\x6F\x6C"
	"\x33\x62\x6C\x74\x69\x6E\x31\x62\x6C\x74\x69\x6E\x32"
	"\x02\x00\x00\x00\x00\x00\x00\x00"
	"\x03\x00\x00\x00\x00\x00\x00\x00"
	"\x02\x00\x00\x00\x00\x00\x00\x00"
	"\x00\x00\x00\x00\x00\x00\x00\x00"
	"\x04\x00\x00\x00\x00\x00\x00\x00"
	"\x04\x00\x00\x00\x00\x00\x00\x00"
	"\x08\x00\x00\x00\x00\x00\x00\x00"
	"\x08\x00\x00\x00\x00\x00\x00\x00"
	"\x0F\x00\x00\x00\x00\x00\x00\x00"
	"\x0F\x00\x00\x00\x00\x00\x00\x00"
	"\x16\x00\x00\x00\x00\x00\x00\x00"
	"\x16\x00\x00\x00\x00\x00\x00\x00"
	"\x1D\x00\x00\x00\x00\x00\x00\x00"
	"\x1D\x00\x00\x00\x00\x00\x00\x00"
	"\x23\x00\x00\x00\x00\x00\x00\x00"
	"\x23\x00\x00\x00\x00\x00\x00\x00"
	"\x29\x00\x00\x00\x00\x00\x00\x00"
	"\x00\x00\x00\x00\x00\x00\x00\x00";

size_t data_bdd_expected_length = 104;
char data_bdd_expected[] = 
"\x08\x00\x00\x00\x00\x00\x00\x00"
"\x00\x00\x00\x00""\x00\x00\x00\x00""\x00\x00\x00\x00"
"\x01\x00\x00\x00""\x01\x00\x00\x00""\x00\x00\x00\x00"
"\xff\xff\xff\xff""\x01\x00\x00\x00""\x04\x00\x00\x00"
"\xfe\xff\xff\xff""\x01\x00\x00\x00""\xfd\xff\xff\xff"
"\x03\x00\x00\x00""\x01\x00\x00\x00""\xfe\xff\xff\xff"
"\x04\x00\x00\x00""\x01\x00\x00\x00""\xff\xff\xff\xff"
"\x03\x00\x00\x00""\x01\x00\x00\x00""\x02\x00\x00\x00"
"\x06\x00\x00\x00""\x01\x00\x00\x00""\xff\xff\xff\xff";
std::vector<bdd> data_bdd_read_expected = {
	{  0,  0, 0 },
	{  0,  1, 1 },
	{  4, -1, 1 },
	{ -3, -2, 1 },
	{ -2,  3, 1 },
	{ -1,  4, 1 },
	{  2,  3, 1 },
	{ -1,  6, 1 }
};

size_t data_tables_expected_length = 317;
char data_tables_expected[] =
// rules
"\x01\x00\x00\x00\x00\x00\x00\x00"
"\x01\x00\x00\x00"                 // r.t
	"\x00" // r.t.extype
	"\x00" // bools{ r.t.neg, r.t.goal }
"\x01\x00\x00\x00\x00\x00\x00\x00" // r.t.size()
"\x04\x00\x00\x00" // r.t[0]
"\xfa\xff\xff\xff" "\xfa\xff\xff\xff" "\x00\x00\x00\x00"
"\x01\x00\x00\x00\x00\x00\x00\x00"
"\x01\x00\x00\x00"
"\x00\x00\x00\x00"
// 48
"\x00\x00\x00\x00\x00\x00\x00\x00"
"\x00\x00\x00\x00"
"\x02\x00\x00\x00\x00\x00\x00\x00" // nstep
"\x00\x00\x00\x00\x00\x00\x00\x00" // tmprels
"\x02\x00\x00\x00\x00\x00\x00\x00" // deps
	"\x00\x00\x00\x00" "\x00\x00\x00\x00\x00\x00\x00\x00"
	"\x01\x00\x00\x00" "\x00\x00\x00\x00\x00\x00\x00\x00"
"\x01\x00\x00\x00\x00\x00\x00\x00" // max_args
"\x00\x00\x00\x00\x00\x00\x00\x00" // rcm
"\x00\x00\x00\x00\x00\x00\x00\x00" // goals
"\x00\x00\x00\x00\x00\x00\x00\x00" // to_drop
"\x00\x00\x00\x00\x00\x00\x00\x00" // strs
"\x00\x00\x00\x00\x00\x00\x00\x00" // str_rels
"\x00\x00\x00\x00\x00\x00\x00\x00" // prog_after_fp
"\x00" // tbls bools

"\x02\x00\x00\x00\x00\x00\x00\x00" // tbls size

// tbl 1
"\x00\x00\x00\x00" // rel
"\x01\x00\x00\x00\x00\x00\x00\x00" "\x01\x00\x00\x00" // arity
"\xfe\xff\xff\xff" // t
"\x01\x00\x00\x00\x00\x00\x00\x00" //len
"\x00\x00\x00\x00\x00\x00\x00\x00" // priority
"\x00\x00\x00\x00\x00\x00\x00\x00" // r
"\x01" // tbl bools
"\xff\xff\xff\xff" // idbltin
"\x00\x00\x00\x00\x00\x00\x00\x00" // bltinargs
"\x00\x00\x00\x00\x00\x00\x00\x00" // btlinsize

// tbl 1
"\x01\x00\x00\x00" // rel
"\x01\x00\x00\x00\x00\x00\x00\x00" "\x01\x00\x00\x00" // arity
"\xfa\xff\xff\xff" // t
"\x01\x00\x00\x00\x00\x00\x00\x00" //len
"\x00\x00\x00\x00\x00\x00\x00\x00" // priority
"\x01\x00\x00\x00\x00\x00\x00\x00" // r
	"\x00\x00\x00\x00\x00\x00\x00\x00"
"\x00" // tbl bools
"\xff\xff\xff\xff" // idbltin
"\x00\x00\x00\x00\x00\x00\x00\x00" // bltinargs
"\x00\x00\x00\x00\x00\x00\x00\x00" // btlinsize
;

size_t data_driver_expected_length = 2618;
char data_driver_expected[] = 
"\xbd\xdd\x00\x00\x00\x00\x00\x00" "\x00\x00\x01\x00\x00\x00\x00\x00"
"\x00\x00\x00\x21\x00\x00\x00\x00" "\x00\x00\x00\x61\x28\x78\x29\x2e"
"\x20\x62\x28\x79\x29\x20\x3a\x2d" "\x20\x61\x28\x78\x29\x2e\x20\x63"
"\x28\x7a\x29\x20\x3a\x2d\x20\x62" "\x28\x79\x29\x2e\x00\x00\x00\x00"
"\x00\x03\x00\x00\x00\x00\x00\x00" "\x00\x03\x00\x00\x00\x00\x00\x00"
"\x00\x00\x00\x00\x00\x00\x00\x00" "\x00\x13\x00\x00\x00\x00\x00\x00"
"\x00\x11\x00\x00\x00\x00\x00\x00" "\x00\x00\x00\x00\x00\x00\x00\x00"
"\x00\x00\x00\x00\x00\x00\x00\x00" "\x00\x5e\x00\x00\x00\x00\x00\x00"
"\x00\x28\x29\x72\x6e\x64\x66\x61" "\x69\x6c\x68\x61\x6c\x74\x61\x6c"
"\x6e\x75\x6d\x61\x6c\x70\x68\x61" "\x62\x77\x5f\x6f\x72\x63\x6f\x75"
"\x6e\x74\x64\x69\x67\x69\x74\x70" "\x72\x69\x6e\x74\x73\x70\x61\x63"
"\x65\x62\x77\x5f\x61\x6e\x64\x62" "\x77\x5f\x6e\x6f\x74\x62\x77\x5f"
"\x78\x6f\x72\x6c\x70\x72\x69\x6e" "\x74\x70\x77\x5f\x61\x64\x64\x70"
"\x77\x5f\x6d\x75\x6c\x74\x70\x72" "\x69\x6e\x74\x61\x62\x6c\x65\x1f"
"\x00\x00\x00\x00\x00\x00\x00\x20" "\x00\x00\x00\x00\x00\x00\x00\x25"
"\x00\x00\x00\x00\x00\x00\x00\x26" "\x00\x00\x00\x00\x00\x00\x00\x33"
"\x00\x00\x00\x00\x00\x00\x00\x34" "\x00\x00\x00\x00\x00\x00\x00\x21"
"\x00\x00\x00\x00\x00\x00\x00\x22" "\x00\x00\x00\x00\x00\x00\x00\x27"
"\x00\x00\x00\x00\x00\x00\x00\x28" "\x00\x00\x00\x00\x00\x00\x00\x35"
"\x00\x00\x00\x00\x00\x00\x00\x36" "\x00\x00\x00\x00\x00\x00\x00\x60"
"\x01\x00\x00\x00\x00\x00\x00\x61" "\x01\x00\x00\x00\x00\x00\x00\x61"
"\x01\x00\x00\x00\x00\x00\x00\x62" "\x01\x00\x00\x00\x00\x00\x00\x62"
"\x01\x00\x00\x00\x00\x00\x00\x65" "\x01\x00\x00\x00\x00\x00\x00\x65"
"\x01\x00\x00\x00\x00\x00\x00\x69" "\x01\x00\x00\x00\x00\x00\x00\x69"
"\x01\x00\x00\x00\x00\x00\x00\x6d" "\x01\x00\x00\x00\x00\x00\x00\x6d"
"\x01\x00\x00\x00\x00\x00\x00\x72" "\x01\x00\x00\x00\x00\x00\x00\x72"
"\x01\x00\x00\x00\x00\x00\x00\x77" "\x01\x00\x00\x00\x00\x00\x00\x77"
"\x01\x00\x00\x00\x00\x00\x00\x7c" "\x01\x00\x00\x00\x00\x00\x00\x7c"
"\x01\x00\x00\x00\x00\x00\x00\x81" "\x01\x00\x00\x00\x00\x00\x00\x81"
"\x01\x00\x00\x00\x00\x00\x00\x86" "\x01\x00\x00\x00\x00\x00\x00\x86"
"\x01\x00\x00\x00\x00\x00\x00\x8b" "\x01\x00\x00\x00\x00\x00\x00\x8b"
"\x01\x00\x00\x00\x00\x00\x00\x90" "\x01\x00\x00\x00\x00\x00\x00\x90"
"\x01\x00\x00\x00\x00\x00\x00\x96" "\x01\x00\x00\x00\x00\x00\x00\x96"
"\x01\x00\x00\x00\x00\x00\x00\x9c" "\x01\x00\x00\x00\x00\x00\x00\x9c"
"\x01\x00\x00\x00\x00\x00\x00\xa2" "\x01\x00\x00\x00\x00\x00\x00\xa2"
"\x01\x00\x00\x00\x00\x00\x00\xa8" "\x01\x00\x00\x00\x00\x00\x00\xa8"
"\x01\x00\x00\x00\x00\x00\x00\xae" "\x01\x00\x00\x00\x00\x00\x00\xae"
"\x01\x00\x00\x00\x00\x00\x00\xb5" "\x01\x00\x00\x00\x00\x00\x00\xb5"
"\x01\x00\x00\x00\x00\x00\x00\xbe" "\x01\x00\x00\x00\x00\x00\x00\x62"
"\x01\x00\x00\x00\x00\x00\x00\x65" "\x01\x00\x00\x00\x00\x00\x00\x65"
"\x01\x00\x00\x00\x00\x00\x00\x69" "\x01\x00\x00\x00\x00\x00\x00\x69"
"\x01\x00\x00\x00\x00\x00\x00\x6d" "\x01\x00\x00\x00\x00\x00\x00\x6d"
"\x01\x00\x00\x00\x00\x00\x00\x72" "\x01\x00\x00\x00\x00\x00\x00\x72"
"\x01\x00\x00\x00\x00\x00\x00\x77" "\x01\x00\x00\x00\x00\x00\x00\x77"
"\x01\x00\x00\x00\x00\x00\x00\x7c" "\x01\x00\x00\x00\x00\x00\x00\x7c"
"\x01\x00\x00\x00\x00\x00\x00\x81" "\x01\x00\x00\x00\x00\x00\x00\x81"
"\x01\x00\x00\x00\x00\x00\x00\x86" "\x01\x00\x00\x00\x00\x00\x00\x86"
"\x01\x00\x00\x00\x00\x00\x00\x8b" "\x01\x00\x00\x00\x00\x00\x00\x8b"
"\x01\x00\x00\x00\x00\x00\x00\x90" "\x01\x00\x00\x00\x00\x00\x00\x90"
"\x01\x00\x00\x00\x00\x00\x00\x96" "\x01\x00\x00\x00\x00\x00\x00\x96"
"\x01\x00\x00\x00\x00\x00\x00\x9c" "\x01\x00\x00\x00\x00\x00\x00\x9c"
"\x01\x00\x00\x00\x00\x00\x00\xa2" "\x01\x00\x00\x00\x00\x00\x00\xa2"
"\x01\x00\x00\x00\x00\x00\x00\xa8" "\x01\x00\x00\x00\x00\x00\x00\xa8"
"\x01\x00\x00\x00\x00\x00\x00\xae" "\x01\x00\x00\x00\x00\x00\x00\xae"
"\x01\x00\x00\x00\x00\x00\x00\xb5" "\x01\x00\x00\x00\x00\x00\x00\xb5"
"\x01\x00\x00\x00\x00\x00\x00\xbe" "\x01\x00\x00\x00\x00\x00\x00\x09"
"\x00\x00\x00\x00\x00\x00\x00\x00" "\x00\x00\x00\x00\x00\x00\x00\x00"
"\x00\x00\x00\x01\x00\x00\x00\x01" "\x00\x00\x00\x00\x00\x00\x00\xff"
"\xff\xff\xff\x01\x00\x00\x00\x04" "\x00\x00\x00\xfe\xff\xff\xff\x01"
"\x00\x00\x00\xfd\xff\xff\xff\x03" "\x00\x00\x00\x01\x00\x00\x00\xfe"
"\xff\xff\xff\x04\x00\x00\x00\x01" "\x00\x00\x00\xff\xff\xff\xff\x03"
"\x00\x00\x00\x01\x00\x00\x00\x02" "\x00\x00\x00\x06\x00\x00\x00\x01"
"\x00\x00\x00\xff\xff\xff\xff\x04" "\x00\x00\x00\x01\x00\x00\x00\x01"
"\x00\x00\x00\x0d\x00\x00\x00\x00" "\x00\x00\x00\x01\x0c\x00\x00\x00"
"\x00\x00\x00\x00\x62\x64\x64\x2d" "\x6d\x61\x78\x2d\x73\x69\x7a\x65"
"\x00\x00\x00\x00\x08\x03\x0a\x00" "\x00\x00\x00\x00\x00\x00\x62\x65"
"\x6e\x63\x68\x6d\x61\x72\x6b\x73" "\x00\x05\x00\x00\x00\x00\x00\x00"
"\x00\x40\x6e\x75\x6c\x6c\x00\x03" "\x05\x00\x00\x00\x00\x00\x00\x00"
"\x64\x65\x62\x75\x67\x00\x12\x00" "\x00\x00\x00\x00\x00\x00\x61\x72"
"\x63\x68\x69\x76\x65\x2e\x74\x65" "\x73\x74\x2e\x64\x65\x62\x75\x67"
"\x00\x03\x04\x00\x00\x00\x00\x00" "\x00\x00\x64\x75\x6d\x70\x00\x07"
"\x00\x00\x00\x00\x00\x00\x00\x40" "\x73\x74\x64\x6f\x75\x74\x00\x03"
"\x05\x00\x00\x00\x00\x00\x00\x00" "\x65\x72\x72\x6f\x72\x00\x07\x00"
"\x00\x00\x00\x00\x00\x00\x40\x73" "\x74\x64\x65\x72\x72\x00\x03\x04"
"\x00\x00\x00\x00\x00\x00\x00\x69" "\x6e\x66\x6f\x00\x05\x00\x00\x00"
"\x00\x00\x00\x00\x40\x6e\x75\x6c" "\x6c\x00\x03\x0a\x00\x00\x00\x00"
"\x00\x00\x00\x69\x6e\x70\x75\x74" "\x2d\x65\x76\x61\x6c\x00\x21\x00"
"\x00\x00\x00\x00\x00\x00\x61\x28" "\x78\x29\x2e\x20\x62\x28\x79\x29"
"\x20\x3a\x2d\x20\x61\x28\x78\x29" "\x2e\x20\x63\x28\x7a\x29\x20\x3a"
"\x2d\x20\x62\x28\x79\x29\x2e\x00" "\x02\x08\x00\x00\x00\x00\x00\x00"
"\x00\x6f\x70\x74\x69\x6d\x69\x7a" "\x65\x00\x01\x03\x06\x00\x00\x00"
"\x00\x00\x00\x00\x6f\x75\x74\x70" "\x75\x74\x00\x07\x00\x00\x00\x00"
"\x00\x00\x00\x40\x73\x74\x64\x6f" "\x75\x74\x00\x03\x0b\x00\x00\x00"
"\x00\x00\x00\x00\x72\x65\x70\x6c" "\x2d\x6f\x75\x74\x70\x75\x74\x00"
"\x07\x00\x00\x00\x00\x00\x00\x00" "\x40\x73\x74\x64\x6f\x75\x74\x00"
"\x02\x03\x00\x00\x00\x00\x00\x00" "\x00\x72\x75\x6e\x00\x01\x03\x08"
"\x00\x00\x00\x00\x00\x00\x00\x75" "\x64\x70\x2d\x61\x64\x64\x72\x00"
"\x09\x00\x00\x00\x00\x00\x00\x00" "\x31\x32\x37\x2e\x30\x2e\x30\x2e"
"\x31\x00\x01\x08\x00\x00\x00\x00" "\x00\x00\x00\x75\x64\x70\x2d\x70"
"\x6f\x72\x74\x00\x8b\x18\x00\x00" "\x00\x00\x00\x00\x00\x00\x00\x00"
"\x00\x00\x00\x00\x00\x00\x00\x00" "\x00\x00\x00\x00\x00\x00\x00\x00"
"\x00\x00\x00\x00\x00\x00\x00\x00" "\x00\x00\x01\x00\x00\x00\x00\x00"
"\x00\x00\x00\x00\x00\x00\x00\x00" "\x00\x00\x00\x00\x00\x00\x00\x00"
"\x00\x00\x00\x00\x00\x00\x00\x00" "\x00\x00\x00\x00\x00\x00\x01\x00"
"\x00\x00\x00\x00\x00\x00\x00\x00" "\x00\x00\x00\x00\x00\x00\x00\x00"
"\x00\x00\x00\x00\x00\x00\x03\x00" "\x00\x00\x00\x00\x00\x00\x00\x01"
"\x00\x00\x00\x00\x00\x00\x00\x00" "\x00\x04\x00\x00\x00\x00\x00\x00"
"\x00\x01\x1f\x00\x00\x00\x00\x00" "\x00\x00\x20\x00\x00\x00\x00\x00"
"\x00\x00\x05\x01\x21\x00\x00\x00" "\x00\x00\x00\x00\x22\x00\x00\x00"
"\x00\x00\x00\x00\x06\x01\x00\x00" "\x00\x00\x00\x00\x00\x01\x00\x00"
"\x00\x00\x00\x00\x00\x00\x00\x00" "\x00\x00\x01\x00\x00\x00\x00\x00"
"\x00\x00\x00\x00\x04\x00\x00\x00" "\x00\x00\x00\x00\x01\x25\x00\x00"
"\x00\x00\x00\x00\x00\x26\x00\x00" "\x00\x00\x00\x00\x00\x05\x01\x27"
"\x00\x00\x00\x00\x00\x00\x00\x28" "\x00\x00\x00\x00\x00\x00\x00\x06"
"\x01\x00\x00\x00\x00\x00\x00\x00" "\x01\x00\x00\x00\x01\x00\x00\x00"
"\x00\x00\x00\x00\x01\x00\x00\x00" "\x00\x00\x00\x00\x00\x00\x04\x00"
"\x00\x00\x00\x00\x00\x00\x01\x1f" "\x00\x00\x00\x00\x00\x00\x00\x20"
"\x00\x00\x00\x00\x00\x00\x00\x05" "\x01\x21\x00\x00\x00\x00\x00\x00"
"\x00\x22\x00\x00\x00\x00\x00\x00" "\x00\x06\x01\x00\x00\x00\x00\x00"
"\x00\x00\x01\x00\x00\x00\x00\x01" "\x00\x00\x00\x00\x00\x00\x00\x00"
"\x00\x04\x00\x00\x00\x00\x00\x00" "\x00\x01\x33\x00\x00\x00\x00\x00"
"\x00\x00\x34\x00\x00\x00\x00\x00" "\x00\x00\x05\x01\x35\x00\x00\x00"
"\x00\x00\x00\x00\x36\x00\x00\x00" "\x00\x00\x00\x00\x06\x01\x00\x00"
"\x00\x00\x00\x00\x00\x01\x00\x00" "\x00\x01\x00\x00\x00\x00\x00\x00"
"\x00\x01\x00\x00\x00\x00\x00\x00" "\x00\x00\x00\x04\x00\x00\x00\x00"
"\x00\x00\x00\x01\x25\x00\x00\x00" "\x00\x00\x00\x00\x26\x00\x00\x00"
"\x00\x00\x00\x00\x05\x01\x27\x00" "\x00\x00\x00\x00\x00\x00\x28\x00"
"\x00\x00\x00\x00\x00\x00\x06\x01" "\x00\x00\x00\x00\x00\x00\x00\x01"
"\x00\x00\x00\x11\x00\x00\x00\x00" "\x00\x00\x00\x83\x00\x00\x00\x00"
"\x00\x00\x00\x86\x00\x00\x00\x00" "\x00\x00\x00\x86\x00\x00\x00\x00"
"\x00\x00\x00\x8a\x00\x00\x00\x00" "\x00\x00\x00\x8a\x00\x00\x00\x00"
"\x00\x00\x00\x8e\x00\x00\x00\x00" "\x00\x00\x00\x8e\x00\x00\x00\x00"
"\x00\x00\x00\x93\x00\x00\x00\x00" "\x00\x00\x00\x93\x00\x00\x00\x00"
"\x00\x00\x00\x98\x00\x00\x00\x00" "\x00\x00\x00\x98\x00\x00\x00\x00"
"\x00\x00\x00\x9d\x00\x00\x00\x00" "\x00\x00\x00\x9d\x00\x00\x00\x00"
"\x00\x00\x00\xa2\x00\x00\x00\x00" "\x00\x00\x00\xa2\x00\x00\x00\x00"
"\x00\x00\x00\xa7\x00\x00\x00\x00" "\x00\x00\x00\xa7\x00\x00\x00\x00"
"\x00\x00\x00\xac\x00\x00\x00\x00" "\x00\x00\x00\xac\x00\x00\x00\x00"
"\x00\x00\x00\xb1\x00\x00\x00\x00" "\x00\x00\x00\xb1\x00\x00\x00\x00"
"\x00\x00\x00\xb7\x00\x00\x00\x00" "\x00\x00\x00\xb7\x00\x00\x00\x00"
"\x00\x00\x00\xbd\x00\x00\x00\x00" "\x00\x00\x00\xbd\x00\x00\x00\x00"
"\x00\x00\x00\xc3\x00\x00\x00\x00" "\x00\x00\x00\xc3\x00\x00\x00\x00"
"\x00\x00\x00\xc9\x00\x00\x00\x00" "\x00\x00\x00\xc9\x00\x00\x00\x00"
"\x00\x00\x00\xcf\x00\x00\x00\x00" "\x00\x00\x00\xcf\x00\x00\x00\x00"
"\x00\x00\x00\xd6\x00\x00\x00\x00" "\x00\x00\x00\xd6\x00\x00\x00\x00"
"\x00\x00\x00\xdf\x00\x00\x00\x00" "\x00\x00\x00\x03\x02\x00\x00\x00"
"\x00\x00\x00\x00\x01\x00\x00\x00" "\x00\x00\x01\x00\x00\x00\x00\x00"
"\x00\x00\x04\x00\x00\x00\xf9\xff" "\xff\xff\xf9\xff\xff\xff\x00\x00"
"\x00\x00\x01\x00\x00\x00\x00\x00" "\x00\x00\x01\x00\x00\x00\x02\x00"
"\x00\x00\x00\x00\x01\x00\x00\x00" "\x00\x00\x00\x00\x08\x00\x00\x00"
"\xf8\xff\xff\xff\xff\xff\xff\xff" "\x00\x00\x00\x00\x01\x00\x00\x00"
"\x00\x00\x00\x00\xff\xff\xff\xff" "\x00\x00\x00\x00\x00\x00\x00\x00"
"\x00\x00\x00\x00\x00\x00\x00\x00" "\x01\x00\x00\x00\x00\x00\x00\x00"
"\x00\x00\x00\x00\x00\x00\x00\x00" "\x03\x00\x00\x00\x00\x00\x00\x00"
"\x00\x00\x00\x00\x00\x00\x00\x00" "\x00\x00\x00\x00\x01\x00\x00\x00"
"\x00\x00\x00\x00\x00\x00\x00\x00" "\x02\x00\x00\x00\x00\x00\x00\x00"
"\x00\x00\x00\x00\x01\x00\x00\x00" "\x00\x00\x00\x00\x00\x00\x00\x00"
"\x00\x00\x00\x00\x00\x00\x00\x00" "\x00\x00\x00\x00\x00\x00\x00\x00"
"\x00\x00\x00\x00\x00\x00\x00\x00" "\x00\x00\x00\x00\x00\x00\x00\x00"
"\x00\x00\x00\x00\x00\x00\x00\x00" "\x00\x00\x00\x00\x00\x03\x00\x00"
"\x00\x00\x00\x00\x00\x00\x00\x00" "\x00\x01\x00\x00\x00\x00\x00\x00"
"\x00\x01\x00\x00\x00\xfb\xff\xff" "\xff\x01\x00\x00\x00\x00\x00\x00"
"\x00\x00\x00\x00\x00\x00\x00\x00" "\x00\x00\x00\x00\x00\x00\x00\x00"
"\x00\x01\xff\xff\xff\xff\x00\x00" "\x00\x00\x00\x00\x00\x00\x00\x00"
"\x00\x00\x00\x00\x00\x00\x01\x00" "\x00\x00\x01\x00\x00\x00\x00\x00"
"\x00\x00\x01\x00\x00\x00\xf9\xff" "\xff\xff\x01\x00\x00\x00\x00\x00"
"\x00\x00\x00\x00\x00\x00\x00\x00" "\x00\x00\x01\x00\x00\x00\x00\x00"
"\x00\x00\x00\x00\x00\x00\x00\x00" "\x00\x00\x00\xff\xff\xff\xff\x00"
"\x00\x00\x00\x00\x00\x00\x00\x00" "\x00\x00\x00\x00\x00\x00\x00\x02"
"\x00\x00\x00\x01\x00\x00\x00\x00" "\x00\x00\x00\x01\x00\x00\x00\xff"
"\xff\xff\xff\x01\x00\x00\x00\x00" "\x00\x00\x00\x00\x00\x00\x00\x00"
"\x00\x00\x00\x01\x00\x00\x00\x00" "\x00\x00\x00\x01\x00\x00\x00\x00"
"\x00\x00\x00\x00\xff\xff\xff\xff" "\x00\x00\x00\x00\x00\x00\x00\x00"
"\x00\x00\x00\x00\x00\x00\x00\x00" "\x62\x83";