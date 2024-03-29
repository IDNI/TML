elem e0(elem::SYM, t_arith_op::NOP, dict.get_lexeme("eol"));
elem e1(char32_t(13));
elem e2(elem::ALT, t_arith_op::NOP, dict.get_lexeme("|"));
elem e3(char32_t(10));
elem e4(elem::SYM, t_arith_op::NOP, dict.get_lexeme("eof"));
production gp5{{e0, e1, e2, e3, e2, e4, }, {}, };
elem e6(elem::SYM, t_arith_op::NOP, dict.get_lexeme("ws_comment"));
elem e7(char32_t(35));
elem e8(elem::SYM, t_arith_op::NOP, dict.get_lexeme("printable_chars"));
production gp9{{e6, e7, e0, e2, e7, e8, e0, }, {}, };
elem e10(elem::SYM, t_arith_op::NOP, dict.get_lexeme("ws_required"));
elem e11(elem::SYM, t_arith_op::NOP, dict.get_lexeme("space"));
elem e12(elem::SYM, t_arith_op::NOP, dict.get_lexeme("ws"));
production gp13{{e10, e11, e12, e2, e6, e12, }, {}, };
elem e14(elem::SYM, t_arith_op::NOP, dict.get_lexeme("null"));
production gp15{{e12, e10, e2, e14, }, {}, };
elem e16(elem::SYM, t_arith_op::NOP, dict.get_lexeme("hex_digit"));
elem e17(elem::SYM, t_arith_op::NOP, dict.get_lexeme("digit"));
elem e18(char32_t(65));
elem e19(char32_t(66));
elem e20(char32_t(67));
elem e21(char32_t(68));
elem e22(char32_t(69));
elem e23(char32_t(70));
elem e24(char32_t(97));
elem e25(char32_t(98));
elem e26(char32_t(99));
elem e27(char32_t(100));
elem e28(char32_t(101));
elem e29(char32_t(102));
production gp30{{e16, e17, e2, e18, e2, e19, e2, e20, e2, e21, e2, e22, e2, e23, e2, e24, e2, e25, e2, e26, e2, e27, e2, e28, e2, e29, }, {}, };
elem e31(elem::SYM, t_arith_op::NOP, dict.get_lexeme("hex_escape"));
elem e32(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"\\\\x\""));
production gp33{{e31, e32, e16, e16, }, {}, };
elem e34(elem::SYM, t_arith_op::NOP, dict.get_lexeme("unicode_escape"));
elem e35(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"\\\\u\""));
production gp36{{e34, e35, e16, e16, e16, e16, }, {}, };
elem e37(elem::SYM, t_arith_op::NOP, dict.get_lexeme("char_escape_encode"));
production gp38{{e37, e31, e2, e34, }, {}, };
elem e39(elem::SYM, t_arith_op::NOP, dict.get_lexeme("char0"));
elem e40(elem::SYM, t_arith_op::NOP, dict.get_lexeme("alnum"));
elem e41(char32_t(33));
elem e42(char32_t(36));
elem e43(char32_t(37));
elem e44(char32_t(38));
elem e45(char32_t(40));
elem e46(char32_t(41));
elem e47(char32_t(42));
elem e48(char32_t(43));
elem e49(char32_t(44));
elem e50(char32_t(45));
elem e51(char32_t(46));
elem e52(char32_t(47));
elem e53(char32_t(58));
elem e54(char32_t(59));
elem e55(char32_t(60));
elem e56(char32_t(61));
elem e57(char32_t(62));
elem e58(char32_t(63));
elem e59(char32_t(64));
elem e60(char32_t(91));
elem e61(char32_t(92));
elem e62(char32_t(93));
elem e63(char32_t(94));
elem e64(char32_t(95));
elem e65(char32_t(123));
elem e66(char32_t(124));
elem e67(char32_t(125));
elem e68(char32_t(126));
production gp69{{e39, e40, e2, e11, e2, e37, e2, e41, e2, e7, e2, e42, e2, e43, e2, e44, e2, e45, e2, e46, e2, e47, e2, e48, e2, e49, e2, e50, e2, e51, e2, e52, e2, e53, e2, e54, e2, e55, e2, e56, e2, e57, e2, e58, e2, e59, e2, e60, e2, e61, e2, e62, e2, e63, e2, e64, e2, e65, e2, e66, e2, e67, e2, e68, }, {}, };
elem e70(elem::SYM, t_arith_op::NOP, dict.get_lexeme("char"));
elem e71(char32_t(39));
elem e72(char32_t(34));
elem e73(char32_t(96));
production gp74{{e70, e39, e2, e61, e71, e2, e72, e2, e73, }, {}, };
elem e75(elem::SYM, t_arith_op::NOP, dict.get_lexeme("string_char"));
production gp76{{e75, e39, e2, e71, e2, e61, e72, e2, e73, }, {}, };
elem e77(elem::SYM, t_arith_op::NOP, dict.get_lexeme("quote_string_char"));
production gp78{{e77, e39, e2, e71, e2, e72, e2, e61, e73, }, {}, };
elem e79(elem::SYM, t_arith_op::NOP, dict.get_lexeme("string_chars"));
elem e80(elem::SYM, t_arith_op::NOP, dict.get_lexeme("string_chars1"));
production gp81{{e79, e75, e80, }, {}, };
production gp82{{e80, e75, e80, e2, e14, }, {}, };
elem e83(elem::SYM, t_arith_op::NOP, dict.get_lexeme("quote_string_chars"));
elem e84(elem::SYM, t_arith_op::NOP, dict.get_lexeme("quote_string_chars1"));
production gp85{{e83, e77, e84, }, {}, };
production gp86{{e84, e77, e84, e2, e14, }, {}, };
elem e87(elem::SYM, t_arith_op::NOP, dict.get_lexeme("printable"));
elem e88(elem::SYM, t_arith_op::NOP, dict.get_lexeme("printable_chars_rest"));
production gp89{{e8, e87, e88, }, {}, };
production gp90{{e88, e87, e88, e2, e14, }, {}, };
elem e91(elem::SYM, t_arith_op::NOP, dict.get_lexeme("chars"));
elem e92(elem::SYM, t_arith_op::NOP, dict.get_lexeme("alpha"));
elem e93(elem::SYM, t_arith_op::NOP, dict.get_lexeme("chars1"));
production gp94{{e91, e92, e93, e2, e64, e93, }, {}, };
production gp95{{e93, e40, e93, e2, e64, e93, e2, e14, }, {}, };
elem e96(elem::SYM, t_arith_op::NOP, dict.get_lexeme("integer"));
elem e97(elem::ARITH, t_arith_op::ADD, dict.get_lexeme("+"));
production gp98{{e96, e17, e97, }, {}, };
elem e99(elem::SYM, t_arith_op::NOP, dict.get_lexeme("sym"));
production gp100{{e99, e91, }, {}, };
elem e101(elem::SYM, t_arith_op::NOP, dict.get_lexeme("var"));
production gp102{{e101, e58, e91, }, {}, };
elem e103(elem::SYM, t_arith_op::NOP, dict.get_lexeme("number"));
production gp104{{e103, e96, }, {}, };
elem e105(elem::SYM, t_arith_op::NOP, dict.get_lexeme("quoted_char"));
elem e106(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"'\""));
elem e107(elem::SYM, t_arith_op::NOP, dict.get_lexeme("quoted_char_esc"));
elem e108(elem::SYM, t_arith_op::NOP, dict.get_lexeme("empty_char"));
production gp109{{e105, e106, e70, e106, e2, e106, e37, e106, e2, e107, e2, e108, }, {}, };
elem e110(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"''\""));
production gp111{{e108, e110, }, {}, };
elem e112(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"'\\\\\""));
production gp113{{e107, e112, e87, e106, }, {}, };
elem e114(elem::SYM, t_arith_op::NOP, dict.get_lexeme("string"));
elem e115(elem::SYM, t_arith_op::NOP, dict.get_lexeme("empty_string"));
production gp116{{e114, e72, e79, e72, e2, e115, }, {}, };
production gp117{{e115, e72, e72, }, {}, };
elem e118(elem::SYM, t_arith_op::NOP, dict.get_lexeme("quote_string"));
elem e119(elem::SYM, t_arith_op::NOP, dict.get_lexeme("empty_quote_string"));
production gp120{{e118, e73, e83, e73, e2, e119, }, {}, };
production gp121{{e119, e73, e73, }, {}, };
elem e122(elem::SYM, t_arith_op::NOP, dict.get_lexeme("term"));
elem e123(elem::SYM, t_arith_op::NOP, dict.get_lexeme("negative_term"));
elem e124(elem::SYM, t_arith_op::NOP, dict.get_lexeme("positive_term"));
production gp125{{e122, e123, e2, e124, }, {}, };
production gp126{{e123, e68, e12, e124, }, {}, };
elem e127(elem::SYM, t_arith_op::NOP, dict.get_lexeme("relname"));
elem e128(elem::SYM, t_arith_op::NOP, dict.get_lexeme("args"));
production gp129{{e124, e127, e128, e2, e127, }, {}, };
elem e130(elem::SYM, t_arith_op::NOP, dict.get_lexeme("elems"));
production gp131{{e128, e12, e45, e12, e130, e12, e46, e2, e12, e45, e12, e46, }, {}, };
elem e132(elem::SYM, t_arith_op::NOP, dict.get_lexeme("elem"));
elem e133(elem::SYM, t_arith_op::NOP, dict.get_lexeme("elems_rest"));
production gp134{{e130, e132, e2, e132, e10, e133, e2, e127, e128, e2, e127, e128, e12, e133, }, {}, };
production gp135{{e133, e132, e2, e132, e128, e2, e132, e10, e133, e2, e128, }, {}, };
elem e136(elem::SYM, t_arith_op::NOP, dict.get_lexeme("char_builtin"));
production gp137{{e132, e99, e2, e101, e2, e103, e2, e105, e2, e114, e2, e136, }, {}, };
production gp138{{e127, e99, }, {}, };
elem e139(elem::SYM, t_arith_op::NOP, dict.get_lexeme("builtin_expr"));
elem e140(elem::SYM, t_arith_op::NOP, dict.get_lexeme("builtin_term"));
elem e141(elem::SYM, t_arith_op::NOP, dict.get_lexeme("builtin_prefixes"));
production gp142{{e139, e140, e2, e141, e12, e140, }, {}, };
elem e143(elem::SYM, t_arith_op::NOP, dict.get_lexeme("builtin_prefix"));
production gp144{{e141, e143, e2, e143, e12, e141, }, {}, };
elem e145(elem::SYM, t_arith_op::NOP, dict.get_lexeme("renew_prefix"));
elem e146(elem::SYM, t_arith_op::NOP, dict.get_lexeme("forget_prefix"));
production gp147{{e143, e145, e2, e146, }, {}, };
elem e148(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"renew\""));
production gp149{{e145, e148, }, {}, };
elem e150(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"forget\""));
production gp151{{e146, e150, }, {}, };
elem e152(elem::SYM, t_arith_op::NOP, dict.get_lexeme("builtin"));
production gp153{{e140, e152, e128, e2, e152, }, {}, };
elem e154(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"halt\""));
elem e155(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"error\""));
elem e156(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"false\""));
elem e157(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"rnd\""));
elem e158(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"count\""));
elem e159(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"bw_and\""));
elem e160(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"bw_or\""));
elem e161(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"bw_xor\""));
elem e162(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"bw_not\""));
elem e163(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"pw_add\""));
elem e164(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"pw_mult\""));
elem e165(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"leq\""));
elem e166(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"print\""));
elem e167(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"println\""));
elem e168(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"println_to\""));
elem e169(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"print_to\""));
elem e170(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"print_delim\""));
elem e171(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"println_delim\""));
elem e172(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"print_to_delim\""));
elem e173(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"println_to_delim\""));
elem e174(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"js_eval\""));
production gp175{{e152, e154, e2, e155, e2, e156, e2, e150, e2, e157, e2, e158, e2, e159, e2, e160, e2, e161, e2, e162, e2, e163, e2, e164, e2, e165, e2, e166, e2, e167, e2, e168, e2, e169, e2, e170, e2, e171, e2, e172, e2, e173, e2, e174, }, {}, };
elem e176(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"alpha\""));
elem e177(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"alnum\""));
elem e178(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"digit\""));
elem e179(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"space\""));
elem e180(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"printable\""));
elem e181(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"eof\""));
production gp182{{e136, e176, e2, e177, e2, e178, e2, e179, e2, e180, e2, e181, }, {}, };
elem e183(elem::SYM, t_arith_op::NOP, dict.get_lexeme("arith_expr"));
elem e184(elem::SYM, t_arith_op::NOP, dict.get_lexeme("arith_op_expr"));
elem e185(elem::SYM, t_arith_op::NOP, dict.get_lexeme("arith_waux_expr"));
production gp186{{e183, e184, e2, e185, }, {}, };
elem e187(elem::SYM, t_arith_op::NOP, dict.get_lexeme("arith_op"));
production gp188{{e184, e132, e12, e187, e12, e132, }, {}, };
elem e189(elem::SYM, t_arith_op::NOP, dict.get_lexeme("arith_aux_op"));
production gp190{{e185, e132, e12, e189, e12, e132, e12, e187, e12, e132, }, {}, };
production gp191{{e185, e132, e12, e189, e12, e132, e12, e187, e12, e132, e12, e132, }, {}, };
elem e192(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"==\""));
elem e193(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"!=\""));
elem e194(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"<=\""));
elem e195(elem::STR, t_arith_op::NOP, dict.get_lexeme("\">=\""));
production gp196{{e187, e56, e2, e192, e2, e193, e2, e194, e2, e195, e2, e57, e2, e55, }, {}, };
elem e197(elem::STR, t_arith_op::NOP, dict.get_lexeme("\">>\""));
elem e198(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"<<\""));
production gp199{{e189, e48, e2, e50, e2, e47, e2, e66, e2, e44, e2, e63, e2, e197, e2, e198, }, {}, };
elem e200(elem::SYM, t_arith_op::NOP, dict.get_lexeme("rule"));
elem e201(elem::SYM, t_arith_op::NOP, dict.get_lexeme("preds"));
elem e202(elem::STR, t_arith_op::NOP, dict.get_lexeme("\":-\""));
production gp203{{e200, e201, e12, e202, e12, e201, e12, e51, }, {}, };
elem e204(elem::SYM, t_arith_op::NOP, dict.get_lexeme("fact"));
elem e205(elem::SYM, t_arith_op::NOP, dict.get_lexeme("pred"));
production gp206{{e204, e205, e12, e51, }, {}, };
elem e207(elem::SYM, t_arith_op::NOP, dict.get_lexeme("preds_rest"));
production gp208{{e201, e205, e207, }, {}, };
production gp209{{e207, e49, e12, e205, e207, e2, e14, }, {}, };
production gp210{{e205, e139, e2, e183, e2, e122, }, {}, };
elem e211(elem::SYM, t_arith_op::NOP, dict.get_lexeme("block"));
elem e212(elem::SYM, t_arith_op::NOP, dict.get_lexeme("prog"));
production gp213{{e211, e65, e212, e12, e67, }, {}, };
elem e214(elem::SYM, t_arith_op::NOP, dict.get_lexeme("query"));
elem e215(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"!!\""));
production gp216{{e214, e41, e12, e122, e12, e51, e2, e215, e12, e122, e12, e51, }, {}, };
elem e217(elem::SYM, t_arith_op::NOP, dict.get_lexeme("macro"));
elem e218(elem::STR, t_arith_op::NOP, dict.get_lexeme("\":=\""));
production gp219{{e217, e124, e12, e218, e12, e201, e12, e51, }, {}, };
elem e220(elem::SYM, t_arith_op::NOP, dict.get_lexeme("production"));
elem e221(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"=>\""));
elem e222(elem::SYM, t_arith_op::NOP, dict.get_lexeme("alts"));
elem e223(elem::SYM, t_arith_op::NOP, dict.get_lexeme("constraints"));
production gp224{{e220, e127, e12, e221, e12, e222, e223, e12, e51, }, {}, };
elem e225(elem::SYM, t_arith_op::NOP, dict.get_lexeme("alt"));
elem e226(elem::SYM, t_arith_op::NOP, dict.get_lexeme("alts_rest"));
production gp227{{e222, e225, e226, }, {}, };
elem e228(elem::SYM, t_arith_op::NOP, dict.get_lexeme("alt_separator"));
production gp229{{e226, e12, e228, e12, e225, e226, e2, e14, }, {}, };
production gp230{{e228, e66, }, {}, };
elem e231(elem::SYM, t_arith_op::NOP, dict.get_lexeme("nt_nt_alt"));
elem e232(elem::SYM, t_arith_op::NOP, dict.get_lexeme("nt_t_alt"));
elem e233(elem::SYM, t_arith_op::NOP, dict.get_lexeme("t_nt_alt"));
elem e234(elem::SYM, t_arith_op::NOP, dict.get_lexeme("t_t_alt"));
production gp235{{e225, e231, e2, e232, e2, e233, e2, e234, }, {}, };
elem e236(elem::SYM, t_arith_op::NOP, dict.get_lexeme("t_t_factor"));
production gp237{{e234, e236, e2, e236, e12, e234, e2, e236, e12, e232, }, {}, };
production gp238{{e233, e236, e12, e233, e2, e236, e12, e231, }, {}, };
elem e239(elem::SYM, t_arith_op::NOP, dict.get_lexeme("nt_t_factor"));
elem e240(elem::SYM, t_arith_op::NOP, dict.get_lexeme("nt_nt_factor"));
production gp241{{e232, e239, e2, e240, e10, e232, e2, e240, e12, e234, e2, e239, e12, e232, e2, e239, e12, e234, }, {}, };
production gp242{{e231, e240, e2, e240, e10, e231, e2, e240, e12, e233, e2, e239, e12, e231, e2, e239, e12, e233, }, {}, };
elem e243(elem::SYM, t_arith_op::NOP, dict.get_lexeme("terminal"));
elem e244(elem::SYM, t_arith_op::NOP, dict.get_lexeme("unot"));
production gp245{{e236, e243, e2, e243, e12, e244, e2, e45, e12, e225, e12, e46, e2, e45, e12, e225, e12, e46, e12, e244, e2, e65, e12, e225, e12, e67, e2, e60, e12, e225, e12, e62, }, {}, };
elem e246(elem::SYM, t_arith_op::NOP, dict.get_lexeme("nonterminal"));
production gp247{{e239, e246, e12, e244, }, {}, };
production gp248{{e240, e246, }, {}, };
production gp249{{e244, e47, e2, e48, }, {}, };
production gp250{{e243, e105, e2, e114, }, {}, };
production gp251{{e246, e127, }, {}, };
elem e252(elem::SYM, t_arith_op::NOP, dict.get_lexeme("constraint"));
production gp253{{e223, e12, e49, e12, e252, e223, e2, e14, }, {}, };
elem e254(elem::SYM, t_arith_op::NOP, dict.get_lexeme("constraint_elem"));
elem e255(elem::SYM, t_arith_op::NOP, dict.get_lexeme("preference"));
production gp256{{e252, e254, e12, e187, e12, e254, e2, e254, e12, e189, e12, e254, e12, e187, e12, e254, e2, e255, }, {}, };
elem e257(elem::SYM, t_arith_op::NOP, dict.get_lexeme("constraint_builtin"));
production gp258{{e254, e132, e2, e257, }, {}, };
elem e259(elem::SYM, t_arith_op::NOP, dict.get_lexeme("constraint_builtin_name"));
elem e260(elem::SYM, t_arith_op::NOP, dict.get_lexeme("constraint_arg"));
production gp261{{e257, e259, e12, e45, e12, e260, e12, e46, }, {}, };
production gp262{{e260, e96, }, {}, };
elem e263(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"len\""));
elem e264(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"substr\""));
production gp265{{e259, e263, e2, e264, }, {}, };
elem e266(elem::SYM, t_arith_op::NOP, dict.get_lexeme("pref"));
elem e267(elem::SYM, t_arith_op::NOP, dict.get_lexeme("priority"));
production gp268{{e255, e266, e2, e267, }, {}, };
elem e269(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"_pref\""));
production gp270{{e266, e269, }, {}, };
production gp271{{e267, e96, }, {}, };
elem e272(elem::SYM, t_arith_op::NOP, dict.get_lexeme("directive"));
elem e273(elem::SYM, t_arith_op::NOP, dict.get_lexeme("string_drctv"));
elem e274(elem::SYM, t_arith_op::NOP, dict.get_lexeme("stdout_drctv"));
elem e275(elem::SYM, t_arith_op::NOP, dict.get_lexeme("trace_drctv"));
elem e276(elem::SYM, t_arith_op::NOP, dict.get_lexeme("internal_drctv"));
elem e277(elem::SYM, t_arith_op::NOP, dict.get_lexeme("domain_drctv"));
elem e278(elem::SYM, t_arith_op::NOP, dict.get_lexeme("eval_drctv"));
elem e279(elem::SYM, t_arith_op::NOP, dict.get_lexeme("quote_drctv"));
elem e280(elem::SYM, t_arith_op::NOP, dict.get_lexeme("codec_drctv"));
elem e281(elem::SYM, t_arith_op::NOP, dict.get_lexeme("bwd_drctv"));
production gp282{{e272, e273, e2, e274, e2, e275, e2, e276, e2, e277, e2, e278, e2, e279, e2, e280, e2, e281, }, {}, };
elem e283(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"@string\""));
elem e284(elem::SYM, t_arith_op::NOP, dict.get_lexeme("strdir"));
production gp285{{e273, e283, e10, e284, e12, e51, }, {}, };
elem e286(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"@stdout\""));
production gp287{{e274, e286, e10, e124, e12, e51, }, {}, };
elem e288(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"@trace\""));
production gp289{{e275, e288, e10, e127, e12, e51, }, {}, };
elem e290(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"@internal\""));
production gp291{{e276, e290, e10, e124, e12, e51, }, {}, };
elem e292(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"@domain\""));
production gp293{{e277, e292, e10, e99, e12, e96, e12, e96, e12, e51, }, {}, };
elem e294(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"@eval\""));
production gp295{{e278, e294, e10, e99, e12, e99, e12, e99, e12, e96, e12, e51, }, {}, };
elem e296(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"@quote\""));
production gp297{{e279, e296, e10, e99, e12, e99, e12, e118, e12, e51, }, {}, };
elem e298(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"@codec\""));
production gp299{{e280, e298, e10, e99, e12, e99, e12, e99, e12, e96, e12, e51, }, {}, };
elem e300(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"@bwd\""));
production gp301{{e281, e300, e12, e51, }, {}, };
elem e302(elem::SYM, t_arith_op::NOP, dict.get_lexeme("fname"));
elem e303(elem::SYM, t_arith_op::NOP, dict.get_lexeme("cmdline"));
elem e304(elem::SYM, t_arith_op::NOP, dict.get_lexeme("cmdlinefile"));
production gp305{{e284, e127, e12, e302, e2, e127, e12, e114, e2, e127, e12, e303, e2, e127, e12, e304, e2, e127, e12, e124, }, {}, };
production gp306{{e302, e55, e8, e57, }, {}, };
production gp307{{e303, e42, e96, }, {}, };
production gp308{{e304, e55, e42, e96, e57, }, {}, };
elem e309(elem::SYM, t_arith_op::NOP, dict.get_lexeme("typedef"));
elem e310(elem::SYM, t_arith_op::NOP, dict.get_lexeme("predtypedef"));
elem e311(elem::SYM, t_arith_op::NOP, dict.get_lexeme("structypedef"));
production gp312{{e309, e310, e2, e311, }, {}, };
elem e313(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"predtype\""));
elem e314(elem::SYM, t_arith_op::NOP, dict.get_lexeme("predtypedef_args"));
production gp315{{e310, e313, e10, e127, e12, e314, e12, e51, }, {}, };
elem e316(elem::SYM, t_arith_op::NOP, dict.get_lexeme("type"));
elem e317(elem::OPENP, t_arith_op::NOP, dict.get_lexeme("("));
elem e318(elem::CLOSEP, t_arith_op::NOP, dict.get_lexeme(")"));
elem e319(elem::ARITH, t_arith_op::MULT, dict.get_lexeme("*"));
production gp320{{e314, e45, e12, e46, e2, e45, e12, e316, e12, e101, e317, e12, e49, e12, e316, e12, e101, e318, e319, e12, e46, }, {}, };
elem e321(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"struct\""));
elem e322(elem::SYM, t_arith_op::NOP, dict.get_lexeme("structypename"));
elem e323(elem::SYM, t_arith_op::NOP, dict.get_lexeme("membdecl"));
production gp324{{e311, e321, e12, e322, e12, e65, e12, e323, e317, e12, e323, e318, e319, e12, e67, }, {}, };
production gp325{{e322, e127, }, {}, };
elem e326(elem::SYM, t_arith_op::NOP, dict.get_lexeme("structype"));
production gp327{{e326, e127, }, {}, };
production gp328{{e323, e316, e12, e101, e317, e12, e49, e12, e101, e318, e319, e12, e51, }, {}, };
elem e329(elem::SYM, t_arith_op::NOP, dict.get_lexeme("primtype"));
production gp330{{e316, e329, e2, e326, }, {}, };
elem e331(elem::SYM, t_arith_op::NOP, dict.get_lexeme("simple_type"));
elem e332(elem::SYM, t_arith_op::NOP, dict.get_lexeme("bitsz_type"));
production gp333{{e329, e331, e2, e332, }, {}, };
elem e334(elem::SYM, t_arith_op::NOP, dict.get_lexeme("int_type"));
elem e335(elem::SYM, t_arith_op::NOP, dict.get_lexeme("char_type"));
elem e336(elem::SYM, t_arith_op::NOP, dict.get_lexeme("sym_type"));
production gp337{{e331, e334, e2, e335, e2, e336, }, {}, };
elem e338(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"int\""));
production gp339{{e334, e338, }, {}, };
elem e340(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"char\""));
production gp341{{e335, e340, }, {}, };
elem e342(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"sym\""));
production gp343{{e336, e342, }, {}, };
elem e344(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"int:\""));
elem e345(elem::SYM, t_arith_op::NOP, dict.get_lexeme("bitsz"));
production gp346{{e332, e344, e12, e345, }, {}, };
production gp347{{e345, e96, }, {}, };
elem e348(elem::SYM, t_arith_op::NOP, dict.get_lexeme("state_block"));
elem e349(elem::SYM, t_arith_op::NOP, dict.get_lexeme("sb_header"));
elem e350(elem::SYM, t_arith_op::NOP, dict.get_lexeme("sb_statements"));
production gp351{{e348, e60, e349, e350, e12, e62, }, {}, };
elem e352(elem::SYM, t_arith_op::NOP, dict.get_lexeme("sb_flipping"));
elem e353(elem::SYM, t_arith_op::NOP, dict.get_lexeme("sb_nonflipping"));
production gp354{{e349, e352, e2, e353, }, {}, };
elem e355(elem::SYM, t_arith_op::NOP, dict.get_lexeme("sb_label"));
elem e356(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"~:\""));
production gp357{{e352, e355, e356, }, {}, };
production gp358{{e353, e355, e53, }, {}, };
production gp359{{e355, e127, }, {}, };
elem e360(elem::SYM, t_arith_op::NOP, dict.get_lexeme("sb_statement"));
elem e361(elem::SYM, t_arith_op::NOP, dict.get_lexeme("sb_statements_rest"));
production gp362{{e350, e12, e360, e361, }, {}, };
production gp363{{e361, e12, e360, e361, e2, e14, }, {}, };
elem e364(elem::SYM, t_arith_op::NOP, dict.get_lexeme("fof"));
production gp365{{e360, e348, e2, e204, e2, e200, e2, e364, }, {}, };
elem e366(elem::SYM, t_arith_op::NOP, dict.get_lexeme("form"));
production gp367{{e364, e201, e12, e202, e12, e366, e12, e51, }, {}, };
elem e368(elem::SYM, t_arith_op::NOP, dict.get_lexeme("form1"));
elem e369(elem::SYM, t_arith_op::NOP, dict.get_lexeme("causal_op"));
production gp370{{e366, e368, e317, e12, e369, e12, e368, e318, e319, }, {}, };
elem e371(elem::SYM, t_arith_op::NOP, dict.get_lexeme("matrix"));
elem e372(elem::SYM, t_arith_op::NOP, dict.get_lexeme("junct_op"));
production gp373{{e368, e371, e317, e12, e372, e12, e371, e318, e319, }, {}, };
elem e374(elem::SYM, t_arith_op::NOP, dict.get_lexeme("implies"));
elem e375(elem::SYM, t_arith_op::NOP, dict.get_lexeme("coimplies"));
production gp376{{e369, e374, e2, e375, }, {}, };
elem e377(elem::SYM, t_arith_op::NOP, dict.get_lexeme("and"));
elem e378(elem::SYM, t_arith_op::NOP, dict.get_lexeme("or"));
production gp379{{e372, e377, e2, e378, }, {}, };
elem e380(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"&&\""));
production gp381{{e377, e380, }, {}, };
elem e382(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"||\""));
production gp383{{e378, e382, }, {}, };
elem e384(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"->\""));
production gp385{{e374, e384, }, {}, };
elem e386(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"<->\""));
production gp387{{e375, e386, }, {}, };
elem e388(elem::SYM, t_arith_op::NOP, dict.get_lexeme("neg_matrix"));
elem e389(elem::SYM, t_arith_op::NOP, dict.get_lexeme("matrix_block"));
elem e390(elem::SYM, t_arith_op::NOP, dict.get_lexeme("prefix_decl"));
production gp391{{e371, e388, e2, e389, e2, e390, e2, e124, e2, e183, }, {}, };
production gp392{{e388, e68, e371, }, {}, };
production gp393{{e389, e65, e12, e366, e12, e67, }, {}, };
elem e394(elem::SYM, t_arith_op::NOP, dict.get_lexeme("prefix"));
elem e395(elem::SYM, t_arith_op::NOP, dict.get_lexeme("prefix_arg"));
production gp396{{e390, e394, e12, e395, e2, e394, e12, e395, e12, e366, }, {}, };
elem e397(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"forall\""));
elem e398(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"exists\""));
elem e399(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"unique\""));
production gp400{{e394, e397, e2, e398, e2, e399, }, {}, };
production gp401{{e395, e101, e2, e127, }, {}, };
elem e402(elem::SYM, t_arith_op::NOP, dict.get_lexeme("guard_statement"));
elem e403(elem::SYM, t_arith_op::NOP, dict.get_lexeme("if_then_else"));
elem e404(elem::SYM, t_arith_op::NOP, dict.get_lexeme("if_then"));
elem e405(elem::SYM, t_arith_op::NOP, dict.get_lexeme("while_do"));
production gp406{{e402, e403, e2, e404, e2, e405, }, {}, };
elem e407(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"if\""));
elem e408(elem::SYM, t_arith_op::NOP, dict.get_lexeme("condition"));
elem e409(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"then\""));
elem e410(elem::SYM, t_arith_op::NOP, dict.get_lexeme("gs_prog"));
production gp411{{e404, e407, e12, e408, e12, e409, e12, e410, }, {}, };
elem e412(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"else\""));
production gp413{{e403, e404, e12, e412, e12, e410, }, {}, };
elem e414(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"while\""));
elem e415(elem::STR, t_arith_op::NOP, dict.get_lexeme("\"do\""));
production gp416{{e405, e414, e12, e408, e12, e415, e12, e410, }, {}, };
production gp417{{e408, e366, }, {}, };
elem e418(elem::SYM, t_arith_op::NOP, dict.get_lexeme("statement"));
elem e419(elem::SYM, t_arith_op::NOP, dict.get_lexeme("statement0"));
production gp420{{e410, e212, e2, e418, e2, e419, }, {}, };
elem e421(elem::SYM, t_arith_op::NOP, dict.get_lexeme("rule0"));
elem e422(elem::SYM, t_arith_op::NOP, dict.get_lexeme("fact0"));
elem e423(elem::SYM, t_arith_op::NOP, dict.get_lexeme("fof0"));
production gp424{{e419, e421, e2, e422, e2, e423, }, {}, };
production gp425{{e421, e201, e12, e202, e12, e201, }, {}, };
production gp426{{e422, e205, }, {}, };
production gp427{{e423, e201, e12, e202, e12, e366, }, {}, };
elem e428(elem::SYM, t_arith_op::NOP, dict.get_lexeme("statements"));
production gp429{{e212, e428, }, {}, };
production gp430{{e428, e12, e418, e428, e2, e14, }, {}, };
production gp431{{e418, e211, e2, e348, e2, e272, e2, e214, e2, e402, e2, e309, e2, e204, e2, e200, e2, e220, e2, e217, e2, e364, }, {}, };
elem e432(elem::SYM, t_arith_op::NOP, dict.get_lexeme("start"));
production gp433{{e432, e212, e12, }, {}, };
raw_prog rp434(dict);
rp434.g.insert(rp434.g.end(), { gp5, gp9, gp13, gp15, gp30, gp33, gp36, gp38, gp69, gp74, gp76, gp78, gp81, gp82, gp85, gp86, gp89, gp90, gp94, gp95, gp98, gp100, gp102, gp104, gp109, gp111, gp113, gp116, gp117, gp120, gp121, gp125, gp126, gp129, gp131, gp134, gp135, gp137, gp138, gp142, gp144, gp147, gp149, gp151, gp153, gp175, gp182, gp186, gp188, gp190, gp191, gp196, gp199, gp203, gp206, gp208, gp209, gp210, gp213, gp216, gp219, gp224, gp227, gp229, gp230, gp235, gp237, gp238, gp241, gp242, gp245, gp247, gp248, gp249, gp250, gp251, gp253, gp256, gp258, gp261, gp262, gp265, gp268, gp270, gp271, gp282, gp285, gp287, gp289, gp291, gp293, gp295, gp297, gp299, gp301, gp305, gp306, gp307, gp308, gp312, gp315, gp320, gp324, gp325, gp327, gp328, gp330, gp333, gp337, gp339, gp341, gp343, gp346, gp347, gp351, gp354, gp357, gp358, gp359, gp362, gp363, gp365, gp367, gp370, gp373, gp376, gp379, gp381, gp383, gp385, gp387, gp391, gp392, gp393, gp396, gp400, gp401, gp406, gp411, gp413, gp416, gp417, gp420, gp424, gp425, gp426, gp427, gp429, gp430, gp431, gp433, });
raw_prog rp435(dict);
rp435.nps.push_back(rp434);
raw_progs rps436(dict);
rps436.p = rp435;

auto& program_gen = rps436;
