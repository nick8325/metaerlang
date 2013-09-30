%%
%% %CopyrightBegin%
%%
%% Copyright Ericsson AB 2001-2010. All Rights Reserved.
%%
%% The contents of this file are subject to the Erlang Public License,
%% Version 1.1, (the "License"); you may not use this file except in
%% compliance with the License. You should have received a copy of the
%% Erlang Public License along with this software. If not, it can be
%% retrieved online at http://www.erlang.org/.
%%
%% Software distributed under the License is distributed on an "AS IS"
%% basis, WITHOUT WARRANTY OF ANY KIND, either express or implied. See
%% the License for the specific language governing rights and limitations
%% under the License.
%%
%% %CopyrightEnd%

-module(cerl_extra).

-export([map_top_down/2]).

-import(cerl, [alias_pat/1, alias_var/1, ann_c_alias/3, ann_c_apply/3,
	       ann_c_binary/2, ann_c_bitstr/6, ann_c_call/4,
	       ann_c_case/3, ann_c_catch/2, ann_c_clause/4,
	       ann_c_cons_skel/3, ann_c_fun/3, ann_c_let/4,
	       ann_c_letrec/3, ann_c_module/5, ann_c_primop/3,
	       ann_c_receive/4, ann_c_seq/3, ann_c_try/6,
	       ann_c_tuple_skel/2, ann_c_values/2, apply_args/1,
	       apply_op/1, binary_segments/1, bitstr_val/1,
	       bitstr_size/1, bitstr_unit/1, bitstr_type/1,
	       bitstr_flags/1, call_args/1, call_module/1, call_name/1,
	       case_arg/1, case_clauses/1, catch_body/1, clause_body/1,
	       clause_guard/1, clause_pats/1, clause_vars/1, concrete/1,
	       cons_hd/1, cons_tl/1, fun_body/1, fun_vars/1, get_ann/1,
	       let_arg/1, let_body/1, let_vars/1, letrec_body/1,
	       letrec_defs/1, letrec_vars/1, module_attrs/1,
	       module_defs/1, module_exports/1, module_name/1,
	       module_vars/1, primop_args/1, primop_name/1,
	       receive_action/1, receive_clauses/1, receive_timeout/1,
	       seq_arg/1, seq_body/1, set_ann/2, subtrees/1, try_arg/1,
	       try_body/1, try_vars/1, try_evars/1, try_handler/1,
	       tuple_es/1, type/1, update_c_alias/3, update_c_apply/3,
	       update_c_binary/2, update_c_bitstr/6, update_c_call/4,
	       update_c_case/3, update_c_catch/2, update_c_clause/4,
	       update_c_cons/3, update_c_cons_skel/3, update_c_fun/3,
	       update_c_let/4, update_c_letrec/3, update_c_module/5,
	       update_c_primop/3, update_c_receive/4, update_c_seq/3,
	       update_c_try/6, update_c_tuple/2, update_c_tuple_skel/2,
	       update_c_values/2, values_es/1, var_name/1]).


%% ---------------------------------------------------------------------

%% Like cerl_trees:map/2, but top-down.

-spec map_top_down(fun((cerl:cerl()) -> cerl:cerl()), cerl:cerl()) -> cerl:cerl().

map_top_down(F, T) ->
    map(F, T).

map(F, T) ->
    map_1(F, F(T)).

map_1(F, T) ->
    case type(T) of
 	literal ->
	    case concrete(T) of
		[_ | _] ->
		    update_c_cons(T, map(F, cons_hd(T)),
				  map(F, cons_tl(T)));
		V when tuple_size(V) > 0 ->
		    update_c_tuple(T, map_list(F, tuple_es(T)));
		_ ->
		    T
	    end;
 	var ->
 	    T;
	values ->
 	    update_c_values(T, map_list(F, values_es(T)));
	cons ->
	    update_c_cons_skel(T, map(F, cons_hd(T)),
			       map(F, cons_tl(T)));
 	tuple ->
	    update_c_tuple_skel(T, map_list(F, tuple_es(T)));
 	'let' ->
	    update_c_let(T, map_list(F, let_vars(T)),
			 map(F, let_arg(T)),
			 map(F, let_body(T)));
	seq ->
 	    update_c_seq(T, map(F, seq_arg(T)),
			 map(F, seq_body(T)));
 	apply ->
	    update_c_apply(T, map(F, apply_op(T)),
			   map_list(F, apply_args(T)));
 	call ->
 	    update_c_call(T, map(F, call_module(T)),
			  map(F, call_name(T)),
			  map_list(F, call_args(T)));
 	primop ->
	    update_c_primop(T, map(F, primop_name(T)),
			    map_list(F, primop_args(T)));
 	'case' ->
 	    update_c_case(T, map(F, case_arg(T)),
			  map_list(F, case_clauses(T)));
 	clause ->
 	    update_c_clause(T, map_list(F, clause_pats(T)),
			    map(F, clause_guard(T)),
			    map(F, clause_body(T)));
 	alias ->
	    update_c_alias(T, map(F, alias_var(T)),
			   map(F, alias_pat(T)));
 	'fun' ->
	    update_c_fun(T, map_list(F, fun_vars(T)),
			 map(F, fun_body(T)));
 	'receive' ->
	    update_c_receive(T, map_list(F, receive_clauses(T)),
			     map(F, receive_timeout(T)),
			     map(F, receive_action(T)));
 	'try' ->
 	    update_c_try(T, map(F, try_arg(T)),
			 map_list(F, try_vars(T)),
			 map(F, try_body(T)),
			 map_list(F, try_evars(T)),
			 map(F, try_handler(T)));
 	'catch' ->
	    update_c_catch(T, map(F, catch_body(T)));
	binary ->
	    update_c_binary(T, map_list(F, binary_segments(T)));
	bitstr ->
	    update_c_bitstr(T, map(F, bitstr_val(T)),
			    map(F, bitstr_size(T)),
			    map(F, bitstr_unit(T)),
			    map(F, bitstr_type(T)),
			    map(F, bitstr_flags(T)));
	letrec ->
	    update_c_letrec(T, map_pairs(F, letrec_defs(T)),
			    map(F, letrec_body(T)));
	module ->
	    update_c_module(T, map(F, module_name(T)),
			    map_list(F, module_exports(T)),
			    map_pairs(F, module_attrs(T)),
			    map_pairs(F, module_defs(T)))
    end.

map_list(F, [T | Ts]) ->
    [map(F, T) | map_list(F, Ts)];
map_list(_, []) ->
    [].

map_pairs(F, [{T1, T2} | Ps]) ->
    [{map(F, T1), map(F, T2)} | map_pairs(F, Ps)];
map_pairs(_, []) ->
    [].
