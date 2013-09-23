-module(symbolic).
-compile(export_all).

-import(cerl, [type/1, meta/1,
               set_ann/2,
               c_int/1,
               c_atom/1, atom_val/1,
               c_var/1, var_name/1,
               c_tuple/1, tuple_es/1,
               make_list/1, list_elements/1,
               alias_var/1, alias_pat/1,
               update_c_cons/3, cons_head/1, cons_tail/1,
               update_c_fun/3, c_fun/2, fun_arity/1, fun_vars/1, fun_body/1,
               update_c_apply/3, c_apply/2, apply_op/1, apply_args/1,
               c_call/3, call_module/1, call_name/1, call_args/1,
               c_primop/2, primop_name/1, primop_args/1,
               case_arg/1, case_clauses/1,
               clause_pats/1, clause_guard/1, clause_body/1, clause_vars/1,
               update_c_values/2, c_values/1, values_es/1,
               update_c_letrec/3, c_letrec/2, letrec_defs/1, letrec_body/1,
               update_c_let/4, c_let/3, let_vars/1, let_arg/1, let_body/1,
               update_c_module/5,
               module_name/1, module_defs/1, module_attrs/1, module_exports/1]).
-import(cerl_trees, [label/1, get_label/1, free_variables/1]).

c(Mod) ->
    c(Mod, []).
c(Mod, Opts) ->
    Opts1 = [{core_transform, symbolic}, no_error_module_mismatch, binary
            | Opts],
    {ok, Mod, Bin} = compile:file(Mod, Opts1),
    Mod1 = symbolic_runtime:module_name(Mod),
    code:load_binary(Mod1, Mod1, Bin).

core_transform(Mod, _Opts) ->
    Name = atom_val(module_name(Mod)),
    NewName = c_atom(symbolic_runtime:module_name(Name)),
    OldName = put(module_name, NewName),
    Mod1 = update_c_module(Mod, NewName, module_exports(Mod),
                           module_attrs(Mod), module_defs(Mod)),
    {Mod2, _} = label(Mod1),
    Mod3 = to_prolog(Mod2),
    put(module_name, OldName),
    Mod3.

to_prolog(Mod) ->
    Mod1 = core_to_core_pass(fun alpha_rename/1, Mod),
    Mod2 = definitions_pass(fun lambda_lift_letrec/1, Mod1),
    Mod3 = definitions_pass(fun lambda_lift/1, Mod2),
    Mod4 = definitions_pass(fun remove_redundant_partial_application/1, Mod3),
    definitions_pass(fun make_symbolic/1, Mod4).

pretty_print(Mod) ->
    io:format("~s~n", [core_pp:format(clear_anns(Mod))]).

clear_anns(Exp) ->
    cerl_trees:map(fun clear_ann/1, Exp).
clear_ann(Exp) ->
    set_ann(Exp, []).

%% Passes. A pass is something that transforms the core
%% while perhaps emitting new definitions.
pass(Fun, Mod) ->
    Defs = module_defs(Mod),

    OldDefs = put(defs, []),
    Fun(Defs),
    NewDefs = get(defs),
    put(defs, OldDefs),
    NewDefs.

%% A pass that returns a core module.
core_to_core_pass(Fun, Mod) ->
    Fun1 = fun(Defs) ->
        Res = Fun(Defs),
        put(defs, Res ++ get(defs))
    end,
    NewDefs = pass(Fun1, Mod),
    update_c_module(Mod, module_name(Mod), module_exports(Mod),
                    module_attrs(Mod), NewDefs).

%% A pass that acts on each definition separately.
definitions_pass(Fun, Mod) ->
    core_to_core_pass(fun(Defs) ->
        [ {Name, Fun(Body)} || {Name, Body} <- Defs ]
    end, Mod).

%% Emit a new function.
emit(Name, Fun) ->
    put(defs, [{Name, Fun}|get(defs)]).

%% Mapping over expressions.
map_with_type(Fun, Expr) ->
    cerl_trees:map(fun(E) -> Fun(type(E), E) end, Expr).
map_bottom_up_with_type(Fun, Expr) ->
    cerl_extra:map_bottom_up(fun(E) -> Fun(type(E), E) end, Expr).

%% Fresh name generation from labels.
fresh_name(Exp) ->
    list_to_atom("!var" ++ integer_to_list(get_label(Exp))).

%% Alpha-rename all local names so they're unique.
alpha_rename(Defs) ->
    Globals = gb_sets:from_list([ var_name(Name) || {Name, _} <- Defs ]),
    Rename = fun(Type, Expr) ->
                     alpha_rename(Globals, Type, Expr)
             end,
    [ {Rename(var, Name), map_with_type(Rename, Body)}
      || {Name, Body} <- Defs ].

alpha_rename(Globals, var, Var) ->
    %% Quoth the manual:
    %% "[the label] is a unique number for every node, except for
    %%  variables (and function name variables) which get the same
    %%  label if they represent the same variable."
    %% Thus, we can just generate a name based on the variable's label.
    case gb_sets:is_member(var_name(Var), Globals) of
        true ->
            Var;
        false ->
            c_var(rename(fresh_name(Var), var_name(Var)))
    end;
alpha_rename(_, _, Expr) ->
    Expr.

rename(Name, {_, Arity}) ->
    {Name, Arity};
rename(Name, _) ->
    Name.

%% Lambda-lift all functions defined in letrecs.
lambda_lift_letrec(Expr) ->
    map_bottom_up_with_type(fun lambda_lift_letrec/2, Expr).
lambda_lift_letrec(letrec, LetRec) ->
    Defs = letrec_defs(LetRec),
    Body = letrec_body(LetRec),
    do_lambda_lift_letrec(Defs, Body);
lambda_lift_letrec(_, Expr) ->
    Expr.

do_lambda_lift_letrec(Defs, Body) ->
    %% All variables that are free in the letrec's defs.
    Env =
        lists:map(fun cerl:c_var/1,
        lists:usort(
          [ X || {_, Fun} <- Defs,
                 X <- free_variables(Fun), is_local(X) ] --
          [ var_name(Name) || {Name, _} <- Defs ])),

    Subst =
        [ {Name,
           partial_application(bump_arity(length(Env), Name), Env)}
        || {Name, _} <- Defs],
    [ emit(bump_arity(length(Env), Name),
           lambda_lift_letrec(
           c_fun(Env ++ fun_vars(Fun), subst(Subst, fun_body(Fun)))))
      || {Name, Fun} <- Defs ],
    subst(Subst, Body).
is_local({_,_}) ->
    false;
is_local(_) ->
    true.
bump_arity(N, Name) ->
    {Fun, Arity} = var_name(Name),
    c_var({Fun, N + Arity}).

%% This substitution function assumes there are no name clashes.
subst(Subst, Expr) ->
    map_with_type(fun(Type, E) -> subst(Subst, Type, E) end, Expr).
subst(Subst, var, Var) ->
    case lists:keyfind(catch Var, 1, Subst) of
        {_, New} -> New;
        false -> Var
    end;
subst(_, _, Expr) ->
    Expr.

%% Generate a call to a runtime function.
runtime_name() ->
    symbolic_runtime.
runtime() ->
    c_atom(runtime_name()).
runtime(Fun, Args) ->
    c_call(runtime(), c_atom(Fun), Args).
unpack_runtime(Expr) ->
    unpack_runtime(type(Expr), Expr).
unpack_runtime(call, Call) ->
    case atom_val(call_module(Call)) == runtime_name() of
        true ->
            {atom_val(call_name(Call)), call_args(Call)};
        _ ->
            false
    end;
unpack_runtime(_, _) ->
    false.

%% Generate a call to the partial application "primop".
partial_application(Fun, []) ->
    Fun;
partial_application(Fun, Args) ->
    runtime(partial_application, [Fun, make_list(Args)]).
unpack_partial_application(Expr) ->
    case unpack_runtime(Expr) of
        {partial_application, [Fun, Args]} ->
            {Fun, list_elements(Args)};
        _ ->
            false
    end.

%% Lambda-lift ordinary funs, not defined inside letrec.
lambda_lift(Fun) ->
    %% Don't lambda-lift top-level functions!
    update_c_fun(Fun, fun_vars(Fun),
                 map_with_type(fun lambda_lift/2, fun_body(Fun))).
lambda_lift('fun', Fun) ->
    %% Reduce to letrec.
    Name = c_var({fresh_name(Fun), fun_arity(Fun)}),
    do_lambda_lift_letrec([{Name, Fun}], Name);
lambda_lift(_, Expr) ->
    Expr.

%% Remove partial applications that are immediately applied.
remove_redundant_partial_application(Expr) ->
    map_with_type(fun remove_redundant_partial_application/2, Expr).
remove_redundant_partial_application(apply, Apply) ->
    Op = apply_op(Apply),
    Args = apply_args(Apply),
    case unpack_partial_application(Op) of
        {F, Env} ->
            c_apply(F, Env ++ Args);
        false ->
            Apply
    end;
remove_redundant_partial_application(_, Expr) ->
    Expr.

%% Translate function definitions to a symbolic form.
make_symbolic(Expr) ->
    map_with_type(fun make_symbolic/2, Expr).
make_symbolic(apply, Apply) ->
    runtime(apply, [apply_op(Apply), make_list(apply_args(Apply))]);
make_symbolic(call, Call) ->
    case unpack_runtime(Call) of
        false ->
            runtime(call, [call_module(Call),
                           call_name(Call),
                           make_list(call_args(Call))]);
        _ -> Call
    end;
make_symbolic(tuple, Tuple) ->
    runtime(tuple, [make_list(tuple_es(Tuple))]);
make_symbolic(primop, Primop) ->
    runtime(primop, [primop_name(Primop)]);
make_symbolic(var, Var) ->
    case var_name(Var) of
        {Fun, Arity} ->
            runtime(local_fun, [Var, get(module_name), c_atom(Fun), c_int(Arity)]);
        _ ->
            Var
    end;
make_symbolic('case', Case) ->
    runtime('case',
            [make_list(values_to_list(case_arg(Case))),
             make_list(case_clauses(Case))]);
make_symbolic(clause, Clause) ->
    %% Instantiate the variables in the clause's pattern.
    Vars = clause_vars(Clause),
    c_let(Vars,
          c_values([ runtime(new_var, []) || _ <- Vars ]),
          runtime(clause, [make_list(clause_pats(Clause)),
                           clause_guard(Clause),
                           clause_body(Clause)]));
make_symbolic(alias, Alias) ->
    runtime(alias, [alias_var(Alias), alias_pat(Alias)]);
make_symbolic(Type, Expr) when
      Type == literal; Type == 'let'; Type == seq; Type == values; Type == cons;
      Type == 'fun' ->
    Expr;
make_symbolic(_, Expr) ->
    runtime(unknown, [meta(Expr)]).

%% Missing: binary bitstr catch letrec module receive try
%% (relevant: binary bitstr catch try)

values_to_list(Expr) ->
    case type(Expr) of
        values ->
            values_es(Expr);
        _ ->
            [Expr]
    end.
