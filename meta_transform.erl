-module(meta_transform).
-compile(export_all).

-import(cerl, [type/1, meta/1, abstract/1,
               set_ann/2,
               c_int/1,
               c_atom/1, atom_val/1,
               c_var/1, var_name/1,
               c_catch/1, catch_body/1,
               try_arg/1, try_body/1, try_vars/1, try_evars/1, try_handler/1,
               c_tuple/1, tuple_es/1,
               make_list/1, list_elements/1, c_cons/2,
               alias_var/1, alias_pat/1,
               update_c_cons/3, cons_head/1, cons_tail/1,
               update_c_fun/3, c_fun/2, fun_arity/1, fun_vars/1, fun_body/1,
               update_c_apply/3, c_apply/2, apply_op/1, apply_args/1,
               c_call/3, call_module/1, call_name/1, call_args/1, call_arity/1,
               c_primop/2, primop_name/1, primop_args/1,
               case_arg/1, case_clauses/1,
               clause_pats/1, clause_guard/1, clause_body/1, clause_vars/1,
               update_c_values/2, c_values/1, values_es/1,
               update_c_letrec/3, c_letrec/2, letrec_defs/1, letrec_body/1,
               update_c_let/4, c_let/3, let_vars/1, let_arg/1, let_body/1,
               update_c_module/5,
               module_name/1, module_defs/1, module_attrs/1, module_exports/1]).
-import(cerl_trees, [label/1, get_label/1, free_variables/1]).

core_transform(Mod, Opts) ->
    save_process_dict(),

    Name =
        proplists:get_value(real_name, Opts,
                            atom_val(module_name(Mod))),

    put(module_name, Name),
    put(fresh_name, 0),

    Mod1 = to_symbolic(Mod, Opts),
    trace(symbolic2, Mod1, Opts),

    %% Rename the module.
    Mod2 =
        update_c_module(Mod1,
                        c_atom(meta_module_name(Name)),
                        module_exports(Mod1),
                        module_attrs(Mod1),
                        module_defs(Mod1)),
    trace(renamed, Mod2, Opts),

    restore_process_dict(),
    Mod2.

meta_module_name(Mod) ->
    list_to_atom("!" ++ atom_to_list(Mod)).

save_process_dict() ->
    put(old_process_dict, erase()),
    ok.
restore_process_dict() ->
    [ put(K, V) || {K, V} <- get(old_process_dict) ],
    ok.

to_symbolic(Mod, Opts) ->
    Mod1 = alpha_rename(Mod),
    trace(alpha_rename, Mod1, Opts),
    Mod2 = pass(fun lambda_lift_letrec/1, Mod1, Opts),
    trace(lambda_lift_letrec, Mod2, Opts),
    Mod3 = pass(fun lambda_lift/1, Mod2, Opts),
    trace(lambda_lift, Mod3, Opts),
    Mod4 = pass(fun make_symbolic/1, Mod3, Opts),
    trace(symbolic, Mod4, Opts),
    export_all(Mod4).

trace(Pass, Mod, Opts) ->
    case lists:member({trace, Pass}, Opts)
        orelse lists:member(trace, Opts) of
        true ->
            io:format("After pass ~p:~n", [Pass]),
            pretty_print(Mod),
            io:format("~n");
        false ->
            ok
    end.

pretty_print(Mod) ->
    io:format("~s~n", [core_pp:format(clear_anns(Mod))]).

%% Hack: core_pp:format crashes on labelled syntax trees.
clear_anns(Exp) ->
    cerl_trees:map(fun clear_ann/1, Exp).
clear_ann(Exp) ->
    set_ann(Exp, []).

%% Passes. A pass is something that transforms each definition.
%% while perhaps emitting new definitions.
pass(Fun, Mod, Opts) ->
    put(defs, []),
    Res = [{Name, pass_def(Fun, Name, Body, Opts)}
           || {Name, Body} <- module_defs(Mod)],
    update_c_module(Mod, module_name(Mod), module_exports(Mod),
                    module_attrs(Mod),
                    Res ++ get(defs)).
pass_def(Fun, Name, Body, Opts) ->
    case lists:member({symbolic, var_name(Name)}, Opts) of
        true ->
            Body;
        false ->
            Fun(Body)
    end.

%% Emit a new function.
emit(Name, Fun) ->
    put(defs, [{Name, Fun}|get(defs)]).

%% Mapping over expressions while matching on their type.
map_with_type(Fun, Expr) ->
    cerl_trees:map(fun(E) -> Fun(type(E), E) end, Expr).
map_bottom_up_with_type(Fun, Expr) ->
    cerl_extra:map_bottom_up(fun(E) -> Fun(type(E), E) end, Expr).

%% Generate a fresh name.
fresh_name() ->
    N = get(fresh_name),
    put(fresh_name, N+1),
    list_to_atom("v!" ++ integer_to_list(N)).

%% Alpha-rename all local names so they're unique.
alpha_rename(Mod) ->
    %% Quoth the manual:
    %% "[the label] is a unique number for every node, except for
    %%  variables (and function name variables) which get the same
    %%  label if they represent the same variable."
    %% Thus, we label the module, collect all variable labels,
    %% and then generate a substitution from *labels* to variables.

    {Mod1, _} = label(Mod),
    Exports = gb_sets:from_list(
                [ get_label(Name) || Name <- module_exports(Mod1) ]),

    Labels = cerl_trees:fold(fun collect_labels/2, gb_sets:new(), Mod1),
    Subst = gb_trees:from_orddict(
              orddict:from_list(
                [ {Label, fresh_name()}
                  || Label <- gb_sets:to_list(Labels),
                     not gb_sets:is_member(Label, Exports)])),
    map_with_type(fun(Type, E) -> subst_label(Subst, Type, E) end, Mod1).

collect_labels(Exp, Labels) ->
    collect_labels(type(Exp), Exp, Labels).
collect_labels(var, Exp, Labels) ->
    gb_sets:add(get_label(Exp), Labels);
collect_labels(_, _, Labels) ->
    Labels.

subst_label(Subst, var, Var) ->
    case gb_trees:lookup(get_label(Var), Subst) of
        none ->
            Var;
        {value, Name} ->
            c_var(rename(Name, var_name(Var)))
    end;
subst_label(_, _, Expr) ->
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

%% This substitution function assumes there are no name clashes
%% (as guaranteed by alpha_rename/1).
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
runtime_key() ->
    '!runtime'.
runtime() ->
    c_call(c_atom(erlang), c_atom(get), [c_atom(runtime_key())]).
runtime(Fun, Args) ->
    Runtime = c_var(fresh_name()),
    c_let([Runtime], runtime(),
          c_call(Runtime, c_atom(Fun), Args)).

%% Generate a call to the partial application "primop".
partial_application(Fun, []) ->
    Fun;
partial_application(Fun, Args) ->
    c_primop(c_atom(partial_application), [Fun|Args]).

%% Lambda-lift ordinary funs, not defined inside letrec.
lambda_lift(Fun) ->
    %% Don't lambda-lift top-level functions!
    update_c_fun(Fun, fun_vars(Fun),
                 map_with_type(fun lambda_lift/2, fun_body(Fun))).
lambda_lift('fun', Fun) ->
    %% Reduce to letrec.
    Name = c_var({fresh_name(), fun_arity(Fun)}),
    do_lambda_lift_letrec([{Name, Fun}], Name);
lambda_lift(_, Expr) ->
    Expr.

%% Translate function definitions to a symbolic form.
make_symbolic(Expr) ->
    map_with_type(fun make_symbolic/2, Expr).
make_symbolic(apply, Apply) ->
    runtime(apply, [apply_op(Apply), make_list(apply_args(Apply))]);
make_symbolic(call, Call) ->
    Fun = runtime(make_fun,
                  [call_module(Call), call_name(Call), c_int(call_arity(Call))]),
    runtime(apply, [Fun, make_list(call_args(Call))]);
make_symbolic(tuple, Tuple) ->
    runtime(tuple, [make_list(tuple_es(Tuple))]);
make_symbolic(primop, Primop) ->
    runtime(primop, [primop_name(Primop), make_list(primop_args(Primop))]);
make_symbolic(var, Var) ->
    case var_name(Var) of
        {Fun, Arity} ->
            runtime(make_fun, [c_atom(get(module_name)), c_atom(Fun), c_int(Arity)]);
        _ ->
            Var
    end;
make_symbolic('catch', Catch) ->
    runtime('catch', [Catch]);
make_symbolic('try', Try) ->
    runtime('try',
            [try_arg(Try),
             bind(try_vars(Try),
                  c_tuple([make_list(try_vars(Try)), try_body(Try)])),
             bind(try_evars(Try),
                  c_tuple([make_list(try_evars(Try)), try_handler(Try)]))]);
make_symbolic('case', Case) ->
    runtime('case',
            [make_list(values_to_list(case_arg(Case))),
             make_list(case_clauses(Case))]);
make_symbolic(clause, Clause) ->
    %% Instantiate the variables in the clause's pattern.
    Vars = clause_vars(Clause),
    bind(Vars,
          runtime(clause, [make_list(clause_pats(Clause)),
                           clause_guard(Clause),
                           c_fun([], clause_body(Clause))]));
make_symbolic(alias, Alias) ->
    runtime(alias, [alias_var(Alias), alias_pat(Alias)]);
make_symbolic(Type, Expr) when
      Type == literal; Type == 'let'; Type == seq; Type == values; Type == cons;
      Type == 'fun' ->
    Expr;
make_symbolic(_, Expr) ->
    runtime(unknown, [c_atom(type(Expr))]).

bind(Vars, Expr) ->
    c_let(Vars,
          c_values([ runtime(new_var, []) || _ <- Vars ]),
          Expr).

%% Missing: binary bitstr letrec module receive
%% (relevant: binary bitstr)

values_to_list(Expr) ->
    case type(Expr) of
        values ->
            values_es(Expr);
        _ ->
            [Expr]
    end.

%% Export all functions from a module.
export_all(Mod) ->
    update_c_module(Mod, module_name(Mod),
                    [Name || {Name, _} <- module_defs(Mod)],
                    module_attrs(Mod), module_defs(Mod)).
