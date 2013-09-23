-module(symbolic).
-compile(export_all).

-import(cerl, [type/1,
               set_ann/2,
               c_int/1,
               c_atom/1, atom_val/1,
               c_var/1, var_name/1,
               c_tuple/1, make_list/1, list_elements/1,
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
    Mod1 = rename_module(Mod),
    code:load_binary(Mod1, Mod1, Bin).

core_transform(Mod, _Opts) ->
    Mod1 = update_c_module(Mod, c_atom(rename_module(atom_val(module_name(Mod)))),
                           module_exports(Mod), module_attrs(Mod), module_defs(Mod)),
    {Mod2, _} = label(Mod1),
    to_prolog(Mod2).

to_prolog(Mod) ->
    Mod1 = core_to_core_pass(on_definitions(fun uniquify_letrec/1), Mod),
    Mod2 = core_to_core_pass(on_definitions(fun lambda_lift_letrec/1), Mod1),
    Mod3 = core_to_core_pass(on_definitions(fun lambda_lift/1), Mod2),
    Mod4 = core_to_core_pass(on_definitions(fun remove_redundant_partial_application/1), Mod3),
    Mod5 = core_to_core_pass(fun(Defs) -> make_symbolic(module_name(Mod4), Defs) end,
                             Mod4),
    io:format("~s~n", [core_pp:format(clear_anns(Mod5))]),
    Mod5.

rename_module(Mod) ->
    list_to_atom("!symb" ++ atom_to_list(Mod)).

clear_anns(Exp) ->
    cerl_trees:map(fun clear_ann/1, Exp).
clear_ann(Exp) ->
    set_ann(Exp, []).

pass(Fun, Mod) ->
    Defs = module_defs(Mod),

    OldDefs = put(defs, []),
    Fun(Defs),
    NewDefs = get(defs),
    put(defs, OldDefs),
    NewDefs.

core_to_core_pass(Fun, Mod) ->
    Fun1 = fun(Defs) ->
        Res = Fun(Defs),
        put(defs, Res ++ get(defs))
    end,
    NewDefs = pass(Fun1, Mod),
    update_c_module(Mod, module_name(Mod), module_exports(Mod),
                    module_attrs(Mod), NewDefs).

emit(Name, Fun) ->
    put(defs, [{Name, Fun}|get(defs)]).

fresh_name(Exp) ->
    list_to_atom("!var" ++ integer_to_list(get_label(Exp))).
fresh_fun(Fun) ->
    c_var({fresh_name(Fun), fun_arity(Fun)}).

map_definitions(Fun, Defs) ->
    [ {Name, Fun(Body)} || {Name, Body} <- Defs ].
on_definitions(Fun) ->
    fun(Defs) -> map_definitions(Fun, Defs) end.
map_with_type(Fun, Expr) ->
    cerl_trees:map(fun(E) -> Fun(type(E), E) end, Expr).

%% Alpha-rename all letrec-bound names so they're unique.
uniquify_letrec(Expr) ->
    map_with_type(fun uniquify_letrec/2, Expr).
uniquify_letrec(letrec, LetRec) ->
    Defs = letrec_defs(LetRec),
    Body = letrec_body(LetRec),

    %% There is no easy way to deal with binders, so I use a trick to
    %% avoid having to do it. Quoth the manual:
    %% "[the label] is a unique number for every node, except for
    %%  variables (and function name variables) which get the same
    %%  label if they represent the same variable."
    %% So, when substituting, we look at labels rather than names.

    Subst = [{get_label(Name), fresh_fun(Fun)} || {Name, Fun} <- Defs],
    update_c_letrec(LetRec,
                    [{fresh_fun(Fun), subst_label(Subst, Fun)}
                    || {_, Fun} <- Defs],
                    subst_label(Subst, Body));
uniquify_letrec(_, Expr) ->
    Expr.

subst_label(Subst, Expr) ->
    map_with_type(fun(Type, E) -> subst_label(Subst, Type, E) end, Expr).
subst_label(Subst, var, Var) ->
    case lists:keyfind(catch get_label(Var), 1, Subst) of
        {_, New} -> New;
        false -> Var
    end;
subst_label(_, _, Expr) ->
    Expr.

%% Lambda-lift all functions defined in letrecs.
lambda_lift_letrec(Expr) ->
    map_with_type(fun lambda_lift_letrec/2, Expr).
lambda_lift_letrec(letrec, LetRec) ->
    Defs = letrec_defs(LetRec),
    Body = letrec_body(LetRec),
    Env = lists:usort(
            [ c_var(X) || {_, Fun} <- Defs,
                          X <- free_variables(Fun),
                          is_local(X) ]),
    
    Subst = [{Name, partial_application(lambda_lifted_name(Env, Name), Env)}
             || {Name, _} <- Defs],
    [ emit(lambda_lifted_name(Env, Name),
           c_fun(Env ++ fun_vars(Fun), subst(Subst, fun_body(Fun))))
      || {Name, Fun} <- Defs ],
    subst(Subst, Body);
lambda_lift_letrec(_, Expr) ->
    Expr.

is_local({_,_}) ->
    false;
is_local(_) ->
    true.

lambda_lifted_name(Env, Name) ->
    {Fun, Arity} = var_name(Name),
    c_var({Fun, length(Env) + Arity}).

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
    case type(Expr) of
        call ->
            Mod = call_module(Expr),
            RuntimeName = runtime_name(),
            case atom_val(Mod) of
                RuntimeName ->
                    {atom_val(call_name(Expr)), call_args(Expr)};
                _ ->
                    false
            end;
        _ ->
            false
    end.

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
lambda_lift(Expr) ->
    case type(Expr) of
        %% Don't lambda-lift top-level functions!
        'fun' ->
            update_c_fun(Expr,
                         fun_vars(Expr),
                         map_with_type(fun lambda_lift/2, fun_body(Expr)));
        _ ->
            map_with_type(fun lambda_lift/2, Expr)
    end.
lambda_lift('fun', Fun) ->
    Vars = fun_vars(Fun),
    Body = fun_body(Fun),
    Env = [ c_var(X) || X <- free_variables(Fun), is_local(X) ],
    Name = lambda_lifted_name(Env, fresh_fun(Fun)),
    emit(Name, c_fun(Env ++ Vars, Body)),
    partial_application(Name, Env);
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
make_symbolic(Mod, Defs) ->
    [ {Name, make_symbolic_fun(Mod, Name, Fun)}
    || {Name, Fun} <- Defs ].
make_symbolic_fun(Mod, Name, Fun) ->
    {Atom, _} = var_name(Name),
    Vars = fun_vars(Fun),
    Body = map_with_type(fun make_symbolic_expr/2, fun_body(Fun)),
    c_fun(Vars,
          runtime(calling,
                  [c_tuple([Mod, c_atom(Atom), make_list(Vars)]),
                   c_fun([], Body)])).

make_symbolic_expr(apply, Apply) ->
    runtime(apply, [apply_op(Apply), make_list(apply_args(Apply))]);
make_symbolic_expr(call, Call) ->
    runtime(call, [call_module(Call),
                   call_name(Call),
                   make_list(call_args(Call))]);
make_symbolic_expr('case', Case) ->
    runtime('case',
            [make_list(values_to_list(case_arg(Case))),
             make_list(case_clauses(Case))]);
make_symbolic_expr(clause, Clause) ->
    %% Instantiate the variables in the clause's pattern.
    Vars = clause_vars(Clause),
    c_let(Vars,
          c_values([ runtime(new_var, []) || _ <- Vars ]),
          runtime(clause, [make_list(clause_pats(Clause)),
                           clause_guard(Clause),
                           clause_body(Clause)]));
make_symbolic_expr(alias, Alias) ->
    runtime(alias, [alias_var(Alias), alias_pat(Alias)]);
make_symbolic_expr(Type, Expr) when
      Type == 'fun'; Type == literal; Type == var;
      Type == 'let'; Type == seq; Type == values; Type == cons;
      Type == tuple ->
    Expr;
make_symbolic_expr(_, Expr) ->
    runtime(unknown, [Expr]).

%% Missing: binary bitstr catch letrec module primop receive try

values_to_list(Expr) ->
    case type(Expr) of
        values ->
            values_es(Expr);
        _ ->
            [Expr]
    end.
