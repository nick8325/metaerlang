-module(symbolic).
-compile(export_all).

-import(cerl, [type/1,
               set_ann/2,
               c_atom/1, atom_val/1,
               c_var/1, var_name/1,
               update_c_fun/3, c_fun/2, fun_arity/1, fun_vars/1, fun_body/1,
               c_apply/2, apply_op/1, apply_args/1,
               c_call/3, call_module/1, call_name/1, call_args/1,
               c_primop/2, primop_name/1, primop_args/1,
               case_arg/1, case_clauses/1,
               values_es/1,
               update_c_letrec/3, c_letrec/2, letrec_defs/1, letrec_body/1,
               update_c_module/5,
               module_name/1, module_defs/1, module_attrs/1, module_exports/1]).
-import(cerl_trees, [label/1, get_label/1, free_variables/1]).

c(Mod) ->
    c(Mod, []).
c(Mod, Opts) ->
    shell_default:c(Mod, [{core_transform, monkey}|Opts]).

core_transform(Mod, _Opts) ->
    to_prolog(Mod),
    Mod.

to_prolog(Mod) ->
    Exports = lists:map(fun cerl:var_name/1, module_exports(Mod)),
    Mod1 = core_to_core_pass(on_definitions(fun lambda_lift_letrec/1), Mod),
    Mod2 = core_to_core_pass(on_definitions(fun lambda_lift/1), Mod1),
    Mod3 = core_to_core_pass(on_definitions(fun remove_redundant_partial_application/1), Mod2),
    io:format("~s~n", [core_pp:format(clear_anns(Mod3))]),
    {module_name(Mod), Exports, Mod1}.

clear_anns(Exp) ->
    cerl_trees:map(fun clear_ann/1, Exp).
clear_ann(Exp) ->
    set_ann(Exp, []).

pass(Fun, Mod) ->
    {Mod1, _} = label(Mod),
    Defs = module_defs(Mod1),

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
    list_to_atom("$var" ++ integer_to_list(get_label(Exp))).

map_definitions(Fun, Defs) ->
    [ {Name, Fun(Body)} || {Name, Body} <- Defs ].
on_definitions(Fun) ->
    fun(Defs) -> map_definitions(Fun, Defs) end.
map_with_type(Fun, Expr) ->
    cerl_trees:map(fun(E) -> Fun(type(E), E) end, Expr).

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
    %% There is no easy way to deal with binders, so I use a trick to
    %% avoid having to do it. Quoth the manual:
    %% "[the label] is a unique number for every node, except for
    %%  variables (and function name variables) which get the same
    %%  label if they represent the same variable."
    %% So, when substituting, we look at labels rather than names.
    
    %% A substitution from label to partially-applied function.
    Subst = [{get_label(Name),
              partial_application(lambda_lifted_name(Env, Name, Fun), Env)}
             || {Name, Fun} <- Defs],
    %% Generate the lambda-lifted functions.
    [ emit(lambda_lifted_name(Env, Name, Fun),
           c_fun(Env ++ fun_vars(Fun), subst(Subst, fun_body(Fun))))
      || {Name, Fun} <- Defs ],
    subst(Subst, Body);
lambda_lift_letrec(_, Expr) ->
    Expr.

is_local({_,_}) ->
    false;
is_local(_) ->
    true.

subst(Subst, Expr) ->
    map_with_type(fun(Type, E) -> subst(Subst, Type, E) end, Expr).
subst(Subst, var, Var) ->
    case lists:keyfind(catch get_label(Var), 1, Subst) of
        {_, New} -> New;
        false -> Var
    end;
subst(_, _, Expr) ->
    Expr.

lambda_lifted_name(Env, Name, Body) ->
    c_var({fresh_name(Name), length(Env) + fun_arity(Body)}).

partial_application(Fun, []) ->
    Fun;
partial_application(Fun, Args) ->
    c_primop(c_atom(partial_application), [Fun|Args]).
unpack_partial_application(Expr) ->
    case type(Expr) of
        primop ->
            case atom_val(primop_name(Expr)) of
                partial_application ->
                    [F|Xs] = primop_args(Expr),
                    {F,Xs};
                _ -> false
            end;
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
    Name = lambda_lifted_name(Env, Fun, Fun),
    emit(Name, c_fun(Env ++ Vars, Body)),
    partial_application(Name, Env);
lambda_lift(_, Expr) ->
    Expr.

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

arg_to_list(Expr) ->
    arg_to_list(type(Expr), Expr).
arg_to_list(values, Expr) ->
    values_es(Expr);
arg_to_list(_, Expr) ->
    Expr.
