-module(symbolic_runtime).
-compile(export_all).
-compile({no_auto_import, [apply/2]}).

module_name(Mod) ->
    list_to_atom("symbolic!" ++ atom_to_list(Mod)).

partial_application({thunk, Fun, Args}, Args2) ->
    {thunk, Fun, Args ++ Args2};
partial_application(Fun, Args) when is_function(Fun) ->
    {thunk, Fun, Args}.

in_function(Name, Fun) ->
    {in_function, Name, Fun}.

apply({thunk, Fun, Args}, Args2) ->
    apply(Fun, Args ++ Args2);
apply(Fun, Args) ->
    case is_safe(Fun, Args) of
        true -> erlang:apply(Fun, Args);
        false -> {apply, Fun, Args}
    end.

is_safe(Fun, Args) when is_function(Fun) ->
    erlang:fun_info(Fun, arity) == {arity, length(Args)};
is_safe(_, _) ->
    false.

make_fun(Mod, Fun, Arity) when is_atom(Mod), is_atom(Fun), is_integer(Arity) ->
    case erlang:function_exported(module_name(Mod), Fun, Arity) of
        true ->
            erlang:make_fun(module_name(Mod), Fun, Arity);
        false ->
            io:format("Unknown function ~p:~p/~p~n", [Mod, Fun, Arity]),
            failure()
    end;
make_fun(Mod, Fun, Arity) ->
    {'fun', Mod, Fun, Arity}.

'case'(Values, Clauses) ->
    {'case', Values, Clauses}.

clause(Patts, Guard, Body) ->
    {clause, Patts, Guard, Body}.

tuple(Xs) ->
    {tuple, Xs}.

primop(partial_application, [F|Args]) ->
    partial_application(F, Args);
primop(match_fail, _) ->
    failure();
primop(Primop, Args) ->
    {primop, Primop, Args}.

failure() ->
    {failure}.

unknown(Expr) ->
    {unknown, Expr}.

new_var() ->
    {var, make_ref()}.
