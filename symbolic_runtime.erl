-module(symbolic_runtime).
-compile(export_all).

runtime_name(Mod) ->
    list_to_atom("!symb" ++ atom_to_list(Mod)).

partial_application({thunk, Fun, Args}, Args2) ->
    {thunk, Fun, Args ++ Args2};
partial_application(Fun, Args) when is_function(Fun) ->
    {thunk, Fun, Args}.

in_function(Name, Fun) ->
    {in_function, Name, Fun}.

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
    case erlang:function_exported(runtime_name(Mod), Fun, Arity) of
        true ->
            erlang:make_fun(runtime_name(Mod), Fun, Arity);
        false ->
            {'fun', Mod, Fun, Arity}
    end;
make_fun(Mod, Fun, Arity) ->
    {'fun', Mod, Fun, Arity}.

local_fun(Fun, Mod, Name, Arity) ->
    {local_fun, Fun, Mod, Name, Arity}.

call(erlang, make_fun, [Mod, Fun, Arity]) ->
    make_fun(Mod, Fun, Arity);
call(Mod, Fun, Args) ->
    ?MODULE:apply(make_fun(Mod, Fun, length(Args)), Args).

'case'(Values, Clauses) ->
    {'case', Values, Clauses}.

clause(Patts, Guard, Body) ->
    {clause, Patts, Guard, Body}.

tuple(Xs) ->
    {tuple, Xs}.

primop(X) ->
    {primop, X}.

unknown(Expr) ->
    {unknown, Expr}.

new_var() ->
    {var, make_ref()}.
