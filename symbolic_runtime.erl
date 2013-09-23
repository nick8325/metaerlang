-module(symbolic_runtime).
-compile(export_all).

partial_application({thunk, Fun, Args}, Args2) ->
    {thunk, Fun, Args ++ Args2};
partial_application(Fun, Args) when is_function(Fun) ->
    {thunk, Fun, Args}.

calling(Name, Fun) ->
    {calling, Name, Fun}.

apply(Fun, Args) ->
    {apply, Fun, Args}.

make_fun(Mod, Fun, Arity) ->
    {'fun', Mod, Fun, Arity}.

call(erlang, make_fun, [Mod, Fun, Arity]) ->
    make_fun(Mod, Fun, Arity);
call(Mod, Fun, Args) ->
    ?MODULE:apply(make_fun(Mod, Fun, length(Args)), Args).

'case'(Values, Clauses) ->
    {'case', Values, Clauses}.

clause(Patts, Guard, Body) ->
    {clause, Patts, Guard, Body}.

unknown(Expr) ->
    {unknown, Expr}.

new_var() ->
    {var, make_ref()}.
