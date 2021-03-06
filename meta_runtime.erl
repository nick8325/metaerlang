-module(meta_runtime).
-compile(export_all).
-compile({no_auto_import, [apply/2]}).

partial_application({thunk, Fun, Args}, Args2) ->
    {thunk, Fun, Args ++ Args2};
partial_application(Fun={'fun',_,_,_}, Args) ->
    {thunk, Fun, Args}.

in_function(Name, Fun) ->
    {in_function, Name, Fun}.

apply({thunk, Fun, Args}, Args2) ->
    apply(Fun, Args ++ Args2);
apply({'fun', M, F, A}, Args) ->
    case A == length(Args) of
        true -> {apply, M, F, Args};
        false -> failure()
    end;
apply(Fun, Args) ->
    {apply, Fun, Args}.

'case'(Values, Clauses) ->
    {'case', Values, Clauses}.

'catch'(Expr) ->
    {'catch', Expr}.

'try'(Expr, Success, Failure) ->
    {'try', Expr, Success, Failure}.

clause(Patts, Guard, Body) ->
    {clause, Patts, Guard, Body}.

alias(X, Y) ->
    {alias, X, Y}.

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
