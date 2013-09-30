-module(test_gen).
-compile(export_all).
-include_lib("eqc/include/eqc.hrl").

atoms() ->
    elements([a,b,c,d,e,f,g,h]).

unique_list() ->
    unique_list([]).
unique_list(Xs) ->
    oneof([[],
           ?LET(X, ?SUCHTHAT(Y, atoms(), not member(Y, Xs)),
               [X|unique_list([X|Xs])])]).

member(_, []) ->
    false;
member(X, [X|_]) ->
    true;
member(X, [_|Xs]) ->
    member(X, Xs).
