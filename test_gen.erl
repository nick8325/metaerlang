-module(test_gen).
-compile(export_all).
-include_lib("eqc/include/eqc.hrl").

atom() ->
    elements([a,b,c,d,e,f,g,h]).

unique_list() ->
    unique_list([]).
unique_list(Xs) ->
    oneof([[],
           ?LET(X, ?SUCHTHAT(Y, atom(), not member(Y, Xs)),
               [X|unique_list([X|Xs])])]).

list_of(Gen) ->
    ?LAZY(
    oneof([[], [Gen|list_of(Gen)]])).

atom_list() ->
    list_of(atom()).

one_atom_list() ->
    ?LET(X, atom(), list_of(X)).

member(_, []) ->
    false;
member(X, [X|_]) ->
    true;
member(X, [_|Xs]) ->
    member(X, Xs).
