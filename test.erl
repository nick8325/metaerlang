-module(test).
-compile(export_all).

member(_, []) ->
    false;
member(X, [X|_]) ->
    true;
member(X, [_|Xs]) ->
    member(X, Xs).

f(Xs) ->
    concat([Zs || Ys <- inits(Xs), Zs <- tails(Ys)]).

inits(Xs) ->
    map(fun reverse/1, tails(Xs)).

map(_F, []) ->
    [];
map(F, [X|Xs]) ->
    [F(X)|map(F, Xs)].

concat(Xs) ->
    concat([], Xs).
concat([], []) ->
    [];
concat([], [Xs|Xss]) ->
    concat(Xs, Xss);
concat([X|Xs], Xss) ->
    [X|concat(Xs, Xss)].

reverse(Xs) ->
    reverse(Xs, []).
reverse([], Ys) ->
    Ys;
reverse([X|Xs], Ys) ->
    reverse(Xs, [X|Ys]).

tails([]) ->
    [[]];
tails(Xs=[_|Ys]) ->
   [Xs|tails(Ys)].
