-module(test).
-compile(export_all).

member(_, []) ->
    false;
member(X, [X|_]) ->
    true;
member(X, [_|Xs]) ->
    member(X, Xs).
