:- module(prelude, [is_module/1, apply/4, noteq/2]).

:- dynamic(is_module/1).

apply(Mod, Fun, Res, Args) :-
    is_module(Mod),
    Mod:apply(Fun, Res, Args).

noteq(X, Y) :-
    not_var(X),
    not_var(Y),
    \+ (X = Y).

not_var([]).
not_var([_|_]).
not_var(a).
not_var(b).
