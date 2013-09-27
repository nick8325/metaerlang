:- module(prelude, [is_module/1, apply/4, noteq/2]).

:- dynamic(is_module/1).

apply(Mod, Fun, Res, Args) :-
    is_module(Mod),
    Mod:apply(Fun, Res, Args).

noteq(X, Y) :-
    nonvar(X), nonvar(Y), !,
    X =.. [F|Xs],
    Y =.. [G|Ys],
    (F \== G; noteq_list(Xs, Ys)).

noteq(X, Y) :-
    var(X), var(Y), X == Y, !, fail.

noteq(X, Y) :-
    nonvar(X), !,
    forbid_unifying(Y, X).
noteq(X, Y) :-
    nonvar(Y), !,
    forbid_unifying(X, Y).
noteq(X, Y) :-
    %% must have var(X), var(Y).
    forbid_unifying(X, Y),
    %% must make Y an attributed variable too -
    %% otherwise unifying X = Y is a no-op
    put_attr(Y, prelude, []).

noteq_list([], [_|_]).
noteq_list([_|_], []).
noteq_list([X|_], [Y|_]) :-
    noteq(X, Y).
noteq_list([_|Xs], [_|Ys]) :-
    noteq_list(Xs, Ys).

noteq_several(_X, []).
noteq_several(X, [Y|Ys]) :-
    noteq(X, Y),
    noteq_several(X, Ys).

forbid_unifying(X, T) :-
    get_forbidden(X, Xs),
    put_attr(X, prelude, [T|Xs]),
    true.

get_forbidden(X, Xs) :-
    get_attr(X, prelude, Xs), !.
get_forbidden(_X, []).

attr_unify_hook(Xs, Y) :-
    check_forbidden(Y),
    list_to_set(Xs, Ys),
    noteq_several(Y, Ys).

check_forbidden(X) :-
    attvar(X), !,
    get_forbidden(X, Xs),
    check_forbidden_list(X, Xs).
check_forbidden(_X).

check_forbidden_list(_X, []).
check_forbidden_list(X, [Y|Ys]) :-
    X \== Y,
    check_forbidden_list(X, Ys).

attribute_goals(X) -->
    {get_forbidden(X, Xs),
     list_to_set(Xs, Ys)},
    goals_list(X,Ys).
goals_list(_X,[]) -->
    [].
goals_list(X,[Y|Ys]) -->
    [X \= Y],
    goals_list(X, Ys).
