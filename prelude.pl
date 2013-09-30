:- module(prelude, [new_function/4, apply/4, apply_fun/4, is_fun/1, noteq/2, not_unifiable/2, solve/1]).

:- dynamic(is_function/4).

:- meta_predicate new_function(?, ?, ?, :).
new_function(Mod, Fun, Arity, Apply) :-
    assertz(is_function(Mod, Fun, Arity, Apply)).

:- new_function(erlang, not, 1, erlang_not).
erlang_not(true, false).
erlang_not(false, true).

apply(Mod, Fun, Res, Args) :-
    is_function(Mod, Fun, Arity, Apply),
    length(Args, Arity),
    !,
    apply(Apply, [Res|Args]).
apply(Mod, Fun, _, Args) :-
    length(Args, Arity),
    format("*** Unknown function ~p:~p/~p~n", [Mod, Fun, Arity]),
    trace,
    fail.

apply_fun(_, fun(Mod, Fun, Arity), Res, Args) :-
    !,
    length(Args, Arity),
    apply(Mod, Fun, Res, Args).
apply_fun(Mod, thunk(Fun, Xs), Res, Ys) :-
    !,
    append(Xs, Ys, Zs),
    apply_fun(Mod, Fun, Res, Zs).
apply_fun(Mod, Fun, Res, Args) :-
    apply(Mod, Fun, Res, Args).

is_fun(fun(_,_,_)).
is_fun(thunk(_,_)).

not_unifiable(X, Y) :-
    \+ X = Y.

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

solve(Goal) :-
    call(Goal),
    instantiate(Goal).

instantiate(apply(_, _, Res, Args)) :-
    %% Only one solution.
    term([Res|Args]),
    !.

term(a).
term(b).
term(0).
term(1).
term(true).
term(false).
term([]).
term([X|Xs]) :- term(X), term(Xs).
term(tuple(Xs)) :- term(Xs).
