:- use_module(prelude).

:- new_function(eqc_gen, bind, 2, bind).
:- new_function(eqc_gen, suchthat, 2, suchthat).
:- new_function(eqc_gen, oneof, 1, oneof).
:- new_function(eqc_gen, elements, 1, elements).

bind(bind(Gen, F), Gen, F).
suchthat(suchthat(Gen, P), Gen, P).
oneof(oneof(Xs), Xs).
elements(elements(Xs), Xs).

in(X, bind(Gen, F)) :-
    !,
    in(Y, Gen),
    apply_fun(eqc_gen, F, Gen1, [Y]),
    in(X, Gen1).
in(X, suchthat(Gen, P)) :-
    !,
    apply_fun(eqc_gen, P, true, [X]),
    in(X, Gen).
in(X, oneof(Xs)) :-
    !,
    member(Gen, Xs),
    in(X, Gen).
in(X, elements(Xs)) :-
    !,
    member(X, Xs).
in(X, [Y|Ys]) :-
    !,
    X = [Z|Zs],
    in(Z, Y),
    in(Zs, Ys).
in(X, X).
