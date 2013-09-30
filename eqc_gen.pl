:- use_module(prelude).

:- new_function(eqc_gen, bind, 2, bind).
:- new_function(eqc_gen, suchthat, 2, suchthat).
:- new_function(eqc_gen, oneof, 1, oneof).
:- new_function(eqc_gen, elements, 1, elements).

bind(bind(Gen, F), Gen, F).
suchthat(suchthat(Gen, P), Gen, P).
oneof(oneof(Xs), Xs).
elements(elements(Xs), Xs).

in(X, Gen) :-
    in(X, Gen, _).

in(X, bind(Gen, F), P1*P2) :-
    !,
    in(Y, Gen, P1),
    apply_fun(eqc_gen, F, Gen1, [Y]),
    in(X, Gen1, P2).
in(X, suchthat(Gen, Pred), P) :-
    !,
    apply_fun(eqc_gen, Pred, true, [X]),
    in(X, Gen, P).
in(X, oneof(Xs), P/N) :-
    !,
    member(Gen, Xs),
    length(Xs, N),
    in(X, Gen, P).
in(X, elements(Xs), 1/N) :-
    !,
    member(X, Xs),
    length(Xs, N).
in(X, [Y|Ys], P1*P2) :-
    !,
    X = [Z|Zs],
    in(Z, Y, P1),
    in(Zs, Ys, P2).
in(X, X, 1).

prob(X, Gen, P) :-
    findall(P, in(X, Gen, P), Probs),
    sum(Probs, P).
sum([], 0).
sum([P|Ps], Total) :-
    N is P,
    sum(Ps, Rest),
    Total is N + Rest.
