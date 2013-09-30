%% Translate pure Erlang to Prolog.
-module(prolog).
-compile(export_all).

c(Mod) ->
    c(Mod, [report]).
c(Mod, Opts) ->
    meta:c(Mod, Opts),
    file:write_file(atom_to_list(Mod) ++ ".pl", translate(Mod)).

translate(Mod) ->
    Clauses =
    lists:flatten(
    [ translate(Mod, Fun, Arity)
      || {Fun, Arity} <- meta:exports(Mod) ]),

    [":- use_module(prelude).\n",
     ":- discontiguous(apply/3).\n",
     ":- new_module(" ++ atom_to_list(Mod), ", apply).\n\n",
     "apply(fun(Mod, Fun, Arity), Res, Args) :- \n",
     "    length(Args, Arity), apply(Mod, Fun, Res, Args).\n\n",
     pretty(Clauses) ].

pretty(Clauses) ->
    lists:map(fun pretty_clause/1, Clauses).
pretty_clause({assert, Name, Args, Body}) ->
    put(vars, gb_trees:empty()),
    put(id, 0),
    [ "'", atom_to_list(Name), "'",
      brack(comma(lists:map(fun pretty_exp/1, Args))), " :-\n",
      pretty_exp(Body), ".\n\n" ].

pretty_exp({seq, []}) ->
    "true";
pretty_exp({seq, Xs}) ->
    brack(comma(lists:map(fun pretty_exp/1, Xs)));
pretty_exp({choice, []}) ->
    "fail";
pretty_exp({choice, Xs}) ->
    brack(semicolon(lists:map(fun pretty_exp/1, Xs)));
pretty_exp({unify, X, Y}) ->
    brack([ pretty_exp(X), " = ", pretty_exp(Y) ]);
pretty_exp({call, Fun, Args}) ->
    [ "'", atom_to_list(Fun), "'",
      brack(comma(lists:map(fun pretty_exp/1, Args))) ];
pretty_exp(Var={var, _}) ->
    show_var(Var);
pretty_exp(N) when is_integer(N) ->
    integer_to_list(N);
pretty_exp(X) when is_atom(X) ->
    "'" ++ atom_to_list(X) ++ "'";
pretty_exp({functor, F, []}) ->
    pretty_exp(F);
pretty_exp({functor, F, Args}) ->
    [pretty_exp(F), brack(comma(lists:map(fun pretty_exp/1, Args)))];
pretty_exp([]) ->
    "[]";
pretty_exp([X|Xs]) ->
    ["[", pretty_exp(X), "|", pretty_exp(Xs), "]"].

show_var(Var) ->
    Vars = get(vars),
    case gb_trees:lookup(Var, Vars) of
        none ->
            Id = get(id),
            put(id, Id+1),
            put(vars, gb_trees:insert(Var, Id, Vars));
        {value, Id} -> ok
    end,
    "X" ++ integer_to_list(Id).

brack(Xs) ->
    ["(", Xs, ")"].
comma(Xs) ->
    sep(", ", Xs).
semicolon(Xs) ->
    sep(";\n", Xs).
sep(_, [X]) ->
    X;
sep(S, [X|Xs]) ->
    [X,S|sep(S, Xs)].

translate(Mod, Fun, Arity) ->
    Vars = [meta_runtime:new_var() || _ <- lists:seq(1, Arity)],
    Name = list_to_atom(atom_to_list(Mod) ++ ":" ++
                        atom_to_list(Fun) ++ "/" ++
                        integer_to_list(Arity)),
    Exp = meta:apply(meta_runtime, Mod, Fun, Vars),
    {Res, Clause} = expr(Exp),
    [ assert(Name, [Res|Vars], Clause),
      assert(apply, [Fun, Res, Vars],
             {call, Name, [Res|Vars]}) ].

assert(Name, Vars, {choice, Xs}) ->
    [assert(Name, Vars, X) || X <- Xs];
assert(Name, Vars, E) ->
    {assert, Name, Vars, E}.


expr(Exp) ->
    expr(Exp, meta_runtime:new_var()).

expr({'case', Vars, Clauses}, Res) ->
    {Res, clauses(Vars, Clauses, Res)};
expr(Lit, _) when is_integer(Lit); is_atom(Lit); Lit == [] ->
    {Lit, true()};
expr([X|Xs], _) ->
    {XR, XC} = expr(X),
    {XsR, XsC} = expr(Xs),
    {[XR|XsR], seq([XC, XsC])};
expr(Var={var,_}, _) ->
    {Var, true()};
expr({failure}, Res) ->
    {Res, false()};
expr({apply, Mod, Fun, Args}, Res) ->
    {VArgs, Clause} = exprs(Args),
    {Res, seq([Clause, {call, apply, [Mod, Fun, Res, VArgs]}])};
expr({apply, Fun, Args}, Res) ->
    {VArgs, Clause} = exprs(Args),
    {Res, seq([Clause, {call, apply, [Fun, Res, VArgs]}])};
expr({tuple, Tuple}, _) ->
    {Res, Clause} = exprs(Tuple),
    {{functor, tuple, Res}, Clause};
expr({alias, X1, X2}, Res) ->
    {X1R, X1C} = expr(X1, Res),
    {X2R, X2C} = expr(X2, Res),
    {X1R, seq([X1C, X2C, unify(X1R, X2R)])};
expr({'fun', Mod, Fun, Arity}, _) ->
    {Res, Clause} = exprs([Mod, Fun, Arity]),
    {{functor, 'fun', Res}, Clause};
expr(Exp, _) ->
    io:format("*** Unknown expression ~p~n", [Exp]),
    false().

exprs(Exps) ->
    {Res, Clauses} = lists:unzip(lists:map(fun expr/1, Exps)),
    {Res, seq(Clauses)}.

clauses(Vars, Clauses, Res) ->
    clauses(Vars, Clauses, Res, true()).
clauses(_, [], _, _) ->
    false();
clauses(Vars, [{clause, Patts, Guard, Body}|Clauses], Res, PrevGuard) ->
    {Res1, Expr} = expr(Body(), Res),
    NextGuard = seq([guard(Guard),
                     choice([invert_match(fun not_unifiable/2,
                                          match(Vars, Patts, true(), true())),
                             match(Vars, Patts, invert_match(fun separable/2, guard(Guard)), true())])]),
    choice([match(Vars, Patts, guard(Guard), seq([PrevGuard, Expr, unify(Res, Res1)])),
            clauses(Vars, Clauses, Res, NextGuard)]).

match(Vars, Patts, Guard, Body) ->
    lists:foldl(fun lett/2, seq([Guard, Body]),
                    lists:zip(Patts, Vars)).

lett({X={var, _}, T}, U) ->
    subst(X, T, U);
lett({T, U}, V) ->
    {_, Clause} = expr({alias, T, U}),
    seq([Clause, V]).

subst(X, T, {seq, Xs}) ->
    seq(subst(X, T, Xs));
subst(X, T, {choice, Xs}) ->
    choice(subst(X, T, Xs));
subst(X, T, {unify, U, V}) ->
    {unify, subst(X, T, U), subst(X, T, V)};
subst(X, T, {call, F, Args}) ->
    {call, F, subst(X, T, Args)};
subst(X, T, {functor, F, Args}) ->
    {functor, F, subst(X, T, Args)};
subst(X, T, [U|Us]) ->
    [subst(X, T, U)|subst(X, T, Us)];
subst(X, T, X) ->
    T;
subst(_, _, T) ->
    T.

invert_match(Disunify, {seq, Xs}) ->
    choice([ invert_match(Disunify, X) || X <- Xs ]);
invert_match(Disunify, {choice, Xs}) ->
    seq([ invert_match(Disunify, X) || X <- Xs ]);
invert_match(Disunify, {unify, X, Y}) ->
    Disunify(X, Y).

separable(X, Y) ->
    {V1, C1} = expr(X),
    {V2, C2} = expr(Y),
    seq(
      [ C1, C2, {call, noteq, [V1, V2]} ]).
not_unifiable(X, Y) ->
    {V1, C1} = expr(X),
    {V2, C2} = expr(Y),
    seq(
      [ C1, C2, {call, not_unifiable, [V1, V2]} ]).

guard(true) ->
    true();
guard(false) ->
    false();
guard({apply, erlang, '=:=', [X, Y]}) ->
    {V1, C1} = expr(X),
    {V2, C2} = expr(Y),
    seq([ C1, C2, unify(V1, V2)]);
guard(Guard) ->
    io:format("*** Unknown guard ~p~n", [Guard]),
    false().

true() ->
    seq([]).
seq(Xs) ->
    smart(seq, choice, Xs).
false() ->
    choice([]).
choice(Xs) ->
    smart(choice, seq, Xs).
unify(X, X) ->
    true();
unify(X, Y) ->
    {unify, X, Y}.

smart(Op, CoOp, Xs) ->
    Ys = lists:concat([ flatten(Op, X) || X <- Xs ]),
    sequence(Op, CoOp, Ys, []).

flatten(Op, {Op, Xs}) ->
    Xs;
flatten(_, X) ->
    [X].

sequence(_, _, [], [X]) ->
    X;
sequence(Op, _, [], Ys) ->
    {Op, lists:reverse(Ys)};
sequence(_, CoOp, [{CoOp, []}|_], _) ->
    {CoOp, []};
sequence(Op, CoOp, [X|Xs], Ys) ->
    sequence(Op, CoOp, Xs, [X|Ys]).
