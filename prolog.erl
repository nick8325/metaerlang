%% Translate pure Erlang to Prolog.
-module(prolog).
-compile(export_all).

c(Mod) ->
    c(Mod, [report]).
c(Mod, Opts) ->
    meta:c(Mod, Opts),
    file:write_file("erl_" ++ atom_to_list(Mod) ++ ".pl", translate(Mod)).

translate(Mod) ->
    Name = atom_to_list(Mod),
    Clauses =
    lists:flatten(
    [ translate(Mod, Fun, Arity)
      || {Fun, Arity} <- meta:exports(Mod) ]),

    [":- module(erl_", Name, ", [",
     comma([ [ show_atom(Fun), "/", integer_to_list(length(Args)) ]
           || {assert, Fun, Args, _} <- lists:flatten(Clauses) ]),
     "]).\n",
     ":- use_module(prelude).\n",
     "apply_fun(Fun, Res, Args) :- apply_fun(", Name, ", Fun, Res, Args).\n\n",
     pretty(Clauses) ].

pretty(Clauses) ->
    lists:map(fun pretty_clause/1, Clauses).
pretty_clause({goal, Goal}) ->
    [ ":- ", pretty_exp(Goal), ".\n" ];
pretty_clause({assert, Name, Args, Body}) ->
    put(vars, gb_trees:empty()),
    put(id, 0),
    [ show_atom(Name),
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
    [ show_atom(Fun),
      brack(comma(lists:map(fun pretty_exp/1, Args))) ];
pretty_exp(Var={var, _}) ->
    show_var(Var);
pretty_exp(N) when is_integer(N) ->
    integer_to_list(N);
pretty_exp(X) when is_atom(X) ->
    show_atom(X);
pretty_exp({functor, F, []}) ->
    pretty_exp(F);
pretty_exp({functor, F, Args}) ->
    [pretty_exp(F), brack(comma(lists:map(fun pretty_exp/1, Args)))];
pretty_exp([]) ->
    "[]";
pretty_exp([X|Xs]) ->
    ["[", pretty_exp(X), "|", pretty_exp(Xs), "]"].

show_atom(X) when is_atom(X) ->
    "'" ++ atom_to_list(X) ++ "'".

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
    Name = list_to_atom(atom_to_list(Mod) ++ ":" ++ atom_to_list(Fun)),
    Exp = meta:apply(meta_runtime, Mod, Fun, Vars),
    {Res, Clause} = expr(Exp),
    [ {goal, {call, new_function, [Mod, Fun, Arity, Name]}},
      assert(Name, [Res|Vars], Clause) ].

assert(Name, Vars, {choice, Xs}) ->
    [assert(Name, Vars, X) || X <- Xs];
assert(Name, Vars, E) ->
    {assert, Name, Vars, E}.

expr(Exp) ->
    expr(Exp, meta_runtime:new_var()).

expr_var(Exp) ->
    {Res, Clause} = expr(Exp),
    case Res of
        {var, _} ->
            {Res, Clause};
        _ ->
            Var = meta_runtime:new_var(),
            {Var, seq([Clause, unify(Var, Res)])}
    end.

expr({'case', Exprs, Clauses}, Res) ->
    {Vars, Clause} = exprs_var(Exprs),
    {Res, seq([Clause, clauses(Vars, Clauses, Res)])};
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
    {Res, seq([Clause, {call, apply_fun, [Fun, Res, VArgs]}])};
expr({tuple, Tuple}, _) ->
    {Res, Clause} = exprs(Tuple),
    {{functor, tuple, Res}, Clause};
expr({'fun', Mod, Fun, Arity}, _) ->
    {Res, Clause} = exprs([Mod, Fun, Arity]),
    {{functor, 'fun', Res}, Clause};
expr({thunk, Fun, Args}, _) ->
    {Res, Clause} = exprs([Fun, Args]),
    {{functor, thunk, Res}, Clause};
expr(Exp, _) ->
    io:format("*** Unknown expression ~p~n", [Exp]),
    false().

exprs(Exps) ->
    {Res, Clauses} = lists:unzip(lists:map(fun expr/1, Exps)),
    {Res, seq(Clauses)}.

exprs_var(Exps) ->
    {Res, Clauses} = lists:unzip(lists:map(fun expr_var/1, Exps)),
    {Res, seq(Clauses)}.

clauses(Vars, Clauses, Res) ->
    clauses(Vars, Clauses, Res, true()).
clauses(_, [], _, _) ->
    false();
clauses(Vars, [{clause, Patts, Guard, Body}|Clauses], Res, PrevGuard) ->
    {Res1, Expr} = expr(Body, Res),
    NextGuard = seq([guard(Guard),
                     choice([invert_match(fun not_unifiable/2,
                                          match(Vars, Patts, true(), true())),
                             match(Vars, Patts, invert_match(fun separable/2, guard(Guard)), true())])]),
    choice([match(Vars, Patts, guard(Guard), seq([PrevGuard, Expr, unify(Res, Res1)])),
            clauses(Vars, Clauses, Res, NextGuard)]).

match(Vars, Patts, Guard, Body) ->
    Binds = lists:zip(Patts, Vars),
    Binds1 = lists:concat(lists:map(fun flatten_binds/1, Binds)),
    lists:foldl(fun match/2, seq([Guard, Body]), Binds1).

flatten_binds({T, U}) ->
    {BindsT, T1} = flatten_patt(T),
    [{T1, U}|BindsT].

flatten_patt({alias, X={var,_}, T}) ->
    {Binds, T1} = flatten_patt(T),
    {[{X, T1}|Binds], X};
flatten_patt([T|U]) ->
    {BindsT, T1} = flatten_patt(T),
    {BindsU, U1} = flatten_patt(U),
    {BindsT ++ BindsU, [T1|U1]};
flatten_patt({tuple, T}) ->
    {BindsT, T1} = flatten_patt(T),
    {BindsT, {functor, tuple, T1}};
flatten_patt(X) ->
    {E, {seq, []}} = expr(X), % X should be a literal
    {[], E}.

match({X={var, _}, T}, Body) ->
    subst(X, T, Body);
match({T, U}, Body) ->
    seq([unify(T, U), Body]).

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
