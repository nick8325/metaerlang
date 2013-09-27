%% Translate pure Erlang to Prolog.
-module(prolog).
-compile(export_all).

translate(Mod) ->
    Clauses =
    lists:concat(
    [ translate(Mod, Fun, Arity)
      || {Fun, Arity} <- meta:exports(Mod) ]),
    
    [ ":- use_module(prelude, [apply/4, noteq/2]).\n",
      ":- assert(prelude:is_module(", atom_to_list(Mod), ")).\n",
      pretty(Clauses) ].

pretty(Clauses) ->
    lists:map(fun pretty_clause/1, Clauses).
pretty_clause({Name, Args, Body}) ->
    put(vars, gb_trees:empty()),
    put(id, 0),
    [ "'", atom_to_list(Name), "'",
      brack(comma(lists:map(fun pretty_exp/1, Args))), " :-\n",
      pretty_exp(Body), ".\n" ].

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
    Name = list_to_atom(lists:flatten(
               io_lib:format("~p:~p/~p", [Mod, Fun, Arity]))),
    Exp = meta:apply(meta_runtime, Mod, Fun, Vars),
    {Res, Clause} = expr(Exp),
    [ {Name, [Res|Vars], Clause},
      {apply, [Fun, Res, Vars],
       {call, Name, [Res|Vars]}} ].

expr(Exp) ->
    expr(Exp, meta_runtime:new_var()).

expr({'case', Vars, Clauses}, Res) ->
    {Res, clauses(Vars, Clauses, Res)};
expr(Lit, _) when is_integer(Lit); is_atom(Lit); is_list(Lit) ->
    {Lit, true()};
expr(Var={var,_}, _) ->
    {Var, true()};
expr({failure}, Res) ->
    {Res, false()};
expr({apply, Mod, Fun, Args}, Res) ->
    {VArgs, Clause} = exprs(Args),
    {Res, seq([Clause, {call, apply, [Mod, Fun, Res, VArgs]}])};
expr({tuple, Tuple}, _) ->
    {Res, Clause} = exprs(Tuple),
    {{functor, tuple, Res}, Clause};
expr(Exp, _) ->
    io:format("*** Unknown expression ~p~n", [Exp]),
    false().

exprs(Exps) ->
    {Res, Clauses} = lists:unzip(lists:map(fun expr/1, Exps)),
    {Res, seq(Clauses)}.

clauses(_, [], _) ->
    false();
clauses(Vars, [{clause, Patts, Guard, Body}|Clauses], Res) ->
    {Res1, Expr} = expr(Body(), Res),
    choice([match(Vars, Patts, guard(Guard), seq([Expr, unify(Res, Res1)])),
            seq([invert_match(match(Vars, Patts, guard(Guard), true())),
                 clauses(Vars, Clauses, Res)])]).

match(Vars, Patts, Guard, Body) ->
    lists:foldl(fun lett/2, seq([Guard, Body]),
                    lists:zip(Patts, Vars)).

lett({X={var, _}, T}, U) ->
    io:format("~p ~p ~p -> ~p~n", [X, T, U, subst(X, T, U)]),
    subst(X, T, U);
lett({T, U}, V) ->
    seq([unify(T, U), V]).

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

invert_match({seq, Xs}) ->
    choice(lists:map(fun invert_match/1, Xs));
invert_match({choice, Xs}) ->
    seq(lists:map(fun invert_match/1, Xs));
invert_match({unify, X, Y}) ->
    disunify(X, Y).

disunify(X, Y) ->
    {V1, C1} = expr(X),
    {V2, C2} = expr(Y),
    seq(
      [ C1, C2, {call, noteq, [V1, V2]} ]).

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
sequence(Op, CoOp, [T={CoOp, []}|_], Ys) ->
    {CoOp, []};
sequence(Op, CoOp, [X|Xs], Ys) ->
    sequence(Op, CoOp, Xs, [X|Ys]).

test() ->
    meta:c(test),
    file:write_file("test.pl", translate(test)).
