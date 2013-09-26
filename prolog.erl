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
      brack(comma(lists:map(fun show_var/1, Args))), " :-\n",
      pretty_exp(Body), ".\n" ].
pretty_exp({choice, []}) ->
    "fail";
pretty_exp({choice, Xs}) ->
    brack(semicolon(lists:map(fun pretty_exp/1, Xs)));
pretty_exp({unify, X, Y}) ->
    brack([ pretty_exp(X), " = ", pretty_exp(Y) ]);
pretty_exp(true) ->
    "true";
pretty_exp(fail) ->
    "fail";
pretty_exp({call, Fun, Args}) ->
    [ "'", atom_to_list(Fun), "'",
      brack(comma(lists:map(fun pretty_exp/1, Args))) ];
pretty_exp({seq, []}) ->
    "true";
pretty_exp({seq, Xs}) ->
    brack(comma(lists:map(fun pretty_exp/1, Xs)));
pretty_exp(Var={var, _}) ->
    show_var(Var);
pretty_exp(N) when is_integer(N) ->
    integer_to_list(N);
pretty_exp(X) when is_atom(X) ->
    "'" ++ atom_to_list(X) ++ "'";
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
    Res = meta_runtime:new_var(),
    Name = list_to_atom(lists:flatten(
               io_lib:format("~p:~p/~p", [Mod, Fun, Arity]))),
    Exp = meta:apply(meta_runtime, Mod, Fun, Vars),
    FVar = meta_runtime:new_var(),
    VVar = meta_runtime:new_var(),
    [ {Name, [Res|Vars], expr(Exp, Res)},
      {apply, [FVar, Res, VVar],
       seq(
         [ unify(Fun, FVar),
           unify(Vars, VVar),
           {call, Name, [Res|Vars]} ])} ].

expr({'case', Vars, Clauses}, Res) ->
    choice(clauses(Vars, Clauses, Res));
expr(Lit, Res) when is_integer(Lit); is_atom(Lit); is_list(Lit) ->
    unify(Lit, Res);
expr(Var={var,_}, Res) ->
    unify(Var, Res);
expr({failure}, _) ->
    fail;
expr({apply, Mod, Fun, Args}, Res) ->
    {call, apply, [Mod, Fun, Res, Args]};
expr({tuple, Tuple}, Res) ->
    Vars = [meta_runtime:new_var() || _ <- lists:seq(1, length(Tuple))],
    seq(
     [ unify(Elem, Var) || {Elem, Var} <- lists:zip(Tuple, Vars) ] ++
     [ {call, tuple, [Res, Vars]} ]);
expr(Exp, _Res) ->
    io:format("*** Unknown expression ~p~n", [Exp]),
    fail.

clauses(Vars, Clauses, Res) ->
    clauses(Vars, Clauses, Res, true).
clauses(_, [], _, _) ->
    [];
clauses(Vars, [{clause, Patts, Guard, Body}|Clauses], Res, Failed) ->
    Match = match_clause(fun seq/1, fun choice/1, fun unify/2, Vars, Patts, Guard),
    NotMatch = match_clause(fun choice/1, fun seq/1, fun disunify/2, Vars, Patts, Guard),
    [ seq([Failed, Match, expr(Body(), Res)])
    | clauses(Vars, Clauses, Res, seq([Failed, NotMatch])) ].

disunify(X, Y) ->
    V1 = meta_runtime:new_var(),
    V2 = meta_runtime:new_var(),
    seq(
      [ expr(X, V1),
        expr(Y, V2),
        {call, noteq, [V1, V2]} ]).

match_clause(Seq, Choice, Unify, Vars, Patts, Guard) ->
    Seq(
     [ Unify(X, Y) || {X, Y} <- lists:zip(Vars, Patts) ] ++
     [ guard(Seq, Choice, Unify, Guard) ]).

guard(Seq, _Choice, _Unify, true) ->
    Seq([]);
guard(_Seq, Choice, _Unify, false) ->
    Choice([]);
guard(Seq, _Choice, Unify, {apply, erlang, '=:=', [X, Y]}) ->
    V1 = meta_runtime:new_var(),
    V2 = meta_runtime:new_var(),
    Seq(
     [ expr(X, V1),
       expr(Y, V2),
       Unify(V1, V2) ]);
guard(_, _, _, Guard) ->
    io:format("*** Unknown guard ~p~n", [Guard]),
    fail.

choice(Xs) ->
    {choice, Xs}.
unify(X, Y) ->
    {unify, X, Y}.
seq(Xs) ->
    {seq, Xs}.

test() ->
    meta:c(test),
    file:write_file("test.pl", translate(test)).
