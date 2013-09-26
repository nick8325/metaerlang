-module(std_erlang).
-compile(export_all).

-compile({symbolic, is_integer/1}).
is_integer(X) ->
    {guard, is_integer, [X]}.

-compile({symbolic, '>='/2}).
'>='(X, Y) ->
    {guard, '>=', [X, Y]}.

-compile({symbolic, 'and'/2}).
'and'(X, Y) ->
    {guard, 'and', [X, Y]}.
