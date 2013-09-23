-module(symbolic_erlang).
-compile(export_all).

is_integer(X) ->
    {guard, is_integer, [X]}.
'>='(X, Y) ->
    {guard, '>=', [X, Y]}.
'and'(X, Y) ->
    {guard, 'and', [X, Y]}.
