-module(std_erlang).
-compile(export_all).

'and'(false, X) when is_boolean(X) ->
    false;
'and'(true, X) when is_boolean(X) ->
    X.
