-module(lists_impl).
-compile(export_all).

seq(M, N) when is_integer(M), is_integer(N), M >= N ->
    [];
seq(M, N) when is_integer(M), is_integer(N) ->
    [M|seq(M+1, N)].
