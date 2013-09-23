-module('symbolic!lists').
-compile(export_all).

seq(M, N) ->
    'symbolic!lists_impl':seq(M, N).
