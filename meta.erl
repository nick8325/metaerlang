-module(meta).
-export([start/0, start_1/0, c/1, c/2, apply/4, exports/1]).

base() ->
    [meta_transform, meta_runtime, cerl_extra, prolog].
builtins() ->
    [erlang, lists].

all_modules(Mods, Fun) ->
    [ Fun(Mod) || Mod <- Mods ],
    ok.

ensure_loaded() ->
    Mods =
        base() ++
        lists:map(fun meta_transform:meta_module_name/1, builtins()),
    all_modules(Mods, fun ensure_loaded/1).
ensure_loaded(Mod) ->
    ensure_loaded(Mod, meta_not_started).
ensure_loaded(Mod, Error) ->
    case code:ensure_loaded(Mod) of
        {error, _} ->
            error(Error);
        _ ->
            ok
    end.

start() ->
    compile_native(?MODULE),
    ?MODULE:start_1().
start_1() ->
    all_modules(base(), fun compile_native/1),
    all_modules(builtins(), fun compile_builtin/1).
compile_native(Mod) ->
    case compile:file(Mod, [report]) of
        {ok, _} ->
            code:purge(Mod),
            code:load_file(Mod);
        error ->
            exit(compile_failed)
    end.
compile_builtin(Mod) ->
    compile(list_to_atom("std_" ++ atom_to_list(Mod)),
            [report, {real_name, Mod}]).

c(Mod) ->
    c(Mod, [report]).
c(Mod, Opts) ->
    ensure_loaded(),
    compile(Mod, Opts).

compile(Mod, Opts) ->
    Opts1 = [{core_transform, meta_transform},
              no_error_module_mismatch,
              binary],

    case compile:file(Mod, Opts ++ Opts1) of
        {ok, Mod, Bin} ->
            Mod1 = meta_transform:meta_module_name(
                  proplists:get_value(real_name, Opts, Mod)),
            code:purge(Mod1),
            code:load_binary(Mod1, Mod1, Bin),
            ok;
        error ->
            error
    end.

apply(Runtime, Mod, Fun, Args) ->
    put(meta_transform:runtime_key(), Runtime),
    Mod1 = meta_transform:meta_module_name(Mod),
    case erlang:function_exported(Mod1, Fun, length(Args)) of
        true ->
            apply(Mod1, Fun, Args);
        false ->
            io:format("*** Unknown metafunction ~p:~p/~p~n",
                      [Mod, Fun, length(Args)]),
            Runtime:failure()
    end.

exports(Mod) ->
    Mod1 = meta_transform:meta_module_name(Mod),
    ensure_loaded(Mod1, {module_not_loaded, Mod}),
    erlang:get_module_info(Mod1, exports) --
        [{module_info, 0},
         {module_info, 1}].
