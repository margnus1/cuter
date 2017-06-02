%% -*- erlang-indent-level: 2 -*-
%%------------------------------------------------------------------------------
-module(cuter_heur).
-type state() :: term().
-type heap_elem() :: term().
-callback new() -> state().
-callback update_mfas(state(), [mfa()]) -> state().
-callback compare(heap_elem(), heap_elem(), state()) -> boolean().
