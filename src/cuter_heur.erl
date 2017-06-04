%% -*- erlang-indent-level: 2 -*-
%%------------------------------------------------------------------------------
-module(cuter_heur).
-type state() :: term().
-type heap_elem() :: term().
-callback new(pid()) -> state().
-callback update_mfas([mfa()], state()) -> state().
-callback compare(heap_elem(), heap_elem(), state()) -> boolean().
