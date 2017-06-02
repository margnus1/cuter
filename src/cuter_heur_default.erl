%% -*- erlang-indent-level: 2 -*-
%%------------------------------------------------------------------------------
-module(cuter_heur_default).
-behaviour(cuter_heur).

-export([new/0, update_mfas/2, compare/3]).

-export_type([state/0]).

-type state() :: none.

-spec new() -> state().
-spec update_mfas(state(), [mfa()]) -> state().
-spec compare(_, _, state()) -> boolean().

new() -> none.
update_mfas(none, L) when is_list(L) -> none.
compare(A, B, none) -> A < B.
