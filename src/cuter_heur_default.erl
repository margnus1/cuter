%% -*- erlang-indent-level: 2 -*-
%%------------------------------------------------------------------------------
-module(cuter_heur_default).
-behaviour(cuter_heur).

-export([new/1, update_mfas/2, compare/3]).

-export_type([state/0]).

-type state() :: none.

-spec new(pid()) -> state().
-spec update_mfas([mfa()], state()) -> state().
-spec compare(_, _, state()) -> boolean().

new(_Codeserver) -> none.
update_mfas(L, none) when is_list(L) -> none.
compare(A, B, none) -> A < B.
