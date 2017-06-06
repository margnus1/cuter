%% -*- erlang-indent-level: 2 -*-
%%------------------------------------------------------------------------------
-module(cuter_heur_errdepth).
-behaviour(cuter_heur).

-export([new/1, update_mfas/2, compare/3]).

-export_type([state/0]).

-include("include/cuter_macros.hrl").

-type errdepth() :: inf | non_neg_integer().
%% -type tag() :: cuter_cerl:tagID().
-type nodedepths() :: array:array(errdepth()).
-type fundepths() :: #{mfa() => errdepth()}.
-type callers() :: #{mfa() => ordset:ordset(mfa())}.

-record(st, {
          codeserver :: pid(),
          callers    :: callers(),
          nodedepths :: nodedepths(),
          fundepths  :: fundepths()
         }).
-type state() :: #st{}.
-spec new(pid()) -> state().
-spec update_mfas([mfa()], state()) -> state().
-spec compare(_, _, state()) -> boolean().

%% -record(vc, {
%%          }).
-type letrecs() :: #{{atom(), arity()} => errdepth()}.
-record(vs, {
          mfa :: mfa(),
          lrs = #{} :: letrecs(),
          depth :: errdepth(),
          badmatch_depth :: errdepth() | undefined,
          state      :: state()
         }).

new(Codeserver) ->
  #st{callers=#{}, nodedepths=array:new(), fundepths=#{},
      codeserver=Codeserver}.

update_mfas(MFAs, Old) ->
  %% TODO: Deal with updates (clear fundepths; add deps of those to wq)
  process(wq_new(MFAs), update_callers(MFAs, Old)).

compare(AElem = {AVis, _, ATag, _}, BElem = {BVis, _, BTag, _}, State) ->
  ADepth = get_nodedepth(ATag, State),
  BDepth = get_nodedepth(BTag, State),
  {AVis, ADepth, AElem} < {BVis, BDepth, BElem}.

-ifdef(NOTDEF).
pp(MFA, State) ->
  {AST0, _Exported} = get_code(MFA, State),
  AST1 = cerl:add_ann([{depth, get_fundepth(MFA, State)}], pp_ann(AST0, State)),
  io:format("~s~n", [cerl_prettypr:format(AST1)]).

pp_annss(Nodess, St) -> [[pp_ann(Node, St) || Node <- Nodes] || Nodes <- Nodess].
pp_ann(Node, St) ->
  Ann = pp_ann_filter(cerl:get_ann(Node), St),
  case cerl:subtrees(Node) of
    [] -> cerl:set_ann(Node, Ann); % Sic on arg order (cerl lib idiosyncrasy)
    Subtrees ->
      cerl:ann_make_tree(Ann, cerl:type(Node), pp_annss(Subtrees, St))
  end.

pp_ann_filter([A={?BRANCH_TAG_PREFIX, This}|Anns], St) ->
  [A, {depth, get_nodedepth(This, St)}|pp_ann_filter(Anns, St)];
pp_ann_filter([A={next_tag,{?BRANCH_TAG_PREFIX, Next}}|Anns], St) ->
  [A, {next_depth, get_nodedepth(Next, St)}|pp_ann_filter(Anns, St)];
pp_ann_filter([{file,_}|Anns], St) -> pp_ann_filter(Anns, St);
pp_ann_filter([Line|Anns], St) when is_integer(Line) -> pp_ann_filter(Anns, St);
pp_ann_filter([Other|Anns], St) -> [Other|pp_ann_filter(Anns, St)];
pp_ann_filter([], _St) -> [].
-endif.

update_callers(MFAs, State0) ->
  lists:foldl(fun(MFA, State1=#st{callers = CM0}) ->
                  State1#st{callers=add_callers(get_callees(MFA, State1),
                                                MFA, CM0)}
              end, State0, MFAs).

add_callers([], _Caller, Callers) -> Callers;
add_callers([Callee|Callees], Caller, Callers0) ->
  Callers =
    case Callers0 of
      #{Callee := Set} -> Callers0#{Callee := ordsets:add_element(Caller, Set)};
      #{} -> Callers0#{Callee => [Caller]}
    end,
  add_callers(Callees, Caller, Callers).

%% TODO: Deal with mocking name resolution
%% TODO: Filter out letrec-defined functions
get_callees(MFA={M,_,_}, State) ->
  {AST, _Exported} = get_code(MFA, State),
  Callees = callees(AST, ordsets:new()),
  %% Module-qualify local calls
  ordsets:from_list(lists:map(fun({F,A}) -> {M,F,A}; (O) -> O end, Callees)).

calleesss(Nodess, Acc) -> lists:foldl(fun calleess/2, Acc, Nodess).
calleess(Nodes, Acc) -> lists:foldl(fun callees/2, Acc, Nodes).
callees(Node, Acc0) ->
  Acc1 = calleesss(cerl:subtrees(Node), Acc0),
  case resolve_call(Node) of
    no -> Acc1;
    {yes, Target} -> ordsets:add_element(Target, Acc1)
  end.

process(WQ0, State0) ->
  case wq_out(WQ0) of
    empty -> State0;
    {MFA, WQ1} ->
      {AST, _Exported} = get_code(MFA, State0),
      %% case MFA of {vs,len,_} ->
      %%     io:fwrite("~s~n", [cerl_prettypr:format(AST)])
      %% ; _ -> ok end,
      VS = #vs{mfa=MFA, depth=inf, state=State0},
      %% TODO: Are there recursive letrecs? In that case, we need to
      %% fixpoint-loop.
      #vs{depth=Depth, state=State1} = visit_node(cerl:fun_body(AST), VS),
      case update_fundepth(MFA, Depth, State1) of
        unchanged -> process(WQ1, State1);
        {changed, State = #st{callers=Callers}} ->
          %% TODO: Do sth about external calls to internal functions
          WQ = lists:foldl(fun wq_in/2, WQ1, maps:get(MFA, Callers, [])),
          process(WQ, State)
      end
  end.

visit_nodess(Nodess, DepthStateTuple) ->
  lists:foldr(fun visit_nodes/2, DepthStateTuple, Nodess).

visit_nodes(Nodes, DepthStateTuple) ->
  lists:foldr(fun visit_node/2, DepthStateTuple, Nodes).

visit_node(Node, VS0=#vs{depth=ExitDepth}) ->
  #tags{this=undefined, next=undefined} = get_tags(Node),
  VS = #vs{depth=Depth} =
    case cerl:type(Node) of
      'case' ->
        Clauses = cerl:case_clauses(Node),
        #vs{depth=ExitDepth, badmatch_depth=Depth0} = VS1 =
          visit_clauses(Clauses, VS0#vs{badmatch_depth=0}),
        visit_node(cerl:case_arg(Node),
                   VS1#vs{depth=Depth0, badmatch_depth=undefined});
        %% visit_casey(cerl:case_arg(Node), cerl:case_clauses(Node), VS0);
      'try' ->
        VS1 = visit_node(cerl:try_arg(Node), VS0),
        %% TODO: The full behaviour of try
        visit_node(cerl:try_body(Node), VS1);
        %% error({notimpl,cerl:type(Node)});
      'fun' ->
        (visit_node(cerl:fun_body(Node), VS0#vs{depth=inf})
        )#vs{depth=ExitDepth};
      letrec ->
        VS1 = visit_letrec_defs(cerl:letrec_defs(Node), VS0),
        visit_node(cerl:letrec_body(Node), VS1#vs{depth=ExitDepth});
      clause -> error(nothere);
      _ ->
        %% Non-branching case
        %% Assume the subtrees are executed in sequence
        visit_nodess(cerl:subtrees(Node), VS0)
    end,
  case lookup_call(Node, VS) of
    no -> VS;
    {yes, CallDepth} ->
      VS#vs{depth=min(CallDepth, Depth)}
  end.

%% visit_casey(Arg, Clauses, VS0=#vs{depth=ExitDepth}) ->
%%   #vs{depth=ExitDepth, badmatch_depth=Depth0} = VS1 =
%%     visit_clauses(Clauses, VS0#vs{badmatch_depth=0}),
%%   visit_node(Arg, VS1#vs{depth=Depth0, badmatch_depth=undefined}).

lookup_call(Node, #vs{mfa={M,_,_}, state=State, lrs=LRs}) ->
  case resolve_call(Node) of
    no -> no;
    {yes, FA={F,A}} ->
      case LRs of
        #{FA := Depth} -> {yes, Depth};
        #{} ->
          {yes, call_depth({M,F,A}, State)}
      end;
    {yes, MFA={_,_,_}} ->
      {yes, call_depth(MFA, State)}
  end.

visit_letrec_defs(LRDs, VS) ->
  lists:foldl(fun visit_letrec_def/2, VS, LRDs).

visit_letrec_def({Name, Def}, VS0) ->
  VS = #vs{depth=Depth, lrs=LRs} =
    visit_node(Def, VS0#vs{depth=inf}),
  VS#vs{lrs=maps:put(Name, Depth, LRs)}.

visit_clauses(Clauses, VS) ->
  lists:foldr(fun visit_clause/2, VS, Clauses).

%% TODO: Don't consider literal 'true' guards a branch
visit_clause(Node, VS0 = #vs{depth=ExitDepth, badmatch_depth=BadmatchDepth, state=State0}) ->
  #tags{this={?BRANCH_TAG_PREFIX, This}, next={?BRANCH_TAG_PREFIX, Next}} =
    get_tags(Node),
  State1 = update_nodedepth(Next, BadmatchDepth, State0),
  VS1 = #vs{depth=Depth1, state=State2} =
    visit_node(cerl:clause_body(Node), VS0#vs{state=State1}),
  State3 = update_nodedepth(This, Depth1, State2),
  Depth2 = case can_guard_fail(cerl:clause_guard(Node)) of
             false -> Depth1;
             true -> ed_add(min(Depth1,BadmatchDepth),1)
           end,
  VS2 = visit_node(cerl:clause_guard(Node), VS1#vs{depth=Depth2, state=State3}),
  VS = #vs{depth=Depth, badmatch_depth=BadmatchDepth} =
    visit_pats(cerl:clause_pats(Node), VS2#vs{badmatch_depth=BadmatchDepth}),
  %% %% +1 for the first pattern (fastest way to next clause)
  VS#vs{depth=ExitDepth,
        badmatch_depth=%% min(ed_add(BadmatchDepth,1), Depth)
          Depth}.

can_guard_fail(Node) ->
  not cerl:is_literal(Node) orelse cerl:concrete(Node) =/= 'true'.

visit_patss(Patss, VS) ->
  lists:foldr(fun visit_pats/2, VS, Patss).

visit_pats(Pats, VS) ->
  lists:foldr(fun visit_pat/2, VS, Pats).

visit_pat(Node, VS0) ->
  %% Assume the subpatterns are matched in sequence
  #vs{depth=Depth, badmatch_depth=BadmatchDepth, state=State0} = VS1 =
    visit_patss(cerl:subtrees(Node), VS0),
  case get_tags(Node) of
    #tags{this=undefined, next=undefined} ->
      %% Non-branching case
      VS1;
    #tags{this={?BRANCH_TAG_PREFIX, This}, next={?BRANCH_TAG_PREFIX, Next}} ->
      State1 = update_nodedepth(Next, BadmatchDepth, State0),
      State = update_nodedepth(This, Depth, State1),
      %% After 1 decision, we can either be in the next clause or continue match
      VS1#vs{depth=ed_add(min(BadmatchDepth, Depth),1), state=State}
  end.

-spec resolve_call(cerl:cerl()) -> no | {yes, mfa()} | {yes, {atom(), arity()}}.
resolve_call(Node) ->
  case cerl:type(Node) of
    primop ->
      case cerl:concrete(cerl:primop_name(Node)) of
        match_fail -> {yes, {erlang, error, 1}};

        bs_context_to_binary -> no
      end;
    apply ->
      case cerl:var_name(cerl:apply_op(Node)) of
        FA = {_,_} -> {yes, FA};
        Var when is_atom(Var) -> no
      end;
    call ->
      case {resolve_atom(cerl:call_module(Node)),
            resolve_atom(cerl:call_name(Node))}
      of
        {{yes, M}, {yes, F}} ->
          {yes, {M, F, length(cerl:call_args(Node))}};
        {_, _} -> no
      end;
    _Other -> no
  end.

resolve_atom(Node) ->
  case cerl:is_literal(Node) of
    false -> no;
    true ->
      case cerl:concrete(Node) of
        Atom when is_atom(Atom) -> {yes, Atom};
        _ -> no
      end
  end.

call_depth({erlang,error,1}, _State) -> 0;
call_depth({erlang,error,2}, _State) -> 0;
call_depth({erlang,exit,1},  _State) -> 0;
call_depth(MFA, State) ->
  get_fundepth(MFA, State).

get_tags(Node) ->
  cuter_cerl:get_tags(cerl:get_ann(Node)).

get_code(MFA={M,_,_}, #st{codeserver=Codeserver}) ->
  {ok, FC} = cuter_codeserver:load(Codeserver, M),
  {ok, Value} = cuter_codeserver:lookup_in_module_cache(MFA, FC),
  Value.

get_fundepth(MFA, #st{fundepths=FDepths}) ->
  maps:get(MFA, FDepths, inf).

update_fundepth(MFA, NewDepth, State = #st{fundepths=FDepths}) ->
  case maps:get(MFA, FDepths, inf) of
    NewDepth -> unchanged;
    _Old ->
      {changed, State#st{fundepths=FDepths#{MFA => NewDepth}}}
  end.

get_nodedepth(Tag, #st{nodedepths=NDs}) ->
  case array:get(Tag, NDs) of
    undefined -> error(badarg, [Tag]);
    Depth -> Depth
  end.

update_nodedepth(Tag, Depth, State=#st{nodedepths=NDs}) ->
  State#st{nodedepths=array:set(Tag, Depth, NDs)}.

ed_add(inf, _) -> inf;
ed_add(_, inf) -> inf;
ed_add(A, B) -> A + B.

%% Workqueue AST
wq_new(L) -> L.

wq_in(E, []) -> [E];
wq_in(E, [E|_]=Q) -> Q;
wq_in(E, [O|Q]) -> [O|wq_in(E,Q)].

wq_out([E|Q]) -> {E,Q};
wq_out([]) -> empty.
