:- use_module(library(dcg/basics)).
:- use_module(library(lists)).

% +-------------------+
% | General utilities |
% +-------------------+

index_of(X, [X|_], 0).
index_of(X, [_|Vs], I) :-
  index_of(X, Vs, IMinus1),
  I is IMinus1 + 1.

set_at(0, V, [_|Xs], [V|Xs]).
set_at(I, V, [X|Xs], [X|Ys]) :-
  I > 0,
  IMinus1 is I - 1,
  set_at(IMinus1, V, Xs, Ys).

swap(0, 0, Xs, Xs) :- !.
swap(0, J, [X|Xs], [Y|Ys]) :-
  J > 0,
  JMinus1 is J - 1,
  nth0(JMinus1, Xs, Y),
  set_at(JMinus1, X, Xs, Ys),
  !.
swap(I, 0, Xs, Ys) :-
  swap(0, I, Xs, Ys),
  !.
swap(I, J, [X|Xs], [X|Ys]) :-
  IMinus1 is I - 1,
  JMinus1 is J - 1,
  swap(IMinus1, JMinus1, Xs, Ys).

middle(Xs, X) :-
  length(Xs, L),
  I is div(L, 2),
  nth0(I, Xs, X).

% +-------------------------+
% | Solution to the problem |
% +-------------------------+

% Holds if the given rule applies to the given update (a list of numbers).
rule_applies(rule(X, Y), Update) :-
  index_of(X, Update, I), index_of(Y, Update, J) -> !, I < J; true.

% Holds if all rules applies to the given update.
rules_apply([], _).
rules_apply([Rule|Rules], Update) :-
  rule_applies(Rule, Update), rules_apply(Rules, Update).

% Applies a single rule to the given update.
apply_rule(rule(X, Y), Update, Result) :-
  index_of(X, Update, I), index_of(Y, Update, J), I > J -> swap(I, J, Update, Result); Result = Update.

% Applies all rules sequentially to the update (once).
apply_rules([], Update, Update).
apply_rules([Rule|Rules], Update, Result) :-
  apply_rule(Rule, Update, Update2),
  apply_rules(Rules, Update2, Result).

% Iteratively applies all rules until the result no longer changes (i.e. performs a fixpoint computation).
fix_rules(Rules, Update, Result) :-
  apply_rules(Rules, Update, Update2),
  (Update = Update2 -> Result = Update; fix_rules(Rules, Update2, Result)).

% Computes the part 1 solution.
solve_part1(input(Rules, Updates), Part1) :-
  findall(X, (member(Update, Updates), rules_apply(Rules, Update), middle(Update, X)), Xs),
  sumlist(Xs, Part1).

% Computes the part 2 solution.
solve_part2(input(Rules, Updates), Part2) :-
  findall(X, (member(Update, Updates), \+ rules_apply(Rules, Update), fix_rules(Rules, Update, Result), middle(Result, X)), Xs),
  sumlist(Xs, Part2).

% +---------------------------+
% | DCG for parsing the input |
% +---------------------------+

dcg_input(input(Rules, Updates)) --> dcg_rules(Rules), dcg_updates(Updates).

dcg_rules([])           --> eol.
dcg_rules([Rule|Rules]) --> dcg_rule(Rule), dcg_rules(Rules).

dcg_rule(rule(X, Y)) --> number(X), "|", number(Y), eol.

dcg_updates([])               --> eol.
dcg_updates([Update|Updates]) --> dcg_update(Update), dcg_updates(Updates).

dcg_update([])         --> eol.
dcg_update([X])        --> number(X), eol.
dcg_update([X1,X2|Xs]) --> number(X1), ",", dcg_update([X2|Xs]).

% +--------------+
% | Main program |
% +--------------+

read_input(Path, Input) :-
  phrase_from_file(dcg_input(Input), Path).

main :-
  current_prolog_flag(argv, [Cmd|Args]),
  (
    Args = [] -> write('Usage: '), write(Cmd), writeln(' <path to input>');
    Args = [InputPath|_] ->
      read_input(InputPath, Input),

      solve_part1(Input, Part1),
      write('Part 1: '), write(Part1), nl,

      solve_part2(Input, Part2),
      write('Part 2: '), write(Part2), nl
  ).
