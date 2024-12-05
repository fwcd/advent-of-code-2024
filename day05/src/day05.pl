:- use_module(library(dcg/basics)).
:- use_module(library(lists)).

index_of(X, [X|_], 0).
index_of(X, [_|Vs], I) :-
  index_of(X, Vs, IMinus1),
  I is IMinus1 + 1.

middle(Xs, X) :-
  length(Xs, L),
  I is div(L, 2),
  nth0(I, Xs, X).

rule_applies(rule(X, Y), Update) :-
  index_of(X, Update, I), index_of(Y, Update, J) -> !, I < J; true.

rules_apply([], _).
rules_apply([Rule|Rules], Update) :-
  rule_applies(Rule, Update), rules_apply(Rules, Update).

solve_part1(input(Rules, Updates), Part1) :-
  findall(X, (member(Update, Updates), rules_apply(Rules, Update), middle(Update, X)), Xs),
  sumlist(Xs, Part1).

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
      write('Part 1: '), write(Part1), nl
  ).
