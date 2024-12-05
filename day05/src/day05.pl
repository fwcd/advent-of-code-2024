:- use_module(library(dcg/basics)).

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

      write('Input: '), write(Input), nl
  ).
