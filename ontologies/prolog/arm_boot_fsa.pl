%% ARM Boot FSA - SWI-Prolog Encoding
%% Generated: 2025-12-27
%% Usage: swipl -g "consult('arm_boot_fsa.pl'), run_tests, halt."
%%        swipl arm_boot_fsa.pl  (interactive)

:- module(arm_boot_fsa, [
    boot_state/1,
    transition/2,
    reachable/2,
    terminal/1,
    success/1,
    failure/1,
    initial/1,
    loading/1,
    execution/1,
    path_length/3,
    happy_path/1,
    run_tests/0
]).

%% ============================================================================
%% BOOT STATES (13 states)
%% ============================================================================

boot_state(power_on).
boot_state(rom_execution).
boot_state(bootcode_loading).
boot_state(bootcode_execution).
boot_state(startelf_loading).
boot_state(startelf_execution).
boot_state(kernel_loading).
boot_state(kernel_execution).
boot_state(boot_success).
boot_state(no_boot_media).
boot_state(firmware_corrupt).
boot_state(secure_boot_fail).
boot_state(hardware_fail).

%% ============================================================================
%% STATE CLASSIFICATION
%% ============================================================================

%% Terminal states (no outgoing transitions)
terminal(boot_success).
terminal(no_boot_media).
terminal(firmware_corrupt).
terminal(secure_boot_fail).
terminal(hardware_fail).

%% Success state
success(boot_success).

%% Failure states
failure(no_boot_media).
failure(firmware_corrupt).
failure(secure_boot_fail).
failure(hardware_fail).

%% Initial state
initial(power_on).

%% Loading states
loading(bootcode_loading).
loading(startelf_loading).
loading(kernel_loading).

%% Execution states
execution(rom_execution).
execution(bootcode_execution).
execution(startelf_execution).
execution(kernel_execution).

%% ============================================================================
%% TRANSITION RELATION (18 transitions)
%% ============================================================================

%% Happy path transitions
transition(power_on, rom_execution).
transition(rom_execution, bootcode_loading).
transition(bootcode_loading, bootcode_execution).
transition(bootcode_execution, startelf_loading).
transition(startelf_loading, startelf_execution).
transition(startelf_execution, kernel_loading).
transition(kernel_loading, kernel_execution).
transition(kernel_execution, boot_success).

%% Failure transitions
transition(rom_execution, no_boot_media).
transition(bootcode_loading, firmware_corrupt).
transition(bootcode_execution, hardware_fail).
transition(startelf_loading, firmware_corrupt).
transition(startelf_execution, hardware_fail).
transition(kernel_loading, firmware_corrupt).
transition(kernel_execution, hardware_fail).

%% Secure boot failure transitions (Pi4/Pi5)
transition(bootcode_loading, secure_boot_fail).
transition(startelf_loading, secure_boot_fail).
transition(kernel_loading, secure_boot_fail).

%% ============================================================================
%% REACHABILITY (Transitive Closure) - Using tabling for efficiency
%% ============================================================================

:- table reachable/2.

%% Base case: reflexivity
reachable(S, S) :- boot_state(S).

%% Inductive case: one step then reachable
reachable(S1, S3) :-
    transition(S1, S2),
    reachable(S2, S3).

%% ============================================================================
%% PATH FINDING
%% ============================================================================

%% Find a path between two states
path(S, S, [S]) :- boot_state(S).
path(S1, S3, [S1|Rest]) :-
    transition(S1, S2),
    path(S2, S3, Rest).

%% Path length
path_length(S1, S2, N) :-
    path(S1, S2, Path),
    length(Path, L),
    N is L - 1.

%% Shortest path (using findall and min)
shortest_path(S1, S2, N) :-
    findall(L, path_length(S1, S2, L), Lengths),
    min_list(Lengths, N).

%% ============================================================================
%% HAPPY PATH
%% ============================================================================

%% The happy path is the sequence of states leading to success
happy_path(Path) :-
    path(power_on, boot_success, Path),
    \+ (member(S, Path), failure(S)).

%% ============================================================================
%% QUERIES
%% ============================================================================

%% All states reachable from power_on
reachable_from_initial(S) :-
    reachable(power_on, S).

%% All failure states reachable
reachable_failures(Failures) :-
    findall(F, (failure(F), reachable(power_on, F)), Failures).

%% All terminal states reachable
reachable_terminals(Terminals) :-
    findall(T, (terminal(T), reachable(power_on, T)), Terminals).

%% States that can reach success
can_reach_success(S) :-
    reachable(S, boot_success).

%% States that can reach failure
can_reach_failure(S, F) :-
    failure(F),
    reachable(S, F).

%% ============================================================================
%% SAFETY PROPERTIES
%% ============================================================================

%% No state is both success and failure
success_failure_exclusive :-
    \+ (success(S), failure(S)).

%% All terminal states are either success or failure
terminal_classification :-
    forall(terminal(S), (success(S) ; failure(S))).

%% Terminal states have no outgoing transitions
terminal_absorbing :-
    \+ (terminal(S), transition(S, _)).

%% Non-terminal states have at least one successor
non_terminal_has_successor :-
    forall((boot_state(S), \+ terminal(S)), transition(S, _)).

%% ============================================================================
%% SECURE BOOT PROPERTIES
%% ============================================================================

%% Secure boot failure only from loading states
secure_boot_from_loading :-
    forall(transition(S, secure_boot_fail), loading(S)).

%% Hardware failure only from execution states
hardware_fail_from_execution :-
    forall(transition(S, hardware_fail), execution(S)).

%% ============================================================================
%% TESTS
%% ============================================================================

run_tests :-
    format("~n=== ARM Boot FSA - Prolog Tests ===~n~n"),

    % Test 1: Boot success reachable
    format("Test 1: Boot success reachable from power_on... "),
    (reachable(power_on, boot_success) -> format("PASS~n") ; format("FAIL~n")),

    % Test 2: All failures reachable
    format("Test 2: All failure states reachable... "),
    reachable_failures(Failures),
    length(Failures, 4),
    format("PASS (~w)~n", [Failures]),

    % Test 3: Happy path exists
    format("Test 3: Happy path exists... "),
    (happy_path(HP) -> format("PASS (~w)~n", [HP]) ; format("FAIL~n")),

    % Test 4: Happy path length is 9 states (8 transitions)
    format("Test 4: Happy path is 8 transitions... "),
    happy_path(Path),
    length(Path, PathLen),
    (PathLen =:= 9 -> format("PASS (9 states)~n") ; format("FAIL (~w states)~n", [PathLen])),

    % Test 5: Success/failure exclusive
    format("Test 5: Success/failure mutually exclusive... "),
    (success_failure_exclusive -> format("PASS~n") ; format("FAIL~n")),

    % Test 6: Terminal states absorbing
    format("Test 6: Terminal states are absorbing... "),
    (terminal_absorbing -> format("PASS~n") ; format("FAIL~n")),

    % Test 7: Secure boot from loading
    format("Test 7: SecureBootFail only from loading states... "),
    (secure_boot_from_loading -> format("PASS~n") ; format("FAIL~n")),

    % Test 8: Hardware fail from execution
    format("Test 8: HardwareFail only from execution states... "),
    (hardware_fail_from_execution -> format("PASS~n") ; format("FAIL~n")),

    % Test 9: Shortest path to success
    format("Test 9: Shortest path to success is 8... "),
    shortest_path(power_on, boot_success, ShortestSuccess),
    (ShortestSuccess =:= 8 -> format("PASS~n") ; format("FAIL (~w)~n", [ShortestSuccess])),

    % Test 10: Shortest path to no_boot_media
    format("Test 10: Shortest path to no_boot_media is 2... "),
    shortest_path(power_on, no_boot_media, ShortestNoBoot),
    (ShortestNoBoot =:= 2 -> format("PASS~n") ; format("FAIL (~w)~n", [ShortestNoBoot])),

    format("~n=== All tests completed ===~n").

%% ============================================================================
%% INTERACTIVE HELPERS
%% ============================================================================

%% Show all states
show_states :-
    format("Boot States:~n"),
    forall(boot_state(S), format("  ~w~n", [S])).

%% Show all transitions
show_transitions :-
    format("Transitions:~n"),
    forall(transition(S1, S2), format("  ~w -> ~w~n", [S1, S2])).

%% Show happy path
show_happy_path :-
    happy_path(Path),
    format("Happy Path: ~w~n", [Path]).

%% Show reachability from a state
show_reachable(S) :-
    format("States reachable from ~w:~n", [S]),
    forall(reachable(S, T), format("  ~w~n", [T])).

%% ============================================================================
%% MAIN
%% ============================================================================

:- initialization((
    format("ARM Boot FSA loaded.~n"),
    format("Run 'run_tests.' to verify properties.~n"),
    format("Run 'show_happy_path.' to see the success path.~n")
)).
