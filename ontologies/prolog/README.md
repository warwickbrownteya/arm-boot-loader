# ARM Boot FSA - SWI-Prolog Encoding

**Generated**: 2025-12-27
**Prolog**: SWI-Prolog 9.2.9
**Test Time**: <100ms

## Overview

This directory contains a complete logic programming implementation of the ARM bootloader finite state automaton in SWI-Prolog, with executable queries and test suite.

## Files

| File | Description |
|------|-------------|
| `arm_boot_fsa.pl` | Complete FSA module with tests |

## Quick Start

```bash
# Run tests
swipl -g "consult('arm_boot_fsa.pl'), run_tests, halt."

# Interactive mode
swipl arm_boot_fsa.pl
?- show_happy_path.
?- run_tests.
```

## Module Interface

```prolog
:- module(arm_boot_fsa, [
    boot_state/1,      % State declarations
    transition/2,      % Direct transitions
    reachable/2,       % Transitive closure
    terminal/1,        % Terminal states
    success/1,         % Success state
    failure/1,         % Failure states
    initial/1,         % Initial state
    loading/1,         % Loading states
    execution/1,       % Execution states
    path_length/3,     % Path length queries
    happy_path/1,      % Success path
    run_tests/0        % Test suite
]).
```

## Predicates

### State Classification

| Predicate | Description | Example |
|-----------|-------------|---------|
| `boot_state(S)` | S is a valid state | `boot_state(power_on)` |
| `terminal(S)` | S has no outgoing transitions | `terminal(boot_success)` |
| `success(S)` | S is the success state | `success(boot_success)` |
| `failure(S)` | S is a failure state | `failure(hardware_fail)` |
| `initial(S)` | S is the initial state | `initial(power_on)` |
| `loading(S)` | S is a loading state | `loading(kernel_loading)` |
| `execution(S)` | S is an execution state | `execution(rom_execution)` |

### Transitions and Reachability

| Predicate | Description | Example |
|-----------|-------------|---------|
| `transition(S1, S2)` | Direct transition S1 -> S2 | `transition(power_on, rom_execution)` |
| `reachable(S1, S2)` | S2 reachable from S1 | `reachable(power_on, boot_success)` |
| `path(S1, S2, Path)` | Find path from S1 to S2 | `path(power_on, boot_success, P)` |
| `path_length(S1, S2, N)` | Length of path | `path_length(power_on, boot_success, 8)` |
| `shortest_path(S1, S2, N)` | Minimum path length | `shortest_path(power_on, no_boot_media, 2)` |

### Path Queries

| Predicate | Description |
|-----------|-------------|
| `happy_path(Path)` | Path from power_on to boot_success without failures |
| `reachable_failures(Fs)` | All reachable failure states |
| `reachable_terminals(Ts)` | All reachable terminal states |
| `can_reach_success(S)` | States that can reach success |

## Test Suite

Run all 10 tests:

```prolog
?- run_tests.

=== ARM Boot FSA - Prolog Tests ===

Test 1: Boot success reachable from power_on... PASS
Test 2: All failure states reachable... PASS ([no_boot_media,firmware_corrupt,secure_boot_fail,hardware_fail])
Test 3: Happy path exists... PASS ([power_on,rom_execution,...,boot_success])
Test 4: Happy path is 8 transitions... PASS (9 states)
Test 5: Success/failure mutually exclusive... PASS
Test 6: Terminal states are absorbing... PASS
Test 7: SecureBootFail only from loading states... PASS
Test 8: HardwareFail only from execution states... PASS
Test 9: Shortest path to success is 8... PASS
Test 10: Shortest path to no_boot_media is 2... PASS

=== All tests completed ===
```

## Implementation Notes

### Tabling for Termination

The `reachable/2` predicate uses SWI-Prolog tabling to ensure termination:

```prolog
:- table reachable/2.

reachable(S, S) :- boot_state(S).
reachable(S1, S3) :-
    transition(S1, S2),
    reachable(S2, S3).
```

Without tabling, the transitive closure would loop infinitely.

### Safety Properties

```prolog
% No state is both success and failure
success_failure_exclusive :-
    \+ (success(S), failure(S)).

% Terminal states are absorbing (no outgoing transitions)
terminal_absorbing :-
    \+ (terminal(S), transition(S, _)).

% Secure boot failure only from loading states
secure_boot_from_loading :-
    forall(transition(S, secure_boot_fail), loading(S)).
```

## Interactive Helpers

```prolog
?- show_states.        % List all 13 states
?- show_transitions.   % List all 18 transitions
?- show_happy_path.    % Show the success path
?- show_reachable(rom_execution).  % States reachable from a given state
```

## Example Queries

```prolog
% Find all paths to failure
?- failure(F), path(power_on, F, Path).

% Find states with multiple successors
?- transition(S, T1), transition(S, T2), T1 \= T2.

% Find the shortest failure path
?- failure(F), shortest_path(power_on, F, N).

% Which states can reach both success and failure?
?- can_reach_success(S), can_reach_failure(S, _).
```

## Comparison with Other Tools

| Tool | Type | Advantage |
|------|------|-----------|
| SWI-Prolog | Logic programming | Executable queries, path finding |
| Z3 | SMT solver | Property verification |
| Vampire | FOL prover | Theorem proving |
| Lean 4 | Proof assistant | Certified proofs |

**Prolog advantage**: Interactive exploration, path enumeration, and executable specifications.

---

**Last Updated**: 2025-12-27
**Tests Passed**: 10/10
