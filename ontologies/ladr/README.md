# ARM Boot FSA - Prover9/LADR Encoding

**Generated**: 2025-12-27
**Prover**: Prover9 2017-11A (CIIRC)
**Proof Time**: <1ms

## Overview

This directory contains a first-order logic encoding of the ARM bootloader finite state automaton in LADR format, suitable for Prover9 theorem prover and Mace4 model finder.

## Files

| File | Description |
|------|-------------|
| `arm_boot_fsa.in` | Complete FSA encoding with goal |

## Quick Start

```bash
# Prove boot success reachability
prover9 -f arm_boot_fsa.in

# Search for counterexamples (model finding)
mace4 -f arm_boot_fsa.in
```

## Encoding Structure

### Predicates

| Predicate | Arity | Description |
|-----------|-------|-------------|
| `terminal(X)` | 1 | X is a terminal state |
| `success(X)` | 1 | X is the success state |
| `failure(X)` | 1 | X is a failure state |
| `initial(X)` | 1 | X is the initial state |
| `loading(X)` | 1 | X is a loading state |
| `execution(X)` | 1 | X is an execution state |
| `transition(X,Y)` | 2 | Direct transition from X to Y |
| `reachable(X,Y)` | 2 | Y is reachable from X |
| `boot_path(X,Y)` | 2 | Path from initial X to terminal Y |
| `successful_boot(X,Y)` | 2 | Successful boot path |
| `failed_boot(X,Y)` | 2 | Failed boot path |

### State Constants (13 states)

```
power_on, rom_execution, bootcode_loading, bootcode_execution,
startelf_loading, startelf_execution, kernel_loading, kernel_execution,
boot_success, no_boot_media, firmware_corrupt, secure_boot_fail, hardware_fail
```

### Axioms

```prover9
% Transition implies reachability
all X all Y (transition(X,Y) -> reachable(X,Y)).

% Reflexivity
all X reachable(X,X).

% Transitivity
all X all Y all Z (reachable(X,Y) & reachable(Y,Z) -> reachable(X,Z)).

% Terminal states have no outgoing transitions
all X all Y (terminal(X) -> -transition(X,Y)).

% Success and failure are mutually exclusive
all X -(success(X) & failure(X)).
```

### Goal

```prover9
formulas(goals).
reachable(power_on, boot_success).
end_of_list.
```

## Proof Result

```
% Proof 1 at 0.00 seconds.
% Length of proof is 31.
% Level of proof is 9.
% Maximum clause weight is 9.000.

Given=76. Generated=664. Kept=185. proofs=1.
```

The proof chains the 8 happy-path transitions:
```
power_on -> rom_execution -> bootcode_loading -> bootcode_execution
         -> startelf_loading -> startelf_execution -> kernel_loading
         -> kernel_execution -> boot_success
```

## Additional Queries

To prove different goals, modify the `formulas(goals)` section:

```prover9
% Example: Prove all failure states are reachable
formulas(goals).
reachable(power_on, no_boot_media).
reachable(power_on, firmware_corrupt).
reachable(power_on, hardware_fail).
reachable(power_on, secure_boot_fail).
end_of_list.
```

## Mace4 Usage

Use Mace4 to find counterexamples or finite models:

```bash
# Find a model of the assumptions
mace4 -c -f arm_boot_fsa.in

# Find model with specific domain size
mace4 -n 13 -f arm_boot_fsa.in
```

## Comparison with Other Tools

| Prover | Time | Proof Length |
|--------|------|--------------|
| Prover9 | <1ms | 31 steps |
| Vampire | 7ms | 15 steps |
| E Prover | 17ms | - |
| Z3 (SMT) | 49ms | - |

---

**Last Updated**: 2025-12-27
**Proofs Verified**: 1
