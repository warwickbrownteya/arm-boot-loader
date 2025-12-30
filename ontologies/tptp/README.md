# ARM Boot FSA - TPTP Theorem Proving Suite

**Generated**: 2025-12-27
**Prover**: Vampire 5.0.0
**Format**: TPTP First-Order Logic (FOF)

## Overview

This directory contains TPTP encodings of the ARM bootloader FSA and related mathematical theories for automated theorem proving using Vampire, E Prover, or Prover9.

## Files

| File | Description | Theorems | Time |
|------|-------------|----------|------|
| `arm_boot_fsa.p` | FSA states, transitions, reachability | Reachability proofs | 6ms |
| `arm_boot_category.p` | Category theory (Grothendieck) | Identity morphisms | 14ms |
| `arm_boot_kripke.p` | Modal logic (Kripke semantics) | Accessibility theorems | 20ms |
| `arm_boot_theorems.p` | Combined theorem suite | Multiple properties | 13ms |

## Quick Start

```bash
# Prove reachability theorem
vampire --mode casc arm_boot_fsa.p

# With proof output
vampire --proof tptp arm_boot_fsa.p

# With time limit
vampire --time_limit 30 arm_boot_fsa.p

# Using E Prover
eprover --auto arm_boot_fsa.p

# Using Prover9 (requires LADR format)
# These files are in TPTP format; use tptp_to_ladr for conversion
```

## Theorems Proved

### FSA Reachability (arm_boot_fsa.p)

**Theorem**: Boot success is reachable from power on
```
reachable(power_on, boot_success)
```

**Proof structure**: Vampire derives the 8-step happy path:
```
power_on → rom_execution → bootcode_loading → bootcode_execution →
startelf_loading → startelf_execution → kernel_loading → kernel_execution →
boot_success
```

### Category Theory (arm_boot_category.p)

**Theorem**: Every boot state (object) has an identity morphism
```
∀S: object(S) ⟹ ∃Id: morphism(Id) ∧ identity(Id, S)
```

**Proof**: Follows from the identity axiom for categories.

### Kripke Semantics (arm_boot_kripke.p)

**Theorem**: Success world is eventually accessible from power on
```
eventually_accessible(w_power_on, w_boot_success)
```

**Proof**: Via transitive closure of accessibility relation.

## Available Theorems

### arm_boot_fsa.p
1. `theorem_success_reachable` - Boot success is reachable (DEFAULT)
2. `theorem_failures_reachable` - All failure states reachable
3. `theorem_termination` - Terminal state always reachable
4. `theorem_success_terminal` - Success has no outgoing transitions

### arm_boot_category.p
1. `theorem_identity_exists` - Identity morphisms exist (DEFAULT)
2. `theorem_happy_path_exists` - Composition path exists
3. `theorem_identity_unit` - Identity is composition unit
4. `theorem_functor_structure` - Functors preserve structure

### arm_boot_kripke.p
1. `theorem_success_eventually` - Success eventually reachable (DEFAULT)
2. `theorem_success_necessary` - Success is necessary at success world
3. `theorem_failure_possible` - Failure possible from any state
4. `theorem_success_failure_exclusive` - Success/failure exclusive
5. `theorem_axiom_t_holds` - Modal axiom T holds

### arm_boot_theorems.p
1. `theorem_success_reachable` - Success reachable (DEFAULT)
2. `theorem_all_terminals_reachable` - All terminals reachable
3. `theorem_terminal_no_exit` - Terminals have no exits
4. `theorem_exclusive_outcomes` - Success/failure exclusive
5. `theorem_happy_path` - 8-step path to success
6. `theorem_failure_terminal` - Failures are terminal
7. `theorem_firmware_corrupt_from_loading` - FW corrupt reachable
8. `theorem_secure_boot_from_loading` - Secure boot from loading only
9. `theorem_hardware_fail_from_exec` - HW fail from exec only
10. `theorem_non_terminal_progress` - Non-terminals have successors

## To Prove Different Theorems

Uncomment the desired conjecture in the file:

```tptp
% Theorem 2: All failure states are reachable
fof(theorem_failures_reachable, conjecture,
    (reachable(power_on, no_boot_media) &
     reachable(power_on, firmware_corrupt) &
     reachable(power_on, secure_boot_fail) &
     reachable(power_on, hardware_fail))).
```

Then run:
```bash
vampire arm_boot_fsa.p
```

## TPTP Syntax Notes

### Quantifiers
- `![X]:` - Universal (∀)
- `?[X]:` - Existential (∃)

### Connectives
- `&` - Conjunction (∧)
- `|` - Disjunction (∨)
- `~` - Negation (¬)
- `=>` - Implication (→)
- `<=>` - Biconditional (↔)
- `=` - Equality
- `~(X = Y)` - Inequality

### Formula Types
- `fof(name, axiom, formula)` - Axiom
- `fof(name, conjecture, formula)` - Theorem to prove

## Domain Encoding

### Boot States (13)
```
power_on, rom_execution, bootcode_loading, bootcode_execution,
startelf_loading, startelf_execution, kernel_loading, kernel_execution,
boot_success, no_boot_media, firmware_corrupt, secure_boot_fail, hardware_fail
```

### Predicates
```
boot_state(S)           % S is a boot state
terminal_state(S)       % S is terminal (no outgoing transitions)
success_state(S)        % S is success state
failure_state(S)        % S is failure state
initial_state(S)        % S is initial state
loading_state(S)        % S is loading phase
execution_state(S)      % S is execution phase
transition(S1, S2)      % Direct transition from S1 to S2
reachable(S1, S2)       % S2 is reachable from S1
```

## Integration with Ontologies

These TPTP files are derived from:
- `../arm_boot_fsa_ontology.n3` - FSA states and transitions
- `../arm_boot_grothendieck_category.n3` - Category theory
- `../arm_boot_kripke_semantics.n3` - Modal logic

## Performance

| Prover | File | Result | Time |
|--------|------|--------|------|
| Vampire 5.0.0 | arm_boot_fsa.p | Theorem | 6ms |
| Vampire 5.0.0 | arm_boot_category.p | Theorem | 14ms |
| Vampire 5.0.0 | arm_boot_kripke.p | Theorem | 20ms |
| Vampire 5.0.0 | arm_boot_theorems.p | Theorem | 13ms |

## Comparison with SMT

| Aspect | TPTP (Vampire) | SMT-LIB2 (Z3) |
|--------|----------------|---------------|
| Logic | Pure FOL | Multi-sorted |
| Proof output | Yes | Limited |
| Strategy | Auto selection | Fixed |
| Best for | Theorem proving | Satisfiability |
| Performance | <20ms | <50ms |

**Recommendation**: Use Vampire for theorem proving with proofs; Z3 for model generation and satisfiability checking.

---

**Last Updated**: 2025-12-27
