# ARM Boot FSA - SMT-LIB2 Verification Suite

**Generated**: 2025-12-27
**Solver**: Z3 4.15.4
**Performance**: All files execute in <50ms

## Overview

This directory contains SMT-LIB2 encodings of the ARM bootloader finite state automaton (FSA) for formal verification using Z3 and other SMT solvers.

## Files

| File | Purpose | Solver | Execution Time |
|------|---------|--------|----------------|
| `arm_boot_fsa_types.smt2` | Core type definitions (states, conditions, models) | Z3 | 7ms |
| `arm_boot_fsa_transitions.smt2` | Transition relation definition | Z3 | 7ms |
| `arm_boot_fsa_safety.smt2` | Safety property verification | Z3 | 18ms |
| `arm_boot_fsa_reachability.smt2` | Reachability analysis | Z3 | 45ms |
| `arm_boot_fsa_bmc.smt2` | Bounded model checking | Z3 | 38ms |
| `arm_boot_fsa_verify_all.smt2` | Complete verification suite | Z3 | 49ms |
| `arm_boot_fsa_cvc5.smt2` | CVC5-compatible (SMT-LIB 2.6) | CVC5 | 17ms |
| `arm_boot_fsa_yices.smt2` | Yices-compatible (integer encoding) | Yices | 5ms |
| `arm_boot_fsa_portable.smt2` | ASCII-only portable version | Z3 | 45ms |

## Quick Start

```bash
# Z3: Run complete verification (recommended)
z3 arm_boot_fsa_verify_all.smt2

# Z3: Run specific analyses
z3 arm_boot_fsa_safety.smt2
z3 arm_boot_fsa_reachability.smt2
z3 arm_boot_fsa_bmc.smt2

# CVC5: Run verification (requires --incremental for push/pop)
cvc5 --incremental arm_boot_fsa_cvc5.smt2

# Yices: Run verification
yices-smt2 arm_boot_fsa_yices.smt2
```

## State Machine Encoding

### States (13 total)

```
PowerOn → ROMExecution → BootcodeLoading → BootcodeExecution →
StartElfLoading → StartElfExecution → KernelLoading → KernelExecution → BootSuccess

Failure States:
- NoBootMedia (from ROMExecution)
- FirmwareCorrupt (from any Loading state)
- SecureBootFail (from any Loading state, Pi4/Pi5 only)
- HardwareFail (from any Execution state)
```

### Transitions (18 total)

Encoded as a predicate `can-transition(from, to)` that returns true for valid state transitions.

## Verified Properties

### Safety Properties
1. **Mutual Exclusion**: Success and failure states are disjoint
2. **Terminal Absorption**: Terminal states have no outgoing transitions
3. **Non-Stuck**: All non-terminal states have successors
4. **Determinism**: Given conditions, exactly one next state exists
5. **Progress**: Non-terminal states always advance

### Reachability Properties
1. **BootSuccess reachable** in exactly 8 steps (happy path)
2. **All failure states reachable** from initial state
3. **Shortest paths**:
   - NoBootMedia: 2 steps
   - FirmwareCorrupt: 3 steps
   - HardwareFail: 4 steps
   - SecureBootFail: 3 steps

### Temporal Properties (BMC)
1. **AG(success ∧ failure = ⊥)**: Never both success and failure
2. **AF(terminal)**: Eventually reaches terminal state
3. **Loading → X(Execution ∨ Failure)**: Loading always followed by execution or failure
4. **¬(success U ¬kernel_executed)**: Cannot succeed without kernel execution

## Example Output

```
▶ Happy Path (Boot Success):
((s0 PowerOn)
 (s1 ROMExecution)
 (s2 BootcodeLoading)
 (s3 BootcodeExecution)
 (s4 StartElfLoading)
 (s5 StartElfExecution)
 (s6 KernelLoading)
 (s7 KernelExecution)
 (s8 BootSuccess))

▶ Early Failure (No Boot Media):
((s0 PowerOn)
 (s1 ROMExecution)
 (s2 NoBootMedia))
```

## Extending the Verification

### Adding Custom Properties

```smt2
; Check if state X is reachable
(push)
(assert (or (= s1 X) (= s2 X) ... (= sN X)))
(check-sat)
(get-value (s0 s1 ... sN))
(pop)

; Verify property never violated
(push)
(assert (some-violation-condition))
(check-sat)  ; UNSAT means property holds
(pop)
```

### Using with CVC5

```bash
cvc5 --produce-models arm_boot_fsa_verify_all.smt2
```

### Using with Yices

```bash
yices-smt2 arm_boot_fsa_verify_all.smt2
```

## Integration with Ontologies

These SMT-LIB2 files are derived from:
- `../arm_boot_fsa_ontology.n3` (N3/Turtle source)
- `../owl_format/arm_boot_fsa_ontology.owl` (OWL/RDF-XML)

The translation preserves:
- State definitions
- Transition relations
- Condition dependencies
- Model-specific behavior (Pi4/Pi5 secure boot)

## Performance

| Solver | Time | Notes |
|--------|------|-------|
| Z3 4.15.4 | 49ms | Full verification suite |
| CVC5 1.3.3 | ~60ms | Slightly slower startup |
| Yices 2.7.0 | ~30ms | Fastest (limited output) |

## Comparison with HermiT

| Aspect | SMT (Z3) | OWL (HermiT) |
|--------|----------|--------------|
| Consistency | Implied by SAT | Explicit check |
| Reachability | Direct queries | Not supported |
| Counterexamples | Full traces | Not supported |
| Temporal properties | BMC support | Not supported |
| Performance | <50ms | ~100ms |

**Recommendation**: Use both tools - HermiT for ontology consistency, Z3 for state machine verification.

---

**Last Updated**: 2025-12-27
