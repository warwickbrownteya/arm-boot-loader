; ARM Boot FSA - Safety Property Verification
; SMT-LIB2 encoding for Z3 verification
; Generated: 2025-12-27
;
; This file verifies safety properties of the boot FSA
; Usage: z3 arm_boot_fsa_safety.smt2

(set-logic ALL)
(set-option :produce-models true)

; =============================================================================
; TYPE DEFINITIONS
; =============================================================================

(declare-datatypes () ((BootState
    PowerOn ROMExecution BootcodeLoading BootcodeExecution
    StartElfLoading StartElfExecution KernelLoading KernelExecution
    BootSuccess NoBootMedia FirmwareCorrupt SecureBootFail HardwareFail
)))

(declare-datatypes () ((BootCondition
    PowerStable BootMediaFound FileValid SignatureValid HardwareOK KernelValid
)))

(declare-datatypes () ((PiModel Pi1 Pi2 Pi3 Pi4 Pi5 PiZero PiZero2)))

; =============================================================================
; TRANSITION RELATION (deterministic version)
; =============================================================================

; Condition state (will be constrained per-query)
(declare-fun cond-holds (BootCondition) Bool)

; Given conditions, exactly one next state exists (deterministic FSA)
(define-fun next-state ((from BootState)) BootState
    (ite (= from PowerOn)
         (ite (cond-holds PowerStable) ROMExecution PowerOn)  ; Wait for power
    (ite (= from ROMExecution)
         (ite (cond-holds BootMediaFound) BootcodeLoading NoBootMedia)
    (ite (= from BootcodeLoading)
         (ite (cond-holds FileValid) BootcodeExecution FirmwareCorrupt)
    (ite (= from BootcodeExecution)
         (ite (cond-holds HardwareOK) StartElfLoading HardwareFail)
    (ite (= from StartElfLoading)
         (ite (cond-holds FileValid) StartElfExecution FirmwareCorrupt)
    (ite (= from StartElfExecution)
         (ite (cond-holds HardwareOK) KernelLoading HardwareFail)
    (ite (= from KernelLoading)
         (ite (cond-holds KernelValid) KernelExecution FirmwareCorrupt)
    (ite (= from KernelExecution)
         BootSuccess  ; Simplified: assume success from kernel execution
    ; Terminal states stay in place
    from)))))))))

; State classification
(define-fun is-terminal ((s BootState)) Bool
    (or (= s BootSuccess) (= s NoBootMedia) (= s FirmwareCorrupt)
        (= s SecureBootFail) (= s HardwareFail)))

(define-fun is-success ((s BootState)) Bool (= s BootSuccess))
(define-fun is-failure ((s BootState)) Bool
    (or (= s NoBootMedia) (= s FirmwareCorrupt)
        (= s SecureBootFail) (= s HardwareFail)))

; =============================================================================
; SAFETY PROPERTY 1: Determinism
; =============================================================================
; The FSA is deterministic: from any state with given conditions,
; there is exactly one next state.

(echo "")
(echo "=================================================================")
(echo "SAFETY PROPERTY 1: Determinism Verification")
(echo "=================================================================")

; For determinism, we verify that next-state is a function
; (always produces exactly one result for each input)
; This is guaranteed by construction (using ite)

(push)
(declare-const s BootState)
(declare-const n1 BootState)
(declare-const n2 BootState)
(assert (= n1 (next-state s)))
(assert (= n2 (next-state s)))
(assert (not (= n1 n2)))  ; Try to find non-determinism
(check-sat)
(echo "Non-determinism found (should be UNSAT):")
(pop)

; =============================================================================
; SAFETY PROPERTY 2: No Stuck States
; =============================================================================
; Every non-terminal state has a valid successor

(echo "")
(echo "=================================================================")
(echo "SAFETY PROPERTY 2: No Stuck States")
(echo "=================================================================")

(push)
(declare-const s BootState)
; Assume s is not terminal
(assert (not (is-terminal s)))
; Assume all conditions could be true (best case)
(assert (cond-holds PowerStable))
(assert (cond-holds BootMediaFound))
(assert (cond-holds FileValid))
(assert (cond-holds HardwareOK))
(assert (cond-holds KernelValid))
; Try to find a state with no progress
(assert (= s (next-state s)))
(check-sat)
(echo "Found stuck non-terminal state (should be UNSAT):")
(pop)

; =============================================================================
; SAFETY PROPERTY 3: Terminal States Are Absorbing
; =============================================================================
; Once in a terminal state, the system stays there

(echo "")
(echo "=================================================================")
(echo "SAFETY PROPERTY 3: Terminal States Are Absorbing")
(echo "=================================================================")

(push)
(declare-const s BootState)
(assert (is-terminal s))
(assert (not (= s (next-state s))))  ; Terminal state can leave
(check-sat)
(echo "Terminal state can escape (should be UNSAT):")
(pop)

; =============================================================================
; SAFETY PROPERTY 4: Success Requires Valid Path
; =============================================================================
; BootSuccess can only be reached if all conditions were satisfied

(echo "")
(echo "=================================================================")
(echo "SAFETY PROPERTY 4: Success Requires All Conditions")
(echo "=================================================================")

; Trace: sequence of states for bounded verification
(declare-const s0 BootState)
(declare-const s1 BootState)
(declare-const s2 BootState)
(declare-const s3 BootState)
(declare-const s4 BootState)
(declare-const s5 BootState)
(declare-const s6 BootState)
(declare-const s7 BootState)
(declare-const s8 BootState)

; Transitions follow next-state function
(assert (= s0 PowerOn))
(assert (= s1 (next-state s0)))
(assert (= s2 (next-state s1)))
(assert (= s3 (next-state s2)))
(assert (= s4 (next-state s3)))
(assert (= s5 (next-state s4)))
(assert (= s6 (next-state s5)))
(assert (= s7 (next-state s6)))
(assert (= s8 (next-state s7)))

; Query: Can we reach BootSuccess without all conditions?
(push)
(assert (= s8 BootSuccess))
; At least one critical condition fails
(assert (or (not (cond-holds PowerStable))
            (not (cond-holds BootMediaFound))
            (not (cond-holds FileValid))
            (not (cond-holds HardwareOK))
            (not (cond-holds KernelValid))))
(check-sat)
(echo "BootSuccess reachable with missing conditions (should be UNSAT):")
(pop)

; Verify success IS reachable with all conditions
(push)
(assert (= s8 BootSuccess))
(assert (cond-holds PowerStable))
(assert (cond-holds BootMediaFound))
(assert (cond-holds FileValid))
(assert (cond-holds HardwareOK))
(assert (cond-holds KernelValid))
(check-sat)
(echo "BootSuccess reachable with all conditions (should be SAT):")
(get-value (s0 s1 s2 s3 s4 s5 s6 s7 s8))
(pop)

; =============================================================================
; SAFETY PROPERTY 5: Failure Is Reachable
; =============================================================================
; Each failure state is reachable under appropriate conditions

(echo "")
(echo "=================================================================")
(echo "SAFETY PROPERTY 5: Failure States Reachable")
(echo "=================================================================")

; NoBootMedia reachable
(push)
(assert (= s2 NoBootMedia))
(assert (cond-holds PowerStable))
(assert (not (cond-holds BootMediaFound)))
(check-sat)
(echo "NoBootMedia reachable:")
(get-value (s0 s1 s2))
(pop)

; FirmwareCorrupt reachable (at bootcode loading)
(push)
(assert (= s3 FirmwareCorrupt))
(assert (cond-holds PowerStable))
(assert (cond-holds BootMediaFound))
(assert (not (cond-holds FileValid)))
(check-sat)
(echo "FirmwareCorrupt reachable:")
(get-value (s0 s1 s2 s3))
(pop)

; HardwareFail reachable
(push)
(assert (= s4 HardwareFail))
(assert (cond-holds PowerStable))
(assert (cond-holds BootMediaFound))
(assert (cond-holds FileValid))
(assert (not (cond-holds HardwareOK)))
(check-sat)
(echo "HardwareFail reachable:")
(get-value (s0 s1 s2 s3 s4))
(pop)

; =============================================================================
; SAFETY PROPERTY 6: No Cycles (Except Self-Loops on Terminal)
; =============================================================================

(echo "")
(echo "=================================================================")
(echo "SAFETY PROPERTY 6: Progress Guarantee (No Non-Terminal Cycles)")
(echo "=================================================================")

; Boot process should always make progress toward terminal state
; Verify: non-terminal states don't loop back to earlier states

(push)
; Define state ordering (depth from initial state)
(define-fun state-depth ((s BootState)) Int
    (ite (= s PowerOn) 0
    (ite (= s ROMExecution) 1
    (ite (= s BootcodeLoading) 2
    (ite (= s BootcodeExecution) 3
    (ite (= s StartElfLoading) 4
    (ite (= s StartElfExecution) 5
    (ite (= s KernelLoading) 6
    (ite (= s KernelExecution) 7
    (ite (= s BootSuccess) 8
    ; Failure states (terminal at various depths)
    (ite (= s NoBootMedia) 8
    (ite (= s FirmwareCorrupt) 8
    (ite (= s SecureBootFail) 8
    (ite (= s HardwareFail) 8
    -1))))))))))))))

(declare-const current BootState)
(declare-const next BootState)
(assert (not (is-terminal current)))
(assert (= next (next-state current)))
; Try to find a transition that goes backward (or stays same for non-terminal)
(assert (<= (state-depth next) (state-depth current)))
(assert (not (is-terminal next)))
(check-sat)
(echo "Found non-progress transition (should be UNSAT):")
(pop)

(echo "")
(echo "=================================================================")
(echo "SAFETY VERIFICATION COMPLETE")
(echo "=================================================================")
