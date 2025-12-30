; ARM Boot FSA - Reachability Analysis
; SMT-LIB2 encoding for Z3 verification
; Generated: 2025-12-27
;
; This file performs reachability analysis on the boot FSA
; Usage: z3 arm_boot_fsa_reachability.smt2

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

; =============================================================================
; TRANSITION RELATION (relation form for reachability)
; =============================================================================

; Direct transition relation (condition-independent - existential)
; A transition exists if there's SOME condition under which it can fire
(define-fun can-transition ((from BootState) (to BootState)) Bool
    (or
        ; Happy path
        (and (= from PowerOn) (= to ROMExecution))
        (and (= from ROMExecution) (= to BootcodeLoading))
        (and (= from BootcodeLoading) (= to BootcodeExecution))
        (and (= from BootcodeExecution) (= to StartElfLoading))
        (and (= from StartElfLoading) (= to StartElfExecution))
        (and (= from StartElfExecution) (= to KernelLoading))
        (and (= from KernelLoading) (= to KernelExecution))
        (and (= from KernelExecution) (= to BootSuccess))

        ; Failure paths
        (and (= from ROMExecution) (= to NoBootMedia))
        (and (= from BootcodeLoading) (= to FirmwareCorrupt))
        (and (= from BootcodeLoading) (= to SecureBootFail))
        (and (= from BootcodeExecution) (= to HardwareFail))
        (and (= from StartElfLoading) (= to FirmwareCorrupt))
        (and (= from StartElfLoading) (= to SecureBootFail))
        (and (= from StartElfExecution) (= to HardwareFail))
        (and (= from KernelLoading) (= to FirmwareCorrupt))
        (and (= from KernelLoading) (= to SecureBootFail))
        (and (= from KernelExecution) (= to HardwareFail))

        ; Terminal self-loops
        (and (= from BootSuccess) (= to BootSuccess))
        (and (= from NoBootMedia) (= to NoBootMedia))
        (and (= from FirmwareCorrupt) (= to FirmwareCorrupt))
        (and (= from SecureBootFail) (= to SecureBootFail))
        (and (= from HardwareFail) (= to HardwareFail))
    ))

; =============================================================================
; BOUNDED REACHABILITY (up to N steps)
; =============================================================================

(echo "")
(echo "=================================================================")
(echo "REACHABILITY ANALYSIS - Bounded Model Checking")
(echo "=================================================================")

; State trace for 10-step bounded analysis
(declare-const s0 BootState)
(declare-const s1 BootState)
(declare-const s2 BootState)
(declare-const s3 BootState)
(declare-const s4 BootState)
(declare-const s5 BootState)
(declare-const s6 BootState)
(declare-const s7 BootState)
(declare-const s8 BootState)
(declare-const s9 BootState)

; Initial state
(assert (= s0 PowerOn))

; Valid transitions
(assert (can-transition s0 s1))
(assert (can-transition s1 s2))
(assert (can-transition s2 s3))
(assert (can-transition s3 s4))
(assert (can-transition s4 s5))
(assert (can-transition s5 s6))
(assert (can-transition s6 s7))
(assert (can-transition s7 s8))
(assert (can-transition s8 s9))

; =============================================================================
; QUERY 1: Is BootSuccess reachable from PowerOn?
; =============================================================================

(echo "")
(echo "--- Query 1: BootSuccess Reachability ---")

(push)
(assert (or (= s1 BootSuccess) (= s2 BootSuccess) (= s3 BootSuccess)
            (= s4 BootSuccess) (= s5 BootSuccess) (= s6 BootSuccess)
            (= s7 BootSuccess) (= s8 BootSuccess) (= s9 BootSuccess)))
(check-sat)
(echo "BootSuccess is reachable (expected SAT):")
(get-value (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9))
(pop)

; =============================================================================
; QUERY 2: Minimum steps to BootSuccess
; =============================================================================

(echo "")
(echo "--- Query 2: Minimum Steps to BootSuccess ---")

; Can reach in 8 steps?
(push)
(assert (= s8 BootSuccess))
(check-sat)
(echo "Reachable in exactly 8 steps (expected SAT):")
(get-value (s0 s1 s2 s3 s4 s5 s6 s7 s8))
(pop)

; Can reach in 7 steps?
(push)
(assert (= s7 BootSuccess))
(check-sat)
(echo "Reachable in 7 steps (expected UNSAT - need 8 steps):")
(pop)

; =============================================================================
; QUERY 3: Is NoBootMedia reachable?
; =============================================================================

(echo "")
(echo "--- Query 3: NoBootMedia Reachability ---")

(push)
(assert (or (= s1 NoBootMedia) (= s2 NoBootMedia) (= s3 NoBootMedia)
            (= s4 NoBootMedia) (= s5 NoBootMedia)))
(check-sat)
(echo "NoBootMedia is reachable:")
(get-value (s0 s1 s2))
(pop)

; =============================================================================
; QUERY 4: Is FirmwareCorrupt reachable?
; =============================================================================

(echo "")
(echo "--- Query 4: FirmwareCorrupt Reachability ---")

(push)
(assert (or (= s2 FirmwareCorrupt) (= s3 FirmwareCorrupt) (= s4 FirmwareCorrupt)
            (= s5 FirmwareCorrupt) (= s6 FirmwareCorrupt) (= s7 FirmwareCorrupt)))
(check-sat)
(echo "FirmwareCorrupt is reachable:")
(get-value (s0 s1 s2 s3))
(pop)

; =============================================================================
; QUERY 5: Is SecureBootFail reachable?
; =============================================================================

(echo "")
(echo "--- Query 5: SecureBootFail Reachability ---")

(push)
(assert (or (= s2 SecureBootFail) (= s3 SecureBootFail) (= s4 SecureBootFail)
            (= s5 SecureBootFail) (= s6 SecureBootFail) (= s7 SecureBootFail)))
(check-sat)
(echo "SecureBootFail is reachable:")
(get-value (s0 s1 s2 s3))
(pop)

; =============================================================================
; QUERY 6: Is HardwareFail reachable?
; =============================================================================

(echo "")
(echo "--- Query 6: HardwareFail Reachability ---")

(push)
(assert (or (= s3 HardwareFail) (= s4 HardwareFail) (= s5 HardwareFail)
            (= s6 HardwareFail) (= s7 HardwareFail) (= s8 HardwareFail)))
(check-sat)
(echo "HardwareFail is reachable:")
(get-value (s0 s1 s2 s3 s4))
(pop)

; =============================================================================
; QUERY 7: Mutual Exclusion - Can we reach two different terminal states?
; =============================================================================

(echo "")
(echo "--- Query 7: Terminal State Uniqueness ---")

(push)
; Can a single trace reach two different terminal states?
(define-fun is-terminal ((s BootState)) Bool
    (or (= s BootSuccess) (= s NoBootMedia) (= s FirmwareCorrupt)
        (= s SecureBootFail) (= s HardwareFail)))

(declare-const term1 BootState)
(declare-const term2 BootState)
(declare-const idx1 Int)
(declare-const idx2 Int)

; Both are terminal and different
(assert (is-terminal term1))
(assert (is-terminal term2))
(assert (not (= term1 term2)))

; Both appear in trace
(assert (or (= s1 term1) (= s2 term1) (= s3 term1) (= s4 term1)
            (= s5 term1) (= s6 term1) (= s7 term1) (= s8 term1)))
(assert (or (= s1 term2) (= s2 term2) (= s3 term2) (= s4 term2)
            (= s5 term2) (= s6 term2) (= s7 term2) (= s8 term2)))

(check-sat)
(echo "Can reach two different terminal states in one trace (should be UNSAT):")
(pop)

; =============================================================================
; QUERY 8: Shortest Path to Each Failure State
; =============================================================================

(echo "")
(echo "--- Query 8: Shortest Paths to Failure States ---")

; Shortest to NoBootMedia (expect 2 steps)
(push)
(assert (= s2 NoBootMedia))
(check-sat)
(echo "NoBootMedia in 2 steps:")
(get-value (s0 s1 s2))
(pop)

; Shortest to FirmwareCorrupt (expect 3 steps)
(push)
(assert (= s3 FirmwareCorrupt))
(check-sat)
(echo "FirmwareCorrupt in 3 steps:")
(get-value (s0 s1 s2 s3))
(pop)

; Shortest to HardwareFail (expect 4 steps)
(push)
(assert (= s4 HardwareFail))
(check-sat)
(echo "HardwareFail in 4 steps:")
(get-value (s0 s1 s2 s3 s4))
(pop)

; =============================================================================
; QUERY 9: All States Are Reachable
; =============================================================================

(echo "")
(echo "--- Query 9: Universal Reachability ---")

; Check each state is reachable from PowerOn
(echo "Checking reachability of all states...")

(push)
(assert (or (= s1 ROMExecution) (= s2 ROMExecution)))
(check-sat)
(echo "ROMExecution reachable: SAT expected")
(pop)

(push)
(assert (or (= s2 BootcodeLoading) (= s3 BootcodeLoading)))
(check-sat)
(echo "BootcodeLoading reachable: SAT expected")
(pop)

(push)
(assert (or (= s3 BootcodeExecution) (= s4 BootcodeExecution)))
(check-sat)
(echo "BootcodeExecution reachable: SAT expected")
(pop)

(push)
(assert (or (= s4 StartElfLoading) (= s5 StartElfLoading)))
(check-sat)
(echo "StartElfLoading reachable: SAT expected")
(pop)

(push)
(assert (or (= s5 StartElfExecution) (= s6 StartElfExecution)))
(check-sat)
(echo "StartElfExecution reachable: SAT expected")
(pop)

(push)
(assert (or (= s6 KernelLoading) (= s7 KernelLoading)))
(check-sat)
(echo "KernelLoading reachable: SAT expected")
(pop)

(push)
(assert (or (= s7 KernelExecution) (= s8 KernelExecution)))
(check-sat)
(echo "KernelExecution reachable: SAT expected")
(pop)

(echo "")
(echo "=================================================================")
(echo "REACHABILITY ANALYSIS COMPLETE")
(echo "=================================================================")
