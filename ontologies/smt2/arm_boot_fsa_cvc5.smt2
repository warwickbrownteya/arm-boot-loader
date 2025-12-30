; ARM Boot FSA - CVC5 Compatible Version
; SMT-LIB 2.6 syntax for datatypes
; Generated: 2025-12-27

(set-logic ALL)

; =============================================================================
; TYPE DEFINITIONS (SMT-LIB 2.6 syntax)
; =============================================================================

(declare-datatype BootState (
    (PowerOn) (ROMExecution) (BootcodeLoading) (BootcodeExecution)
    (StartElfLoading) (StartElfExecution) (KernelLoading) (KernelExecution)
    (BootSuccess) (NoBootMedia) (FirmwareCorrupt) (SecureBootFail) (HardwareFail)
))

; State classification functions
(define-fun is-terminal ((s BootState)) Bool
    (or (= s BootSuccess) (= s NoBootMedia) (= s FirmwareCorrupt)
        (= s SecureBootFail) (= s HardwareFail)))

(define-fun is-failure ((s BootState)) Bool
    (or (= s NoBootMedia) (= s FirmwareCorrupt)
        (= s SecureBootFail) (= s HardwareFail)))

(define-fun is-success ((s BootState)) Bool (= s BootSuccess))

(define-fun is-loading ((s BootState)) Bool
    (or (= s BootcodeLoading) (= s StartElfLoading) (= s KernelLoading)))

(define-fun is-executing ((s BootState)) Bool
    (or (= s ROMExecution) (= s BootcodeExecution)
        (= s StartElfExecution) (= s KernelExecution)))

; Transition relation
(define-fun can-transition ((from BootState) (to BootState)) Bool
    (or
        (and (= from PowerOn) (= to ROMExecution))
        (and (= from ROMExecution) (= to BootcodeLoading))
        (and (= from ROMExecution) (= to NoBootMedia))
        (and (= from BootcodeLoading) (= to BootcodeExecution))
        (and (= from BootcodeLoading) (= to FirmwareCorrupt))
        (and (= from BootcodeLoading) (= to SecureBootFail))
        (and (= from BootcodeExecution) (= to StartElfLoading))
        (and (= from BootcodeExecution) (= to HardwareFail))
        (and (= from StartElfLoading) (= to StartElfExecution))
        (and (= from StartElfLoading) (= to FirmwareCorrupt))
        (and (= from StartElfLoading) (= to SecureBootFail))
        (and (= from StartElfExecution) (= to KernelLoading))
        (and (= from StartElfExecution) (= to HardwareFail))
        (and (= from KernelLoading) (= to KernelExecution))
        (and (= from KernelLoading) (= to FirmwareCorrupt))
        (and (= from KernelLoading) (= to SecureBootFail))
        (and (= from KernelExecution) (= to BootSuccess))
        (and (= from KernelExecution) (= to HardwareFail))
        (and (= from BootSuccess) (= to BootSuccess))
        (and (= from NoBootMedia) (= to NoBootMedia))
        (and (= from FirmwareCorrupt) (= to FirmwareCorrupt))
        (and (= from SecureBootFail) (= to SecureBootFail))
        (and (= from HardwareFail) (= to HardwareFail))
    ))

; Bounded trace (10 steps)
(declare-const s0 BootState)
(declare-const s1 BootState)
(declare-const s2 BootState)
(declare-const s3 BootState)
(declare-const s4 BootState)
(declare-const s5 BootState)
(declare-const s6 BootState)
(declare-const s7 BootState)
(declare-const s8 BootState)

; Trace constraints
(assert (= s0 PowerOn))
(assert (can-transition s0 s1))
(assert (can-transition s1 s2))
(assert (can-transition s2 s3))
(assert (can-transition s3 s4))
(assert (can-transition s4 s5))
(assert (can-transition s5 s6))
(assert (can-transition s6 s7))
(assert (can-transition s7 s8))

; =============================================================================
; TEST 1: Success/Failure mutual exclusion
; =============================================================================
(push)
(declare-const test_state BootState)
(assert (and (is-success test_state) (is-failure test_state)))
(check-sat)  ; Expected: unsat
(pop)

; =============================================================================
; TEST 2: Terminal states are absorbing
; =============================================================================
(push)
(declare-const term BootState)
(declare-const next BootState)
(assert (is-terminal term))
(assert (can-transition term next))
(assert (not (= term next)))
(check-sat)  ; Expected: unsat
(pop)

; =============================================================================
; TEST 3: BootSuccess is reachable in 8 steps
; =============================================================================
(push)
(assert (= s8 BootSuccess))
(check-sat)  ; Expected: sat
(pop)

; =============================================================================
; TEST 4: Cannot skip boot stages
; =============================================================================
(push)
(assert (= s2 KernelExecution))
(check-sat)  ; Expected: unsat
(pop)

; =============================================================================
; TEST 5: SecureBootFail only from loading states
; =============================================================================
(push)
(assert (or
    (and (= s2 SecureBootFail) (not (is-loading s1)))
    (and (= s3 SecureBootFail) (not (is-loading s2)))
))
(check-sat)  ; Expected: unsat
(pop)

(echo "CVC5: All tests completed")
