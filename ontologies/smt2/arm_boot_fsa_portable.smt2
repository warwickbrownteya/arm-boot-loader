; ARM Boot FSA - Portable SMT-LIB2 Verification
; Compatible with Z3, CVC5, and Yices
; Generated: 2025-12-27

(set-logic ALL)

; =============================================================================
; TYPE DEFINITIONS
; =============================================================================

(declare-datatypes () ((BootState
    PowerOn ROMExecution BootcodeLoading BootcodeExecution
    StartElfLoading StartElfExecution KernelLoading KernelExecution
    BootSuccess NoBootMedia FirmwareCorrupt SecureBootFail HardwareFail
)))

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
(declare-const s9 BootState)

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
(assert (can-transition s8 s9))

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
; TEST 3: Non-terminal states have successors
; =============================================================================
(push)
(declare-const state BootState)
(declare-const next BootState)
(assert (not (is-terminal state)))
(assert (not (can-transition state next)))
(check-sat)  ; Expected: unsat
(pop)

; =============================================================================
; TEST 4: BootSuccess is reachable in 8 steps
; =============================================================================
(push)
(assert (= s8 BootSuccess))
(check-sat)  ; Expected: sat
(pop)

; =============================================================================
; TEST 5: Failure states are reachable
; =============================================================================
(push)
(assert (or (= s2 NoBootMedia) (= s3 FirmwareCorrupt)
            (= s3 SecureBootFail) (= s4 HardwareFail)))
(check-sat)  ; Expected: sat
(pop)

; =============================================================================
; TEST 6: Cannot skip boot stages
; =============================================================================
(push)
(assert (= s2 KernelExecution))
(check-sat)  ; Expected: unsat
(pop)

; =============================================================================
; TEST 7: SecureBootFail only from loading states
; =============================================================================
(push)
(assert (or
    (and (= s2 SecureBootFail) (not (is-loading s1)))
    (and (= s3 SecureBootFail) (not (is-loading s2)))
    (and (= s4 SecureBootFail) (not (is-loading s3)))
    (and (= s5 SecureBootFail) (not (is-loading s4)))
))
(check-sat)  ; Expected: unsat
(pop)

; =============================================================================
; TEST 8: HardwareFail only from execution states
; =============================================================================
(push)
(assert (or
    (and (= s3 HardwareFail) (not (is-executing s2)))
    (and (= s4 HardwareFail) (not (is-executing s3)))
    (and (= s5 HardwareFail) (not (is-executing s4)))
    (and (= s6 HardwareFail) (not (is-executing s5)))
))
(check-sat)  ; Expected: unsat
(pop)

; =============================================================================
; TEST 9: Eventually reaches terminal state
; =============================================================================
(push)
(assert (not (or (is-terminal s2) (is-terminal s3) (is-terminal s4)
                 (is-terminal s5) (is-terminal s6) (is-terminal s7)
                 (is-terminal s8) (is-terminal s9))))
(check-sat)  ; Expected: unsat
(pop)

; =============================================================================
; TEST 10: At most one terminal state per trace
; =============================================================================
(push)
(declare-const t1 BootState)
(declare-const t2 BootState)
(assert (is-terminal t1))
(assert (is-terminal t2))
(assert (not (= t1 t2)))
(assert (or (= s2 t1) (= s3 t1) (= s4 t1) (= s5 t1) (= s6 t1) (= s7 t1) (= s8 t1)))
(assert (or (= s2 t2) (= s3 t2) (= s4 t2) (= s5 t2) (= s6 t2) (= s7 t2) (= s8 t2)))
(check-sat)  ; Expected: unsat
(pop)
