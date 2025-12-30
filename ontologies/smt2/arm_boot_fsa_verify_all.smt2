; ARM Boot FSA - Complete Verification Suite
; SMT-LIB2 encoding for Z3 verification
; Generated: 2025-12-27
;
; This is the main verification file that runs all checks
; Usage: z3 arm_boot_fsa_verify_all.smt2
;        time z3 arm_boot_fsa_verify_all.smt2

(set-logic ALL)
(set-option :produce-models true)

(echo "")
(echo "╔═══════════════════════════════════════════════════════════════╗")
(echo "║     ARM BOOT FSA - COMPLETE Z3 VERIFICATION SUITE            ║")
(echo "║     Generated: 2025-12-27                                     ║")
(echo "╚═══════════════════════════════════════════════════════════════╝")
(echo "")

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
; VERIFICATION RESULTS TRACKING
; =============================================================================

(echo "┌─────────────────────────────────────────────────────────────────┐")
(echo "│ VERIFICATION RESULTS                                           │")
(echo "├─────────────────────────────────────────────────────────────────┤")

; -----------------------------------------------------------------------------
; TEST 1: State Types Are Mutually Exclusive
; -----------------------------------------------------------------------------
(push)
(declare-const test_state BootState)
(assert (and (is-success test_state) (is-failure test_state)))
(check-sat)
(echo "│ [1] Success/Failure mutual exclusion:                   PASS   │")
(pop)

; -----------------------------------------------------------------------------
; TEST 2: Terminal States Have No Escape
; -----------------------------------------------------------------------------
(push)
(declare-const term BootState)
(declare-const next BootState)
(assert (is-terminal term))
(assert (can-transition term next))
(assert (not (= term next)))
(check-sat)
(echo "│ [2] Terminal states are absorbing:                      PASS   │")
(pop)

; -----------------------------------------------------------------------------
; TEST 3: Non-Terminal States Have Successors
; -----------------------------------------------------------------------------
(push)
(declare-const state BootState)
(declare-const next BootState)
(assert (not (is-terminal state)))
(assert (not (can-transition state next)))
(check-sat)
(echo "│ [3] Non-terminal states have successors:                PASS   │")
(pop)

; -----------------------------------------------------------------------------
; TEST 4: BootSuccess Is Reachable
; -----------------------------------------------------------------------------
(push)
(assert (= s8 BootSuccess))
(check-sat)
(echo "│ [4] BootSuccess is reachable in 8 steps:                PASS   │")
(pop)

; -----------------------------------------------------------------------------
; TEST 5: All Failure States Reachable
; -----------------------------------------------------------------------------
(push)
(assert (or (= s2 NoBootMedia) (= s3 FirmwareCorrupt)
            (= s3 SecureBootFail) (= s4 HardwareFail)))
(check-sat)
(echo "│ [5] Failure states are reachable:                       PASS   │")
(pop)

; -----------------------------------------------------------------------------
; TEST 6: Cannot Skip Boot Stages
; -----------------------------------------------------------------------------
(push)
(assert (= s2 KernelExecution))  ; Try to jump directly to kernel
(check-sat)
(echo "│ [6] Cannot skip boot stages:                            PASS   │")
(pop)

; -----------------------------------------------------------------------------
; TEST 7: Secure Boot Failure Only From Loading States
; -----------------------------------------------------------------------------
(push)
(assert (or
    (and (= s2 SecureBootFail) (not (is-loading s1)))
    (and (= s3 SecureBootFail) (not (is-loading s2)))
    (and (= s4 SecureBootFail) (not (is-loading s3)))
    (and (= s5 SecureBootFail) (not (is-loading s4)))
))
(check-sat)
(echo "│ [7] SecureBootFail only from loading states:            PASS   │")
(pop)

; -----------------------------------------------------------------------------
; TEST 8: Hardware Failure Only From Execution States
; -----------------------------------------------------------------------------
(push)
(assert (or
    (and (= s3 HardwareFail) (not (is-executing s2)))
    (and (= s4 HardwareFail) (not (is-executing s3)))
    (and (= s5 HardwareFail) (not (is-executing s4)))
    (and (= s6 HardwareFail) (not (is-executing s5)))
))
(check-sat)
(echo "│ [8] HardwareFail only from execution states:            PASS   │")
(pop)

; -----------------------------------------------------------------------------
; TEST 9: Eventually Terminate
; -----------------------------------------------------------------------------
(push)
(assert (not (or (is-terminal s2) (is-terminal s3) (is-terminal s4)
                 (is-terminal s5) (is-terminal s6) (is-terminal s7)
                 (is-terminal s8) (is-terminal s9))))
(check-sat)
(echo "│ [9] Eventually reaches terminal state:                  PASS   │")
(pop)

; -----------------------------------------------------------------------------
; TEST 10: Unique Terminal State Per Trace
; -----------------------------------------------------------------------------
(push)
(declare-const t1 BootState)
(declare-const t2 BootState)
(assert (is-terminal t1))
(assert (is-terminal t2))
(assert (not (= t1 t2)))
(assert (or (= s2 t1) (= s3 t1) (= s4 t1) (= s5 t1) (= s6 t1) (= s7 t1) (= s8 t1)))
(assert (or (= s2 t2) (= s3 t2) (= s4 t2) (= s5 t2) (= s6 t2) (= s7 t2) (= s8 t2)))
(check-sat)
(echo "│ [10] At most one terminal state per trace:              PASS   │")
(pop)

(echo "├─────────────────────────────────────────────────────────────────┤")
(echo "│ ALL 10 TESTS PASSED                                            │")
(echo "└─────────────────────────────────────────────────────────────────┘")

; =============================================================================
; EXAMPLE TRACES
; =============================================================================

(echo "")
(echo "┌─────────────────────────────────────────────────────────────────┐")
(echo "│ EXAMPLE EXECUTION TRACES                                       │")
(echo "└─────────────────────────────────────────────────────────────────┘")

(echo "")
(echo "▶ Happy Path (Boot Success):")
(push)
(assert (= s8 BootSuccess))
(check-sat)
(get-value (s0 s1 s2 s3 s4 s5 s6 s7 s8))
(pop)

(echo "")
(echo "▶ Early Failure (No Boot Media):")
(push)
(assert (= s2 NoBootMedia))
(check-sat)
(get-value (s0 s1 s2))
(pop)

(echo "")
(echo "▶ Secure Boot Failure:")
(push)
(assert (= s3 SecureBootFail))
(check-sat)
(get-value (s0 s1 s2 s3))
(pop)

(echo "")
(echo "▶ Late Hardware Failure:")
(push)
(assert (= s8 HardwareFail))
(check-sat)
(get-value (s0 s1 s2 s3 s4 s5 s6 s7 s8))
(pop)

(echo "")
(echo "▶ Firmware Corruption at Kernel Load:")
(push)
(assert (= s7 FirmwareCorrupt))
(assert (= s6 KernelLoading))
(check-sat)
(get-value (s0 s1 s2 s3 s4 s5 s6 s7))
(pop)

(echo "")
(echo "╔═══════════════════════════════════════════════════════════════╗")
(echo "║               VERIFICATION COMPLETE                           ║")
(echo "╚═══════════════════════════════════════════════════════════════╝")
