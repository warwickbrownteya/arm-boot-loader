; ARM Boot FSA - Bounded Model Checking
; SMT-LIB2 encoding for Z3 verification
; Generated: 2025-12-27
;
; This file performs bounded model checking on the boot FSA
; Verifies temporal properties over bounded traces
;
; Usage: z3 arm_boot_fsa_bmc.smt2

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
; BOUNDED TRACE INFRASTRUCTURE
; =============================================================================

; 15-step bounded trace (covers all paths with margin)
(declare-const step_0 BootState)
(declare-const step_1 BootState)
(declare-const step_2 BootState)
(declare-const step_3 BootState)
(declare-const step_4 BootState)
(declare-const step_5 BootState)
(declare-const step_6 BootState)
(declare-const step_7 BootState)
(declare-const step_8 BootState)
(declare-const step_9 BootState)
(declare-const step_10 BootState)
(declare-const step_11 BootState)
(declare-const step_12 BootState)
(declare-const step_13 BootState)
(declare-const step_14 BootState)

; State at step accessor (for quantifier-free queries)
(define-fun state-at ((i Int)) BootState
    (ite (= i 0) step_0
    (ite (= i 1) step_1
    (ite (= i 2) step_2
    (ite (= i 3) step_3
    (ite (= i 4) step_4
    (ite (= i 5) step_5
    (ite (= i 6) step_6
    (ite (= i 7) step_7
    (ite (= i 8) step_8
    (ite (= i 9) step_9
    (ite (= i 10) step_10
    (ite (= i 11) step_11
    (ite (= i 12) step_12
    (ite (= i 13) step_13
    step_14)))))))))))))))

; =============================================================================
; TRANSITION RELATION
; =============================================================================

(define-fun valid-transition ((from BootState) (to BootState)) Bool
    (or
        ; Normal transitions
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
        ; Terminal self-loops
        (and (= from BootSuccess) (= to BootSuccess))
        (and (= from NoBootMedia) (= to NoBootMedia))
        (and (= from FirmwareCorrupt) (= to FirmwareCorrupt))
        (and (= from SecureBootFail) (= to SecureBootFail))
        (and (= from HardwareFail) (= to HardwareFail))
    ))

; State predicates
(define-fun is-terminal ((s BootState)) Bool
    (or (= s BootSuccess) (= s NoBootMedia) (= s FirmwareCorrupt)
        (= s SecureBootFail) (= s HardwareFail)))

(define-fun is-failure ((s BootState)) Bool
    (or (= s NoBootMedia) (= s FirmwareCorrupt)
        (= s SecureBootFail) (= s HardwareFail)))

(define-fun is-success ((s BootState)) Bool
    (= s BootSuccess))

(define-fun is-loading ((s BootState)) Bool
    (or (= s BootcodeLoading) (= s StartElfLoading) (= s KernelLoading)))

(define-fun is-executing ((s BootState)) Bool
    (or (= s ROMExecution) (= s BootcodeExecution)
        (= s StartElfExecution) (= s KernelExecution)))

; =============================================================================
; TRACE CONSTRAINTS
; =============================================================================

; Initial state
(assert (= step_0 PowerOn))

; All transitions are valid
(assert (valid-transition step_0 step_1))
(assert (valid-transition step_1 step_2))
(assert (valid-transition step_2 step_3))
(assert (valid-transition step_3 step_4))
(assert (valid-transition step_4 step_5))
(assert (valid-transition step_5 step_6))
(assert (valid-transition step_6 step_7))
(assert (valid-transition step_7 step_8))
(assert (valid-transition step_8 step_9))
(assert (valid-transition step_9 step_10))
(assert (valid-transition step_10 step_11))
(assert (valid-transition step_11 step_12))
(assert (valid-transition step_12 step_13))
(assert (valid-transition step_13 step_14))

; =============================================================================
; BMC PROPERTY 1: AG (Globally) Properties
; =============================================================================
; AG phi: phi holds at all states in all traces

(echo "")
(echo "=================================================================")
(echo "BMC PROPERTY VERIFICATION")
(echo "=================================================================")

(echo "")
(echo "--- Property 1: AG (no state is both success and failure) ---")

(push)
; Violation: some state is both success and failure
(assert (or
    (and (is-success step_0) (is-failure step_0))
    (and (is-success step_1) (is-failure step_1))
    (and (is-success step_2) (is-failure step_2))
    (and (is-success step_3) (is-failure step_3))
    (and (is-success step_4) (is-failure step_4))
    (and (is-success step_5) (is-failure step_5))
    (and (is-success step_6) (is-failure step_6))
    (and (is-success step_7) (is-failure step_7))
    (and (is-success step_8) (is-failure step_8))
))
(check-sat)
(echo "Violation found (should be UNSAT - success/failure are disjoint):")
(pop)

; =============================================================================
; BMC PROPERTY 2: AF (Eventually) Properties
; =============================================================================
; AF phi: phi eventually holds (within bound)

(echo "")
(echo "--- Property 2: AF (eventually reach terminal state) ---")

(push)
; Within 10 steps, reach a terminal state
(assert (or (is-terminal step_1) (is-terminal step_2) (is-terminal step_3)
            (is-terminal step_4) (is-terminal step_5) (is-terminal step_6)
            (is-terminal step_7) (is-terminal step_8) (is-terminal step_9)
            (is-terminal step_10)))
(check-sat)
(echo "Terminal state reachable within 10 steps (should be SAT):")
(get-value (step_0 step_1 step_2 step_3 step_4 step_5 step_6 step_7 step_8))
(pop)

; =============================================================================
; BMC PROPERTY 3: Before-After Properties
; =============================================================================
; Loading states must be followed by either execution or failure

(echo "")
(echo "--- Property 3: Loading -> (Execution OR Failure) ---")

(push)
; Violation: loading state followed by something other than execution or failure
(assert (or
    ; BootcodeLoading not followed by BootcodeExecution or failure
    (and (= step_2 BootcodeLoading)
         (not (= step_3 BootcodeExecution))
         (not (is-failure step_3)))
    ; Similar for other loading states
    (and (= step_4 StartElfLoading)
         (not (= step_5 StartElfExecution))
         (not (is-failure step_5)))
    (and (= step_6 KernelLoading)
         (not (= step_7 KernelExecution))
         (not (is-failure step_7)))
))
(check-sat)
(echo "Loading state violation found (should be UNSAT):")
(pop)

; =============================================================================
; BMC PROPERTY 4: No Premature Success
; =============================================================================
; Cannot reach BootSuccess without going through KernelExecution

(echo "")
(echo "--- Property 4: No Premature Success ---")

(push)
; Violation: BootSuccess appears before KernelExecution in trace
(declare-const success_step Int)
(declare-const kernel_step Int)

; Find first occurrence of BootSuccess
(assert (or
    (and (= success_step 1) (= step_1 BootSuccess))
    (and (= success_step 2) (= step_2 BootSuccess))
    (and (= success_step 3) (= step_3 BootSuccess))
    (and (= success_step 4) (= step_4 BootSuccess))
    (and (= success_step 5) (= step_5 BootSuccess))
    (and (= success_step 6) (= step_6 BootSuccess))
    (and (= success_step 7) (= step_7 BootSuccess))
    (and (= success_step 8) (= step_8 BootSuccess))
))

; No KernelExecution appears before success_step
(assert (not (or
    (and (< 1 success_step) (= step_1 KernelExecution))
    (and (< 2 success_step) (= step_2 KernelExecution))
    (and (< 3 success_step) (= step_3 KernelExecution))
    (and (< 4 success_step) (= step_4 KernelExecution))
    (and (< 5 success_step) (= step_5 KernelExecution))
    (and (< 6 success_step) (= step_6 KernelExecution))
    (and (< 7 success_step) (= step_7 KernelExecution))
)))

(check-sat)
(echo "Premature success found (should be UNSAT):")
(pop)

; =============================================================================
; BMC PROPERTY 5: Secure Boot Check (for Pi4/Pi5)
; =============================================================================
; SecureBootFail can only occur from loading states

(echo "")
(echo "--- Property 5: SecureBootFail only from loading states ---")

(push)
; Violation: SecureBootFail reached from non-loading state
(assert (or
    (and (= step_2 SecureBootFail) (not (is-loading step_1)))
    (and (= step_3 SecureBootFail) (not (is-loading step_2)))
    (and (= step_4 SecureBootFail) (not (is-loading step_3)))
    (and (= step_5 SecureBootFail) (not (is-loading step_4)))
    (and (= step_6 SecureBootFail) (not (is-loading step_5)))
    (and (= step_7 SecureBootFail) (not (is-loading step_6)))
))
(check-sat)
(echo "SecureBootFail from non-loading state (should be UNSAT):")
(pop)

; =============================================================================
; BMC PROPERTY 6: Hardware Failure Points
; =============================================================================
; HardwareFail can only occur from execution states

(echo "")
(echo "--- Property 6: HardwareFail only from execution states ---")

(push)
; Violation: HardwareFail reached from non-execution state
(assert (or
    (and (= step_3 HardwareFail) (not (is-executing step_2)))
    (and (= step_4 HardwareFail) (not (is-executing step_3)))
    (and (= step_5 HardwareFail) (not (is-executing step_4)))
    (and (= step_6 HardwareFail) (not (is-executing step_5)))
    (and (= step_7 HardwareFail) (not (is-executing step_6)))
    (and (= step_8 HardwareFail) (not (is-executing step_7)))
    (and (= step_9 HardwareFail) (not (is-executing step_8)))
))
(check-sat)
(echo "HardwareFail from non-execution state (should be UNSAT):")
(pop)

; =============================================================================
; BMC PROPERTY 7: Progress Guarantee
; =============================================================================
; Non-terminal states always make forward progress

(echo "")
(echo "--- Property 7: Forward Progress ---")

; State ordering
(define-fun state-order ((s BootState)) Int
    (ite (= s PowerOn) 0
    (ite (= s ROMExecution) 1
    (ite (= s BootcodeLoading) 2
    (ite (= s BootcodeExecution) 3
    (ite (= s StartElfLoading) 4
    (ite (= s StartElfExecution) 5
    (ite (= s KernelLoading) 6
    (ite (= s KernelExecution) 7
    8)))))))))  ; All terminal states at level 8

(push)
; Violation: non-terminal state doesn't increase order
(assert (or
    (and (not (is-terminal step_0)) (>= (state-order step_0) (state-order step_1)))
    (and (not (is-terminal step_1)) (>= (state-order step_1) (state-order step_2)))
    (and (not (is-terminal step_2)) (>= (state-order step_2) (state-order step_3)))
    (and (not (is-terminal step_3)) (>= (state-order step_3) (state-order step_4)))
    (and (not (is-terminal step_4)) (>= (state-order step_4) (state-order step_5)))
    (and (not (is-terminal step_5)) (>= (state-order step_5) (state-order step_6)))
    (and (not (is-terminal step_6)) (>= (state-order step_6) (state-order step_7)))
    (and (not (is-terminal step_7)) (>= (state-order step_7) (state-order step_8)))
))
(check-sat)
(echo "Non-progress found (should be UNSAT):")
(pop)

; =============================================================================
; COUNTEREXAMPLE GENERATION
; =============================================================================

(echo "")
(echo "--- Generating Example Traces ---")

; Example 1: Successful boot trace
(echo "")
(echo "Example 1: Successful boot path")
(push)
(assert (= step_8 BootSuccess))
(check-sat)
(get-value (step_0 step_1 step_2 step_3 step_4 step_5 step_6 step_7 step_8))
(pop)

; Example 2: Fast failure (no boot media)
(echo "")
(echo "Example 2: No boot media failure")
(push)
(assert (= step_2 NoBootMedia))
(check-sat)
(get-value (step_0 step_1 step_2))
(pop)

; Example 3: Secure boot failure path
(echo "")
(echo "Example 3: Secure boot failure")
(push)
(assert (= step_3 SecureBootFail))
(check-sat)
(get-value (step_0 step_1 step_2 step_3))
(pop)

; Example 4: Late hardware failure
(echo "")
(echo "Example 4: Late hardware failure (at kernel execution)")
(push)
(assert (= step_8 HardwareFail))
(assert (= step_7 KernelExecution))
(check-sat)
(get-value (step_0 step_1 step_2 step_3 step_4 step_5 step_6 step_7 step_8))
(pop)

(echo "")
(echo "=================================================================")
(echo "BOUNDED MODEL CHECKING COMPLETE")
(echo "=================================================================")
