; ARM Boot FSA - Transition Relation
; SMT-LIB2 encoding for Z3 verification
; Generated: 2025-12-27
;
; Usage: z3 arm_boot_fsa_transitions.smt2

(set-logic ALL)
(set-option :produce-models true)

; =============================================================================
; TYPE DEFINITIONS (included for standalone use)
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

; Condition state (runtime environment)
(declare-fun cond-holds (BootCondition) Bool)

; =============================================================================
; TRANSITION RELATION
; =============================================================================
; transition(from, to, condition, secure-boot-applies)
; 18 transitions from ontology

(define-fun transition ((from BootState) (to BootState)) Bool
    (or
        ; T1: PowerOn -> ROMExecution [PowerStable]
        (and (= from PowerOn) (= to ROMExecution) (cond-holds PowerStable))

        ; T2: ROMExecution -> BootcodeLoading [BootMediaFound]
        (and (= from ROMExecution) (= to BootcodeLoading) (cond-holds BootMediaFound))

        ; T3: ROMExecution -> NoBootMedia [NOT BootMediaFound]
        (and (= from ROMExecution) (= to NoBootMedia) (not (cond-holds BootMediaFound)))

        ; T4: BootcodeLoading -> BootcodeExecution [FileValid]
        (and (= from BootcodeLoading) (= to BootcodeExecution) (cond-holds FileValid))

        ; T5: BootcodeLoading -> FirmwareCorrupt [NOT FileValid]
        (and (= from BootcodeLoading) (= to FirmwareCorrupt) (not (cond-holds FileValid)))

        ; T6: BootcodeExecution -> StartElfLoading [HardwareOK]
        (and (= from BootcodeExecution) (= to StartElfLoading) (cond-holds HardwareOK))

        ; T7: BootcodeExecution -> HardwareFail [NOT HardwareOK]
        (and (= from BootcodeExecution) (= to HardwareFail) (not (cond-holds HardwareOK)))

        ; T8: StartElfLoading -> StartElfExecution [FileValid]
        (and (= from StartElfLoading) (= to StartElfExecution) (cond-holds FileValid))

        ; T9: StartElfLoading -> FirmwareCorrupt [NOT FileValid]
        (and (= from StartElfLoading) (= to FirmwareCorrupt) (not (cond-holds FileValid)))

        ; T10: StartElfExecution -> KernelLoading [HardwareOK]
        (and (= from StartElfExecution) (= to KernelLoading) (cond-holds HardwareOK))

        ; T11: StartElfExecution -> HardwareFail [NOT HardwareOK]
        (and (= from StartElfExecution) (= to HardwareFail) (not (cond-holds HardwareOK)))

        ; T12: KernelLoading -> KernelExecution [KernelValid]
        (and (= from KernelLoading) (= to KernelExecution) (cond-holds KernelValid))

        ; T13: KernelLoading -> FirmwareCorrupt [NOT KernelValid]
        (and (= from KernelLoading) (= to FirmwareCorrupt) (not (cond-holds KernelValid)))

        ; T14: KernelExecution -> BootSuccess [always succeeds at this point]
        (and (= from KernelExecution) (= to BootSuccess))

        ; T15: KernelExecution -> HardwareFail [runtime hardware failure]
        (and (= from KernelExecution) (= to HardwareFail))
    ))

; Secure boot transitions (for Pi4/Pi5 only)
(define-fun transition-secure ((from BootState) (to BootState) (model PiModel)) Bool
    (and (or (= model Pi4) (= model Pi5))
         (or
             ; T16: BootcodeLoading -> SecureBootFail [NOT SignatureValid]
             (and (= from BootcodeLoading) (= to SecureBootFail) (not (cond-holds SignatureValid)))

             ; T17: StartElfLoading -> SecureBootFail [NOT SignatureValid]
             (and (= from StartElfLoading) (= to SecureBootFail) (not (cond-holds SignatureValid)))

             ; T18: KernelLoading -> SecureBootFail [NOT SignatureValid]
             (and (= from KernelLoading) (= to SecureBootFail) (not (cond-holds SignatureValid)))
         )))

; Combined transition relation
(define-fun can-transition ((from BootState) (to BootState) (model PiModel)) Bool
    (or (transition from to)
        (transition-secure from to model)))

; =============================================================================
; TRANSITION PROPERTIES
; =============================================================================

; Terminal states have no outgoing transitions
(define-fun is-terminal ((s BootState)) Bool
    (or (= s BootSuccess) (= s NoBootMedia) (= s FirmwareCorrupt)
        (= s SecureBootFail) (= s HardwareFail)))

; Non-terminal states must have at least one outgoing transition
(define-fun has-outgoing ((s BootState)) Bool
    (not (is-terminal s)))

; =============================================================================
; VERIFICATION: Check transition relation is satisfiable
; =============================================================================

(echo "=== Transition Relation Verification ===")

; Verify: At least one transition exists
(push)
(declare-const s1 BootState)
(declare-const s2 BootState)
(assert (transition s1 s2))
(check-sat)
(echo "Transition relation has at least one valid transition:")
(get-value (s1 s2))
(pop)

; Verify: PowerOn has outgoing transition
(push)
(declare-const next BootState)
(assert (transition PowerOn next))
(check-sat)
(echo "PowerOn can transition to:")
(get-value (next))
(pop)

; Verify: BootSuccess is terminal (no outgoing)
(push)
(declare-const next BootState)
(assert (transition BootSuccess next))
(check-sat)
(echo "BootSuccess has outgoing transitions (should be unsat):")
(pop)

(echo "=== Transition definitions loaded ===")
