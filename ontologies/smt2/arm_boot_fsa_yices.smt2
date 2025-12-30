; ARM Boot FSA - Yices Compatible Version
; Uses integer encoding for states (Yices has limited datatype support)
; Generated: 2025-12-27

(set-logic QF_LIA)

; =============================================================================
; STATE ENCODING (as integers 0-12)
; =============================================================================

; State constants
(define-fun PowerOn () Int 0)
(define-fun ROMExecution () Int 1)
(define-fun BootcodeLoading () Int 2)
(define-fun BootcodeExecution () Int 3)
(define-fun StartElfLoading () Int 4)
(define-fun StartElfExecution () Int 5)
(define-fun KernelLoading () Int 6)
(define-fun KernelExecution () Int 7)
(define-fun BootSuccess () Int 8)
(define-fun NoBootMedia () Int 9)
(define-fun FirmwareCorrupt () Int 10)
(define-fun SecureBootFail () Int 11)
(define-fun HardwareFail () Int 12)

; State classification
(define-fun is-terminal ((s Int)) Bool
    (or (= s 8) (= s 9) (= s 10) (= s 11) (= s 12)))

(define-fun is-failure ((s Int)) Bool
    (or (= s 9) (= s 10) (= s 11) (= s 12)))

(define-fun is-success ((s Int)) Bool (= s 8))

(define-fun is-loading ((s Int)) Bool
    (or (= s 2) (= s 4) (= s 6)))

(define-fun is-executing ((s Int)) Bool
    (or (= s 1) (= s 3) (= s 5) (= s 7)))

(define-fun is-valid-state ((s Int)) Bool
    (and (>= s 0) (<= s 12)))

; Transition relation (from, to)
(define-fun can-transition ((from Int) (to Int)) Bool
    (or
        (and (= from 0) (= to 1))    ; PowerOn -> ROMExecution
        (and (= from 1) (= to 2))    ; ROMExecution -> BootcodeLoading
        (and (= from 1) (= to 9))    ; ROMExecution -> NoBootMedia
        (and (= from 2) (= to 3))    ; BootcodeLoading -> BootcodeExecution
        (and (= from 2) (= to 10))   ; BootcodeLoading -> FirmwareCorrupt
        (and (= from 2) (= to 11))   ; BootcodeLoading -> SecureBootFail
        (and (= from 3) (= to 4))    ; BootcodeExecution -> StartElfLoading
        (and (= from 3) (= to 12))   ; BootcodeExecution -> HardwareFail
        (and (= from 4) (= to 5))    ; StartElfLoading -> StartElfExecution
        (and (= from 4) (= to 10))   ; StartElfLoading -> FirmwareCorrupt
        (and (= from 4) (= to 11))   ; StartElfLoading -> SecureBootFail
        (and (= from 5) (= to 6))    ; StartElfExecution -> KernelLoading
        (and (= from 5) (= to 12))   ; StartElfExecution -> HardwareFail
        (and (= from 6) (= to 7))    ; KernelLoading -> KernelExecution
        (and (= from 6) (= to 10))   ; KernelLoading -> FirmwareCorrupt
        (and (= from 6) (= to 11))   ; KernelLoading -> SecureBootFail
        (and (= from 7) (= to 8))    ; KernelExecution -> BootSuccess
        (and (= from 7) (= to 12))   ; KernelExecution -> HardwareFail
        ; Terminal self-loops
        (and (= from 8) (= to 8))
        (and (= from 9) (= to 9))
        (and (= from 10) (= to 10))
        (and (= from 11) (= to 11))
        (and (= from 12) (= to 12))
    ))

; =============================================================================
; TEST 1: Success/Failure mutual exclusion
; =============================================================================
(declare-fun test_state () Int)
(assert (is-valid-state test_state))
(assert (and (is-success test_state) (is-failure test_state)))
(check-sat)  ; Expected: unsat
(reset)

(set-logic QF_LIA)

; Redefine state constants
(define-fun PowerOn () Int 0)
(define-fun ROMExecution () Int 1)
(define-fun BootcodeLoading () Int 2)
(define-fun BootcodeExecution () Int 3)
(define-fun StartElfLoading () Int 4)
(define-fun StartElfExecution () Int 5)
(define-fun KernelLoading () Int 6)
(define-fun KernelExecution () Int 7)
(define-fun BootSuccess () Int 8)
(define-fun NoBootMedia () Int 9)
(define-fun FirmwareCorrupt () Int 10)
(define-fun SecureBootFail () Int 11)
(define-fun HardwareFail () Int 12)

(define-fun is-terminal ((s Int)) Bool
    (or (= s 8) (= s 9) (= s 10) (= s 11) (= s 12)))

(define-fun is-loading ((s Int)) Bool
    (or (= s 2) (= s 4) (= s 6)))

(define-fun can-transition ((from Int) (to Int)) Bool
    (or
        (and (= from 0) (= to 1))
        (and (= from 1) (= to 2))
        (and (= from 1) (= to 9))
        (and (= from 2) (= to 3))
        (and (= from 2) (= to 10))
        (and (= from 2) (= to 11))
        (and (= from 3) (= to 4))
        (and (= from 3) (= to 12))
        (and (= from 4) (= to 5))
        (and (= from 4) (= to 10))
        (and (= from 4) (= to 11))
        (and (= from 5) (= to 6))
        (and (= from 5) (= to 12))
        (and (= from 6) (= to 7))
        (and (= from 6) (= to 10))
        (and (= from 6) (= to 11))
        (and (= from 7) (= to 8))
        (and (= from 7) (= to 12))
        (and (= from 8) (= to 8))
        (and (= from 9) (= to 9))
        (and (= from 10) (= to 10))
        (and (= from 11) (= to 11))
        (and (= from 12) (= to 12))
    ))

; =============================================================================
; TEST 2: Boot success reachable in 8 steps
; =============================================================================
(declare-fun s0 () Int)
(declare-fun s1 () Int)
(declare-fun s2 () Int)
(declare-fun s3 () Int)
(declare-fun s4 () Int)
(declare-fun s5 () Int)
(declare-fun s6 () Int)
(declare-fun s7 () Int)
(declare-fun s8 () Int)

(assert (= s0 0))  ; PowerOn
(assert (can-transition s0 s1))
(assert (can-transition s1 s2))
(assert (can-transition s2 s3))
(assert (can-transition s3 s4))
(assert (can-transition s4 s5))
(assert (can-transition s5 s6))
(assert (can-transition s6 s7))
(assert (can-transition s7 s8))
(assert (= s8 8))  ; BootSuccess

(check-sat)  ; Expected: sat
