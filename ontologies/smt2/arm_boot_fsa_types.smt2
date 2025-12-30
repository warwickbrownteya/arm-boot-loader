; ARM Boot FSA - Core Type Definitions
; SMT-LIB2 encoding for Z3 verification
; Generated: 2025-12-27
;
; Usage: z3 arm_boot_fsa_types.smt2
;        z3 -smt2 arm_boot_fsa_types.smt2

(set-logic ALL)
(set-option :produce-models true)

; =============================================================================
; BOOT STATE ENUMERATION
; =============================================================================
; 13 states from arm_boot_fsa_ontology.n3

(declare-datatypes () ((BootState
    PowerOn           ; Initial state after power on
    ROMExecution      ; ROM code executing, searching for boot media
    BootcodeLoading   ; Loading bootcode.bin from boot media
    BootcodeExecution ; Executing bootcode.bin, initializing SDRAM
    StartElfLoading   ; Loading start.elf from boot media
    StartElfExecution ; Executing start.elf, hardware initialization
    KernelLoading     ; Loading kernel image
    KernelExecution   ; Executing kernel, OS boot
    BootSuccess       ; Successful boot, OS running (TERMINAL - SUCCESS)
    NoBootMedia       ; Failure: No bootable media found (TERMINAL - FAILURE)
    FirmwareCorrupt   ; Failure: Corrupt or missing firmware (TERMINAL - FAILURE)
    SecureBootFail    ; Failure: Secure boot verification failed (TERMINAL - FAILURE)
    HardwareFail      ; Failure: Hardware initialization failed (TERMINAL - FAILURE)
)))

; =============================================================================
; BOOT CONDITIONS
; =============================================================================
; 6 conditions that guard transitions

(declare-datatypes () ((BootCondition
    PowerStable       ; Power supply stable
    BootMediaFound    ; Bootable media detected
    FileValid         ; Firmware file exists and valid
    SignatureValid    ; Digital signature verified (secure boot)
    HardwareOK        ; Hardware initialization successful
    KernelValid       ; Kernel image valid and compatible
)))

; =============================================================================
; RASPBERRY PI MODELS
; =============================================================================
; Different models have different capabilities

(declare-datatypes () ((PiModel
    Pi1       ; ARM11 - no USB boot, no secure boot
    Pi2       ; Cortex-A7 - no secure boot
    Pi3       ; Cortex-A53 - no secure boot
    Pi4       ; Cortex-A72 - USB boot, secure boot
    Pi5       ; Cortex-A76 - USB boot, secure boot, NVMe
    PiZero    ; ARM11 - minimal features
    PiZero2   ; Cortex-A53 - like Pi3
)))

; =============================================================================
; STATE CLASSIFICATION PREDICATES
; =============================================================================

; Terminal states (no outgoing transitions)
(define-fun is-terminal ((s BootState)) Bool
    (or (= s BootSuccess)
        (= s NoBootMedia)
        (= s FirmwareCorrupt)
        (= s SecureBootFail)
        (= s HardwareFail)))

; Success state
(define-fun is-success ((s BootState)) Bool
    (= s BootSuccess))

; Failure states
(define-fun is-failure ((s BootState)) Bool
    (or (= s NoBootMedia)
        (= s FirmwareCorrupt)
        (= s SecureBootFail)
        (= s HardwareFail)))

; Initial state
(define-fun is-initial ((s BootState)) Bool
    (= s PowerOn))

; States where secure boot applies (Pi4, Pi5 only)
(define-fun has-secure-boot ((m PiModel)) Bool
    (or (= m Pi4) (= m Pi5)))

; =============================================================================
; CONDITION FUNCTIONS
; =============================================================================
; Condition variables - represent runtime environment

(declare-fun cond-holds (BootCondition) Bool)

; Convenience predicates
(define-fun power-stable () Bool (cond-holds PowerStable))
(define-fun boot-media-found () Bool (cond-holds BootMediaFound))
(define-fun file-valid () Bool (cond-holds FileValid))
(define-fun signature-valid () Bool (cond-holds SignatureValid))
(define-fun hardware-ok () Bool (cond-holds HardwareOK))
(define-fun kernel-valid () Bool (cond-holds KernelValid))

; =============================================================================
; BASIC VERIFICATION
; =============================================================================

; Verify type system is satisfiable
(check-sat)
(echo "Type definitions loaded successfully")

; Show all states
(echo "Boot States: PowerOn, ROMExecution, BootcodeLoading, BootcodeExecution,")
(echo "             StartElfLoading, StartElfExecution, KernelLoading, KernelExecution,")
(echo "             BootSuccess, NoBootMedia, FirmwareCorrupt, SecureBootFail, HardwareFail")
