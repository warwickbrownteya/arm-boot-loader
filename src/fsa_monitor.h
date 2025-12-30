/* FSA Monitor and Interlocks Header for Bootloader */

#ifndef FSA_MONITOR_H
#define FSA_MONITOR_H

#include <stdint.h>

// FSA States - Hyper-modular with intermediate states for alternative configurations
typedef enum {
    // Power-on and early init
    STATE_POWER_ON,
    STATE_EARLY_HW_INIT,

    // Bootcode phase with intermediates
    STATE_BOOTCODE_SOURCE_SELECT,
    STATE_BOOTCODE_LOADING,
    STATE_BOOTCODE_VALIDATION,
    STATE_BOOTCODE_EXEC,
    STATE_BOOTCODE_CONFIG_PARSE,

    // Hardware initialization phases
    STATE_CORE_DRIVER_INIT,
    STATE_BSP_DRIVER_INIT,
    STATE_HW_VALIDATION,

    // Configuration phase
    STATE_CONFIG_LOADING,
    STATE_CONFIG_PARSING,
    STATE_CONFIG_VALIDATION,
    STATE_CONFIG_APPLICATION,

    // Start.elf phase with alternatives
    STATE_STARTELF_SOURCE_SELECT,
    STATE_STARTELF_LOADING,
    STATE_STARTELF_VALIDATION,
    STATE_STARTELF_EXEC,

    // Kernel phase with multiple sources and intermediates
    STATE_KERNEL_SOURCE_SELECT,
    STATE_KERNEL_LOADING,
    STATE_KERNEL_VALIDATION,
    STATE_INITRD_LOADING,
    STATE_DTB_LOADING,
    STATE_KERNEL_PARAMS_SETUP,
    STATE_KERNEL_EXEC,

    // Alternative boot paths
    STATE_NETWORK_BOOT_INIT,
    STATE_PXE_BOOT_EXEC,
    STATE_USB_BOOT_INIT,
    STATE_FAILSAFE_BOOT_INIT,
    STATE_RECOVERY_BOOT_INIT,

    // Modular component loading
    STATE_MODULE_DEPENDENCY_RESOLVE,
    STATE_MODULE_LOADING,
    STATE_MODULE_VALIDATION,

    // Security and trust states (Kripke modal necessity)
    STATE_SECURITY_ATTESTATION,
    STATE_FIRMWARE_MEASUREMENT,
    STATE_BOOT_POLICY_VALIDATION,
    STATE_TRUSTED_EXECUTION_INIT,

    // Configuration coherence (Grothendieck topology)
    STATE_CONFIGURATION_COHERENCE_CHECK,
    STATE_DEPENDENCY_GRAPH_ANALYSIS,

    // Verification states (Tarski model theory)
    STATE_SEMANTIC_VALIDATION,
    STATE_CONSISTENCY_CHECK,

    // Final states
    STATE_SUCCESS,
    STATE_FAILURE,
    STATE_HALT
} boot_state_t;

// State transition validation
typedef enum {
    TRANSITION_VALID,
    TRANSITION_INVALID,
    TRANSITION_BLOCKED
} transition_status_t;

// Safety interlock types
typedef enum {
    INTERLOCK_NONE,
    INTERLOCK_HARDWARE_NOT_READY,
    INTERLOCK_MEMORY_CORRUPTION,
    INTERLOCK_TIMEOUT,
    INTERLOCK_SECURITY_VIOLATION,
    INTERLOCK_RESOURCE_EXHAUSTED
} interlock_type_t;

// State monitoring data
typedef struct {
    boot_state_t current_state;
    boot_state_t previous_state;
    uint64_t state_entry_time;
    uint32_t state_timeout_ms;
    uint32_t retry_count;
    interlock_type_t active_interlock;
    uint8_t safety_flags;
} state_monitor_t;

// State history for debugging
#define STATE_HISTORY_SIZE 16
typedef struct {
    boot_state_t state;
    uint64_t timestamp;
    transition_status_t transition_result;
    interlock_type_t interlock;
} state_history_entry_t;

// FSA monitoring functions
void fsa_monitor_init(void);
transition_status_t fsa_validate_transition(boot_state_t from_state, boot_state_t to_state);
int fsa_check_interlocks(boot_state_t target_state);
void fsa_update_state(boot_state_t new_state);
void fsa_monitor_tick(void);
void fsa_log_transition(boot_state_t from, boot_state_t to, transition_status_t status);
void fsa_handle_timeout(void);
void fsa_activate_interlock(interlock_type_t type);
void fsa_clear_interlock(void);

// State timeout configuration - comprehensive for all intermediate states
#define TIMEOUT_POWER_ON              1000   // 1 second
#define TIMEOUT_EARLY_HW_INIT         2000   // 2 seconds
#define TIMEOUT_BOOTCODE_SOURCE_SELECT 1000  // 1 second
#define TIMEOUT_BOOTCODE_LOADING      5000   // 5 seconds
#define TIMEOUT_BOOTCODE_VALIDATION   2000   // 2 seconds
#define TIMEOUT_BOOTCODE_EXEC         3000   // 3 seconds
#define TIMEOUT_BOOTCODE_CONFIG_PARSE 2000   // 2 seconds
#define TIMEOUT_CORE_DRIVER_INIT      3000   // 3 seconds
#define TIMEOUT_BSP_DRIVER_INIT       5000   // 5 seconds
#define TIMEOUT_HW_VALIDATION         2000   // 2 seconds
#define TIMEOUT_CONFIG_LOADING        3000   // 3 seconds
#define TIMEOUT_CONFIG_PARSING        2000   // 2 seconds
#define TIMEOUT_CONFIG_VALIDATION     1000   // 1 second
#define TIMEOUT_CONFIG_APPLICATION    1000   // 1 second
#define TIMEOUT_STARTELF_SOURCE_SELECT 1000  // 1 second
#define TIMEOUT_STARTELF_LOADING      5000   // 5 seconds
#define TIMEOUT_STARTELF_VALIDATION   2000   // 2 seconds
#define TIMEOUT_STARTELF_EXEC         10000  // 10 seconds
#define TIMEOUT_KERNEL_SOURCE_SELECT  1000   // 1 second
#define TIMEOUT_KERNEL_LOADING        10000  // 10 seconds
#define TIMEOUT_KERNEL_VALIDATION     2000   // 2 seconds
#define TIMEOUT_INITRD_LOADING        5000   // 5 seconds
#define TIMEOUT_DTB_LOADING           3000   // 3 seconds
#define TIMEOUT_KERNEL_PARAMS_SETUP   1000   // 1 second
#define TIMEOUT_KERNEL_EXEC           5000   // 5 seconds
#define TIMEOUT_NETWORK_BOOT_INIT     5000   // 5 seconds
#define TIMEOUT_USB_BOOT_INIT         3000   // 3 seconds
#define TIMEOUT_FAILSAFE_BOOT_INIT    2000   // 2 seconds
#define TIMEOUT_RECOVERY_BOOT_INIT    2000   // 2 seconds
#define TIMEOUT_MODULE_DEPENDENCY_RESOLVE 2000  // 2 seconds
#define TIMEOUT_MODULE_LOADING        5000   // 5 seconds
#define TIMEOUT_MODULE_VALIDATION     2000   // 2 seconds
#define TIMEOUT_SECURITY_ATTESTATION  3000   // 3 seconds
#define TIMEOUT_FIRMWARE_MEASUREMENT  2000   // 2 seconds
#define TIMEOUT_BOOT_POLICY_VALIDATION 1500  // 1.5 seconds
#define TIMEOUT_TRUSTED_EXECUTION_INIT 2500  // 2.5 seconds
#define TIMEOUT_CONFIGURATION_COHERENCE_CHECK 2000  // 2 seconds
#define TIMEOUT_DEPENDENCY_GRAPH_ANALYSIS 3000  // 3 seconds
#define TIMEOUT_SEMANTIC_VALIDATION  2000   // 2 seconds
#define TIMEOUT_CONSISTENCY_CHECK    1500   // 1.5 seconds

// Safety flags
#define SAFETY_FLAG_HARDWARE_READY    (1 << 0)
#define SAFETY_FLAG_MEMORY_INTEGRITY  (1 << 1)
#define SAFETY_FLAG_SECURITY_VALID    (1 << 2)
#define SAFETY_FLAG_RESOURCES_OK      (1 << 3)

// Recovery actions
typedef enum {
    RECOVERY_NONE,
    RECOVERY_RETRY,
    RECOVERY_RESET,
    RECOVERY_FAILSAFE,
    RECOVERY_HALT
} recovery_action_t;

// ============================================================================
// FORMALLY VERIFIED PROPERTIES (from ontology proofs)
// Proven by: Z3, Vampire, Prover9, Lean 4, SWI-Prolog
// ============================================================================

// Failure type classification (Proven: SecureBootFail only from loading states,
//                              HardwareFail only from execution states)
typedef enum {
    FAILURE_NONE,
    FAILURE_NO_BOOT_MEDIA,      // From ROM execution only
    FAILURE_FIRMWARE_CORRUPT,   // From any loading state
    FAILURE_SECURE_BOOT_FAIL,   // From loading states only (Pi4/Pi5)
    FAILURE_HARDWARE_FAIL       // From execution states only
} failure_type_t;

// Abstract state classification (maps 44 states to 13 verified abstract states)
typedef enum {
    ABSTRACT_POWER_ON,
    ABSTRACT_ROM_EXECUTION,
    ABSTRACT_BOOTCODE_LOADING,
    ABSTRACT_BOOTCODE_EXECUTION,
    ABSTRACT_STARTELF_LOADING,
    ABSTRACT_STARTELF_EXECUTION,
    ABSTRACT_KERNEL_LOADING,
    ABSTRACT_KERNEL_EXECUTION,
    ABSTRACT_BOOT_SUCCESS,
    ABSTRACT_NO_BOOT_MEDIA,
    ABSTRACT_FIRMWARE_CORRUPT,
    ABSTRACT_SECURE_BOOT_FAIL,
    ABSTRACT_HARDWARE_FAIL
} abstract_state_t;

// State classification functions (based on verified FSA properties)
static inline int fsa_is_terminal(boot_state_t s) {
    return (s == STATE_SUCCESS || s == STATE_FAILURE || s == STATE_HALT);
}

static inline int fsa_is_success(boot_state_t s) {
    return (s == STATE_SUCCESS);
}

static inline int fsa_is_failure(boot_state_t s) {
    return (s == STATE_FAILURE || s == STATE_HALT);
}

static inline int fsa_is_loading(boot_state_t s) {
    return (s == STATE_BOOTCODE_LOADING || s == STATE_BOOTCODE_VALIDATION ||
            s == STATE_STARTELF_LOADING || s == STATE_STARTELF_VALIDATION ||
            s == STATE_KERNEL_LOADING || s == STATE_KERNEL_VALIDATION ||
            s == STATE_INITRD_LOADING || s == STATE_DTB_LOADING ||
            s == STATE_CONFIG_LOADING || s == STATE_MODULE_LOADING);
}

static inline int fsa_is_execution(boot_state_t s) {
    return (s == STATE_BOOTCODE_EXEC || s == STATE_STARTELF_EXEC ||
            s == STATE_KERNEL_EXEC || s == STATE_PXE_BOOT_EXEC ||
            s == STATE_CORE_DRIVER_INIT || s == STATE_BSP_DRIVER_INIT);
}

// ============================================================================
// VERIFIED SAFETY INVARIANTS
// Proven theorems that MUST hold at runtime
// ============================================================================

// Theorem 1: Success and failure are mutually exclusive
// Proven by: Z3 (unsat), Vampire, Lean 4, Prolog
#define INVARIANT_SUCCESS_FAILURE_EXCLUSIVE(s) \
    (!(fsa_is_success(s) && fsa_is_failure(s)))

// Theorem 2: Terminal states have no outgoing transitions
// Proven by: Z3 (unsat), Vampire, Lean 4, Prolog
#define INVARIANT_TERMINAL_ABSORBING(from, to) \
    (!fsa_is_terminal(from) || (from) == (to))

// Theorem 3: SecureBootFail only from loading states
// Proven by: Z3 (unsat), Vampire, Lean 4, Prolog
#define INVARIANT_SECURE_BOOT_FROM_LOADING(from, failure) \
    ((failure) != FAILURE_SECURE_BOOT_FAIL || fsa_is_loading(from))

// Theorem 4: HardwareFail only from execution states
// Proven by: Z3 (unsat), Vampire, Lean 4, Prolog
#define INVARIANT_HARDWARE_FAIL_FROM_EXECUTION(from, failure) \
    ((failure) != FAILURE_HARDWARE_FAIL || fsa_is_execution(from))

// Theorem 5: Non-terminal states have at least one successor
// Proven by: Z3 (unsat), Vampire, Lean 4
#define INVARIANT_NON_TERMINAL_HAS_SUCCESSOR(s) \
    (fsa_is_terminal(s) || fsa_has_valid_successor(s))

// Failure tracking for verified constraint enforcement
extern failure_type_t fsa_current_failure_type;
void fsa_set_failure_type(failure_type_t type);
failure_type_t fsa_get_failure_type(void);

// Invariant checking functions
int fsa_check_invariants(boot_state_t current, boot_state_t next, failure_type_t failure);
int fsa_has_valid_successor(boot_state_t s);
abstract_state_t fsa_get_abstract_state(boot_state_t s);
const char* fsa_failure_type_name(failure_type_t type);

// Verified path length (from proofs)
#define VERIFIED_HAPPY_PATH_LENGTH 8  // Proven: 8 transitions to boot_success
#define VERIFIED_SHORTEST_FAILURE  2  // Proven: 2 transitions to no_boot_media

recovery_action_t fsa_determine_recovery(boot_state_t failed_state, interlock_type_t interlock);
void fsa_execute_recovery(recovery_action_t action);

// Enhanced verified transition functions
transition_status_t fsa_validate_transition_verified(boot_state_t from_state,
                                                      boot_state_t to_state,
                                                      failure_type_t failure_type);
void fsa_update_state_verified(boot_state_t new_state, failure_type_t failure_type);
void fsa_transition_to_failure(failure_type_t failure_type);

// Transition counting for happy path verification
void fsa_reset_transition_count(void);
uint32_t fsa_get_transition_count(void);
int fsa_verify_happy_path_length(void);

// State history functions
void fsa_record_history(boot_state_t state, transition_status_t status, interlock_type_t interlock);
void fsa_dump_history(void);
state_history_entry_t* fsa_get_history(uint8_t index);

// Monitoring statistics
typedef struct {
    uint32_t total_transitions;
    uint32_t valid_transitions;
    uint32_t invalid_transitions;
    uint32_t blocked_transitions;
    uint32_t timeouts;
    uint32_t interlocks_triggered;
    uint32_t recoveries_attempted;
    uint32_t recoveries_successful;
} fsa_statistics_t;

fsa_statistics_t* fsa_get_statistics(void);

// Internal safety check function
void fsa_perform_safety_checks(void);

// External interface for main.c
extern state_monitor_t fsa_monitor;

#endif