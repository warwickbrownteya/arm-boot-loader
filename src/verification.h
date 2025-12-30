/* Formal Verification Header for Bootloader */

#ifndef VERIFICATION_H
#define VERIFICATION_H

#include <stdint.h>

// Verification functions
int verification_init(void);
int verification_add_kripke_world(uint32_t world_id, const uint8_t *properties, uint32_t prop_size);
int verification_add_accessibility(uint32_t from_world, uint32_t to_world);
int verification_check_necessity(uint32_t world_id, uint8_t property_bit);
int verification_add_scott_element(uint8_t is_bottom, uint8_t level, const uint8_t *properties, uint32_t prop_size);
int verification_scott_less_equal(uint32_t elem1_idx, uint32_t elem2_idx);
int verification_add_grothendieck_site(uint32_t site_id, const uint8_t *local_data, uint32_t data_size);
int verification_check_sheaf_condition(uint32_t site_idx);
int verification_run_comprehensive_check(void);

// ============================================================================
// FORMALLY PROVEN THEOREM VERIFICATION
// Theorems verified by Z3, CVC5, Yices, Vampire, E Prover, Prover9, Lean 4, Prolog
// ============================================================================

// Theorem identifiers
#define THEOREM_BOOT_SUCCESS_REACHABLE      1
#define THEOREM_ALL_FAILURES_REACHABLE      2
#define THEOREM_SUCCESS_FAILURE_EXCLUSIVE   3
#define THEOREM_TERMINAL_ABSORBING          4
#define THEOREM_NON_TERMINAL_HAS_SUCCESSOR  5
#define THEOREM_SECURE_BOOT_FROM_LOADING    6
#define THEOREM_HARDWARE_FAIL_FROM_EXECUTION 7
#define THEOREM_HAPPY_PATH_LENGTH           8  // Value: 8 transitions
#define THEOREM_SHORTEST_FAILURE_LENGTH     9  // Value: 2 transitions
#define THEOREM_UNIQUE_INITIAL              10

// Verify a specific proven theorem at runtime
int verification_check_proven_theorem(int theorem_id, uint32_t *test_data, uint32_t data_size);

// Verify all formally proven theorems
int verification_check_all_proven_theorems(void);

#endif