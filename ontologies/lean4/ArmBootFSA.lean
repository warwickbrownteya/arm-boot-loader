/-
  ARM Boot FSA - Lean 4 Formalization
  Formal verification of the ARM bootloader finite state automaton

  Generated: 2025-12-27
  Usage: lean ArmBootFSA.lean
-/

-- ============================================================================
-- BOOT STATES
-- ============================================================================

/-- Boot states in the ARM bootloader FSA (13 states) -/
inductive BootState where
  | PowerOn           -- Initial state after power on
  | ROMExecution      -- ROM code executing, searching for boot media
  | BootcodeLoading   -- Loading bootcode.bin from boot media
  | BootcodeExecution -- Executing bootcode.bin, initializing SDRAM
  | StartElfLoading   -- Loading start.elf from boot media
  | StartElfExecution -- Executing start.elf, hardware initialization
  | KernelLoading     -- Loading kernel image
  | KernelExecution   -- Executing kernel, OS boot
  | BootSuccess       -- Successful boot, OS running (TERMINAL)
  | NoBootMedia       -- Failure: No bootable media found (TERMINAL)
  | FirmwareCorrupt   -- Failure: Corrupt or missing firmware (TERMINAL)
  | SecureBootFail    -- Failure: Secure boot verification failed (TERMINAL)
  | HardwareFail      -- Failure: Hardware initialization failed (TERMINAL)
  deriving DecidableEq, Repr

namespace BootState

-- ============================================================================
-- STATE CLASSIFICATION
-- ============================================================================

/-- Terminal states have no outgoing transitions -/
def isTerminal : BootState → Bool
  | BootSuccess => true
  | NoBootMedia => true
  | FirmwareCorrupt => true
  | SecureBootFail => true
  | HardwareFail => true
  | _ => false

/-- Success state -/
def isSuccess : BootState → Bool
  | BootSuccess => true
  | _ => false

/-- Failure states -/
def isFailure : BootState → Bool
  | NoBootMedia => true
  | FirmwareCorrupt => true
  | SecureBootFail => true
  | HardwareFail => true
  | _ => false

/-- Initial state -/
def isInitial : BootState → Bool
  | PowerOn => true
  | _ => false

/-- Loading states (where firmware is being loaded) -/
def isLoading : BootState → Bool
  | BootcodeLoading => true
  | StartElfLoading => true
  | KernelLoading => true
  | _ => false

/-- Execution states (where code is running) -/
def isExecution : BootState → Bool
  | ROMExecution => true
  | BootcodeExecution => true
  | StartElfExecution => true
  | KernelExecution => true
  | _ => false

end BootState

-- ============================================================================
-- TRANSITION RELATION
-- ============================================================================

/-- Direct transition relation between boot states -/
inductive Transition : BootState → BootState → Prop where
  -- Happy path transitions
  | t1  : Transition .PowerOn .ROMExecution
  | t2  : Transition .ROMExecution .BootcodeLoading
  | t4  : Transition .BootcodeLoading .BootcodeExecution
  | t6  : Transition .BootcodeExecution .StartElfLoading
  | t8  : Transition .StartElfLoading .StartElfExecution
  | t10 : Transition .StartElfExecution .KernelLoading
  | t12 : Transition .KernelLoading .KernelExecution
  | t14 : Transition .KernelExecution .BootSuccess
  -- Failure transitions
  | t3  : Transition .ROMExecution .NoBootMedia
  | t5  : Transition .BootcodeLoading .FirmwareCorrupt
  | t7  : Transition .BootcodeExecution .HardwareFail
  | t9  : Transition .StartElfLoading .FirmwareCorrupt
  | t11 : Transition .StartElfExecution .HardwareFail
  | t13 : Transition .KernelLoading .FirmwareCorrupt
  | t15 : Transition .KernelExecution .HardwareFail
  -- Secure boot failure transitions (Pi4/Pi5)
  | t16 : Transition .BootcodeLoading .SecureBootFail
  | t17 : Transition .StartElfLoading .SecureBootFail
  | t18 : Transition .KernelLoading .SecureBootFail

-- ============================================================================
-- REACHABILITY (Reflexive Transitive Closure)
-- ============================================================================

/-- Reachability relation: s2 is reachable from s1 -/
inductive Reachable : BootState → BootState → Prop where
  | refl : ∀ s, Reachable s s
  | step : ∀ s1 s2 s3, Transition s1 s2 → Reachable s2 s3 → Reachable s1 s3

-- ============================================================================
-- BASIC THEOREMS
-- ============================================================================

/-- Transition implies reachability -/
theorem transition_implies_reachable {s1 s2 : BootState} (h : Transition s1 s2) :
    Reachable s1 s2 :=
  Reachable.step s1 s2 s2 h (Reachable.refl s2)

/-- Reachability is transitive -/
theorem reachable_trans {s1 s2 s3 : BootState}
    (h1 : Reachable s1 s2) (h2 : Reachable s2 s3) : Reachable s1 s3 := by
  induction h1 with
  | refl => exact h2
  | step a b c hab hbc ih => exact Reachable.step a b s3 hab (ih h2)

-- ============================================================================
-- HAPPY PATH THEOREMS
-- ============================================================================

/-- ROM execution is reachable from power on -/
theorem rom_reachable : Reachable .PowerOn .ROMExecution :=
  transition_implies_reachable Transition.t1

/-- Bootcode loading is reachable from power on -/
theorem bootcode_loading_reachable : Reachable .PowerOn .BootcodeLoading :=
  reachable_trans rom_reachable (transition_implies_reachable Transition.t2)

/-- Bootcode execution is reachable from power on -/
theorem bootcode_exec_reachable : Reachable .PowerOn .BootcodeExecution :=
  reachable_trans bootcode_loading_reachable (transition_implies_reachable Transition.t4)

/-- Start.elf loading is reachable from power on -/
theorem startelf_loading_reachable : Reachable .PowerOn .StartElfLoading :=
  reachable_trans bootcode_exec_reachable (transition_implies_reachable Transition.t6)

/-- Start.elf execution is reachable from power on -/
theorem startelf_exec_reachable : Reachable .PowerOn .StartElfExecution :=
  reachable_trans startelf_loading_reachable (transition_implies_reachable Transition.t8)

/-- Kernel loading is reachable from power on -/
theorem kernel_loading_reachable : Reachable .PowerOn .KernelLoading :=
  reachable_trans startelf_exec_reachable (transition_implies_reachable Transition.t10)

/-- Kernel execution is reachable from power on -/
theorem kernel_exec_reachable : Reachable .PowerOn .KernelExecution :=
  reachable_trans kernel_loading_reachable (transition_implies_reachable Transition.t12)

/-- MAIN THEOREM: Boot success is reachable from power on -/
theorem boot_success_reachable : Reachable .PowerOn .BootSuccess :=
  reachable_trans kernel_exec_reachable (transition_implies_reachable Transition.t14)

-- ============================================================================
-- FAILURE PATH THEOREMS
-- ============================================================================

/-- No boot media is reachable from power on -/
theorem no_boot_media_reachable : Reachable .PowerOn .NoBootMedia :=
  reachable_trans rom_reachable (transition_implies_reachable Transition.t3)

/-- Firmware corrupt is reachable from power on (via bootcode loading) -/
theorem firmware_corrupt_reachable : Reachable .PowerOn .FirmwareCorrupt :=
  reachable_trans bootcode_loading_reachable (transition_implies_reachable Transition.t5)

/-- Hardware fail is reachable from power on -/
theorem hardware_fail_reachable : Reachable .PowerOn .HardwareFail :=
  reachable_trans bootcode_exec_reachable (transition_implies_reachable Transition.t7)

/-- Secure boot fail is reachable from power on -/
theorem secure_boot_fail_reachable : Reachable .PowerOn .SecureBootFail :=
  reachable_trans bootcode_loading_reachable (transition_implies_reachable Transition.t16)

/-- All terminal states are reachable from power on -/
theorem all_terminals_reachable :
    Reachable .PowerOn .BootSuccess ∧
    Reachable .PowerOn .NoBootMedia ∧
    Reachable .PowerOn .FirmwareCorrupt ∧
    Reachable .PowerOn .SecureBootFail ∧
    Reachable .PowerOn .HardwareFail :=
  ⟨boot_success_reachable, no_boot_media_reachable, firmware_corrupt_reachable,
   secure_boot_fail_reachable, hardware_fail_reachable⟩

-- ============================================================================
-- SAFETY THEOREMS
-- ============================================================================

/-- Success and failure are mutually exclusive -/
theorem success_failure_exclusive (s : BootState) :
    ¬(s.isSuccess = true ∧ s.isFailure = true) := by
  intro ⟨hs, hf⟩
  cases s <;> simp [BootState.isSuccess, BootState.isFailure] at hs hf

/-- Terminal states are either success or failure -/
theorem terminal_is_success_or_failure (s : BootState) (h : s.isTerminal = true) :
    s.isSuccess = true ∨ s.isFailure = true := by
  cases s <;> simp [BootState.isTerminal, BootState.isSuccess, BootState.isFailure] at h ⊢

/-- There is exactly one initial state -/
theorem unique_initial : ∀ s : BootState, s.isInitial = true ↔ s = BootState.PowerOn := by
  intro s
  cases s <;> simp [BootState.isInitial]

-- ============================================================================
-- TRANSITION PROPERTIES
-- ============================================================================

/-- No transitions from BootSuccess (it's terminal) -/
theorem no_transition_from_success : ∀ s, ¬Transition .BootSuccess s := by
  intro s h
  cases h

/-- No transitions from NoBootMedia (it's terminal) -/
theorem no_transition_from_no_boot_media : ∀ s, ¬Transition .NoBootMedia s := by
  intro s h
  cases h

/-- No transitions from FirmwareCorrupt (it's terminal) -/
theorem no_transition_from_firmware_corrupt : ∀ s, ¬Transition .FirmwareCorrupt s := by
  intro s h
  cases h

/-- No transitions from SecureBootFail (it's terminal) -/
theorem no_transition_from_secure_boot_fail : ∀ s, ¬Transition .SecureBootFail s := by
  intro s h
  cases h

/-- No transitions from HardwareFail (it's terminal) -/
theorem no_transition_from_hardware_fail : ∀ s, ¬Transition .HardwareFail s := by
  intro s h
  cases h

/-- Terminal states have no outgoing transitions -/
theorem terminal_no_outgoing (s : BootState) (h : s.isTerminal = true) :
    ∀ s', ¬Transition s s' := by
  intro s' ht
  cases s <;> simp [BootState.isTerminal] at h <;> cases ht

-- ============================================================================
-- PATH LENGTH (for minimum steps analysis)
-- ============================================================================

/-- Minimum steps to reach a state from another -/
inductive StepsTo : BootState → BootState → Nat → Prop where
  | zero : ∀ s, StepsTo s s 0
  | succ : ∀ s1 s2 s3 n, Transition s1 s2 → StepsTo s2 s3 n → StepsTo s1 s3 (n + 1)

/-- Boot success is reachable in exactly 8 steps -/
theorem success_in_8_steps : StepsTo .PowerOn .BootSuccess 8 :=
  StepsTo.succ _ _ _ _ Transition.t1 $  -- PowerOn → ROMExecution
  StepsTo.succ _ _ _ _ Transition.t2 $  -- ROMExecution → BootcodeLoading
  StepsTo.succ _ _ _ _ Transition.t4 $  -- BootcodeLoading → BootcodeExecution
  StepsTo.succ _ _ _ _ Transition.t6 $  -- BootcodeExecution → StartElfLoading
  StepsTo.succ _ _ _ _ Transition.t8 $  -- StartElfLoading → StartElfExecution
  StepsTo.succ _ _ _ _ Transition.t10 $ -- StartElfExecution → KernelLoading
  StepsTo.succ _ _ _ _ Transition.t12 $ -- KernelLoading → KernelExecution
  StepsTo.succ _ _ _ _ Transition.t14 $ -- KernelExecution → BootSuccess
  StepsTo.zero _

/-- NoBootMedia is reachable in exactly 2 steps -/
theorem no_boot_media_in_2_steps : StepsTo .PowerOn .NoBootMedia 2 :=
  StepsTo.succ _ _ _ _ Transition.t1 $
  StepsTo.succ _ _ _ _ Transition.t3 $
  StepsTo.zero _

/-- FirmwareCorrupt is reachable in exactly 3 steps (shortest path) -/
theorem firmware_corrupt_in_3_steps : StepsTo .PowerOn .FirmwareCorrupt 3 :=
  StepsTo.succ _ _ _ _ Transition.t1 $
  StepsTo.succ _ _ _ _ Transition.t2 $
  StepsTo.succ _ _ _ _ Transition.t5 $
  StepsTo.zero _

/-- HardwareFail is reachable in exactly 4 steps (shortest path) -/
theorem hardware_fail_in_4_steps : StepsTo .PowerOn .HardwareFail 4 :=
  StepsTo.succ _ _ _ _ Transition.t1 $
  StepsTo.succ _ _ _ _ Transition.t2 $
  StepsTo.succ _ _ _ _ Transition.t4 $
  StepsTo.succ _ _ _ _ Transition.t7 $
  StepsTo.zero _

-- ============================================================================
-- SECURE BOOT PROPERTIES
-- ============================================================================

/-- Secure boot failure only occurs from loading states -/
theorem secure_boot_fail_from_loading :
    ∀ s, Transition s .SecureBootFail → s.isLoading = true := by
  intro s h
  cases h <;> rfl

/-- Hardware failure only occurs from execution states -/
theorem hardware_fail_from_execution :
    ∀ s, Transition s .HardwareFail → s.isExecution = true := by
  intro s h
  cases h <;> rfl

-- ============================================================================
-- DETERMINISM (given conditions, unique next state)
-- ============================================================================

/-- From PowerOn, only ROMExecution is reachable in one step -/
theorem power_on_deterministic :
    ∀ s, Transition .PowerOn s → s = .ROMExecution := by
  intro s h
  cases h
  rfl

-- ============================================================================
-- SUMMARY
-- ============================================================================

#check boot_success_reachable       -- Main theorem: success is reachable
#check all_terminals_reachable      -- All terminal states reachable
#check success_in_8_steps           -- Happy path is 8 steps
#check terminal_no_outgoing         -- Terminal states are absorbing
#check success_failure_exclusive    -- Success and failure are exclusive
