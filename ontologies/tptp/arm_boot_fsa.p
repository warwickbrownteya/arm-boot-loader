%------------------------------------------------------------------------------
% ARM Boot FSA - Finite State Automaton Encoding
% TPTP format for Vampire theorem prover
% Generated: 2025-12-27
%
% Usage: vampire --mode casc arm_boot_fsa.p
%        vampire --proof tptp arm_boot_fsa.p
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% Domain: Boot States
%------------------------------------------------------------------------------

% Boot state constants
fof(state_power_on, axiom, boot_state(power_on)).
fof(state_rom_exec, axiom, boot_state(rom_execution)).
fof(state_bootcode_loading, axiom, boot_state(bootcode_loading)).
fof(state_bootcode_exec, axiom, boot_state(bootcode_execution)).
fof(state_startelf_loading, axiom, boot_state(startelf_loading)).
fof(state_startelf_exec, axiom, boot_state(startelf_execution)).
fof(state_kernel_loading, axiom, boot_state(kernel_loading)).
fof(state_kernel_exec, axiom, boot_state(kernel_execution)).
fof(state_boot_success, axiom, boot_state(boot_success)).
fof(state_no_boot_media, axiom, boot_state(no_boot_media)).
fof(state_firmware_corrupt, axiom, boot_state(firmware_corrupt)).
fof(state_secure_boot_fail, axiom, boot_state(secure_boot_fail)).
fof(state_hardware_fail, axiom, boot_state(hardware_fail)).

% State count (13 states)
fof(state_enumeration, axiom,
    ![S]: (boot_state(S) <=>
        (S = power_on | S = rom_execution | S = bootcode_loading |
         S = bootcode_execution | S = startelf_loading | S = startelf_execution |
         S = kernel_loading | S = kernel_execution | S = boot_success |
         S = no_boot_media | S = firmware_corrupt | S = secure_boot_fail |
         S = hardware_fail))).

%------------------------------------------------------------------------------
% Domain: State Classification
%------------------------------------------------------------------------------

% Terminal states (no outgoing transitions)
fof(terminal_success, axiom, terminal_state(boot_success)).
fof(terminal_no_media, axiom, terminal_state(no_boot_media)).
fof(terminal_firmware, axiom, terminal_state(firmware_corrupt)).
fof(terminal_secure, axiom, terminal_state(secure_boot_fail)).
fof(terminal_hardware, axiom, terminal_state(hardware_fail)).

fof(terminal_definition, axiom,
    ![S]: (terminal_state(S) <=>
        (S = boot_success | S = no_boot_media | S = firmware_corrupt |
         S = secure_boot_fail | S = hardware_fail))).

% Success state
fof(success_definition, axiom,
    ![S]: (success_state(S) <=> S = boot_success)).

% Failure states
fof(failure_definition, axiom,
    ![S]: (failure_state(S) <=>
        (S = no_boot_media | S = firmware_corrupt |
         S = secure_boot_fail | S = hardware_fail))).

% Initial state
fof(initial_definition, axiom,
    ![S]: (initial_state(S) <=> S = power_on)).

% Loading states
fof(loading_definition, axiom,
    ![S]: (loading_state(S) <=>
        (S = bootcode_loading | S = startelf_loading | S = kernel_loading))).

% Execution states
fof(execution_definition, axiom,
    ![S]: (execution_state(S) <=>
        (S = rom_execution | S = bootcode_execution |
         S = startelf_execution | S = kernel_execution))).

%------------------------------------------------------------------------------
% Transition Relation
%------------------------------------------------------------------------------

% Happy path transitions
fof(t1, axiom, transition(power_on, rom_execution)).
fof(t2, axiom, transition(rom_execution, bootcode_loading)).
fof(t4, axiom, transition(bootcode_loading, bootcode_execution)).
fof(t6, axiom, transition(bootcode_execution, startelf_loading)).
fof(t8, axiom, transition(startelf_loading, startelf_execution)).
fof(t10, axiom, transition(startelf_execution, kernel_loading)).
fof(t12, axiom, transition(kernel_loading, kernel_execution)).
fof(t14, axiom, transition(kernel_execution, boot_success)).

% Failure transitions
fof(t3, axiom, transition(rom_execution, no_boot_media)).
fof(t5, axiom, transition(bootcode_loading, firmware_corrupt)).
fof(t7, axiom, transition(bootcode_execution, hardware_fail)).
fof(t9, axiom, transition(startelf_loading, firmware_corrupt)).
fof(t11, axiom, transition(startelf_execution, hardware_fail)).
fof(t13, axiom, transition(kernel_loading, firmware_corrupt)).
fof(t15, axiom, transition(kernel_execution, hardware_fail)).

% Secure boot failure transitions (for Pi4/Pi5)
fof(t16, axiom, transition(bootcode_loading, secure_boot_fail)).
fof(t17, axiom, transition(startelf_loading, secure_boot_fail)).
fof(t18, axiom, transition(kernel_loading, secure_boot_fail)).

%------------------------------------------------------------------------------
% Transitive Closure: Reachability
%------------------------------------------------------------------------------

% Base case: direct transition implies reachability
fof(reach_base, axiom,
    ![S1, S2]: (transition(S1, S2) => reachable(S1, S2))).

% Inductive case: transitivity
fof(reach_trans, axiom,
    ![S1, S2, S3]: ((reachable(S1, S2) & reachable(S2, S3)) => reachable(S1, S3))).

% Reflexivity for reachability
fof(reach_refl, axiom,
    ![S]: (boot_state(S) => reachable(S, S))).

%------------------------------------------------------------------------------
% Boot Path Definition
%------------------------------------------------------------------------------

% A boot path is a sequence of reachable states from initial to terminal
fof(valid_boot_path, axiom,
    ![S1, S2]: (boot_path(S1, S2) <=>
        (initial_state(S1) & terminal_state(S2) & reachable(S1, S2)))).

% Successful boot path
fof(successful_boot_path, axiom,
    ![S1, S2]: (successful_boot(S1, S2) <=>
        (boot_path(S1, S2) & success_state(S2)))).

% Failed boot path
fof(failed_boot_path, axiom,
    ![S1, S2]: (failed_boot(S1, S2) <=>
        (boot_path(S1, S2) & failure_state(S2)))).

%------------------------------------------------------------------------------
% FSA Properties as Axioms
%------------------------------------------------------------------------------

% Property: Terminal states have no outgoing transitions
fof(terminal_no_outgoing, axiom,
    ![S1, S2]: (terminal_state(S1) => ~transition(S1, S2))).

% Property: Success and failure are mutually exclusive
fof(success_failure_exclusive, axiom,
    ![S]: ~(success_state(S) & failure_state(S))).

% Property: Non-terminal states have at least one outgoing transition
fof(non_terminal_has_successor, axiom,
    ![S]: ((boot_state(S) & ~terminal_state(S)) =>
        ?[S2]: transition(S, S2))).

%------------------------------------------------------------------------------
% THEOREMS TO PROVE
%------------------------------------------------------------------------------

% Theorem 1: Boot success is reachable from power on
fof(theorem_success_reachable, conjecture,
    reachable(power_on, boot_success)).

% Uncomment to prove other theorems:

% Theorem 2: All failure states are reachable
% fof(theorem_failures_reachable, conjecture,
%     (reachable(power_on, no_boot_media) &
%      reachable(power_on, firmware_corrupt) &
%      reachable(power_on, secure_boot_fail) &
%      reachable(power_on, hardware_fail))).

% Theorem 3: From initial state, a terminal state is always reachable
% fof(theorem_termination, conjecture,
%     ![S]: (initial_state(S) => ?[T]: (terminal_state(T) & reachable(S, T)))).

% Theorem 4: Success state has no outgoing transitions
% fof(theorem_success_terminal, conjecture,
%     ~?[S]: transition(boot_success, S)).

%------------------------------------------------------------------------------
% End of file
%------------------------------------------------------------------------------
