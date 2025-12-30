%------------------------------------------------------------------------------
% ARM Boot FSA - Key Theorems
% TPTP format for Vampire theorem prover
% Comprehensive theorem suite for boot process verification
% Generated: 2025-12-27
%
% Usage: vampire --mode casc arm_boot_theorems.p
%        vampire --proof tptp arm_boot_theorems.p
%        vampire --time_limit 30 arm_boot_theorems.p
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% DOMAIN: Boot States
%------------------------------------------------------------------------------

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

%------------------------------------------------------------------------------
% State Classifications
%------------------------------------------------------------------------------

fof(terminal_definition, axiom,
    ![S]: (terminal_state(S) <=>
        (S = boot_success | S = no_boot_media | S = firmware_corrupt |
         S = secure_boot_fail | S = hardware_fail))).

fof(success_definition, axiom,
    ![S]: (success_state(S) <=> S = boot_success)).

fof(failure_definition, axiom,
    ![S]: (failure_state(S) <=>
        (S = no_boot_media | S = firmware_corrupt |
         S = secure_boot_fail | S = hardware_fail))).

fof(initial_definition, axiom,
    ![S]: (initial_state(S) <=> S = power_on)).

fof(loading_definition, axiom,
    ![S]: (loading_state(S) <=>
        (S = bootcode_loading | S = startelf_loading | S = kernel_loading))).

fof(execution_definition, axiom,
    ![S]: (execution_state(S) <=>
        (S = rom_execution | S = bootcode_execution |
         S = startelf_execution | S = kernel_execution))).

%------------------------------------------------------------------------------
% Transition Relation
%------------------------------------------------------------------------------

% Happy path
fof(t1, axiom, transition(power_on, rom_execution)).
fof(t2, axiom, transition(rom_execution, bootcode_loading)).
fof(t4, axiom, transition(bootcode_loading, bootcode_execution)).
fof(t6, axiom, transition(bootcode_execution, startelf_loading)).
fof(t8, axiom, transition(startelf_loading, startelf_execution)).
fof(t10, axiom, transition(startelf_execution, kernel_loading)).
fof(t12, axiom, transition(kernel_loading, kernel_execution)).
fof(t14, axiom, transition(kernel_execution, boot_success)).

% Failure paths
fof(t3, axiom, transition(rom_execution, no_boot_media)).
fof(t5, axiom, transition(bootcode_loading, firmware_corrupt)).
fof(t7, axiom, transition(bootcode_execution, hardware_fail)).
fof(t9, axiom, transition(startelf_loading, firmware_corrupt)).
fof(t11, axiom, transition(startelf_execution, hardware_fail)).
fof(t13, axiom, transition(kernel_loading, firmware_corrupt)).
fof(t15, axiom, transition(kernel_execution, hardware_fail)).
fof(t16, axiom, transition(bootcode_loading, secure_boot_fail)).
fof(t17, axiom, transition(startelf_loading, secure_boot_fail)).
fof(t18, axiom, transition(kernel_loading, secure_boot_fail)).

%------------------------------------------------------------------------------
% Reachability (Transitive Closure)
%------------------------------------------------------------------------------

fof(reach_base, axiom,
    ![S1, S2]: (transition(S1, S2) => reachable(S1, S2))).

fof(reach_trans, axiom,
    ![S1, S2, S3]: ((reachable(S1, S2) & reachable(S2, S3)) => reachable(S1, S3))).

fof(reach_refl, axiom,
    ![S]: (boot_state(S) => reachable(S, S))).

%------------------------------------------------------------------------------
% FSA Properties
%------------------------------------------------------------------------------

fof(terminal_no_outgoing, axiom,
    ![S1, S2]: (terminal_state(S1) => ~transition(S1, S2))).

fof(success_failure_exclusive, axiom,
    ![S]: ~(success_state(S) & failure_state(S))).

%------------------------------------------------------------------------------
% Path Length (for minimum step analysis)
%------------------------------------------------------------------------------

% Distance/step count (simplified for FOL)
fof(step_zero, axiom, ![S]: steps(S, S, zero)).
fof(step_succ, axiom,
    ![S1, S2, S3, N]: ((transition(S1, S2) & steps(S2, S3, N)) =>
                       steps(S1, S3, succ(N)))).

% Natural number ordering for step comparison
fof(nat_zero, axiom, nat(zero)).
fof(nat_succ, axiom, ![N]: (nat(N) => nat(succ(N)))).
fof(less_zero, axiom, ![N]: (nat(N) => ~less(N, zero))).
fof(less_succ, axiom, ![N, M]: (less(N, M) <=> less(succ(N), succ(M)))).

%------------------------------------------------------------------------------
% THEOREMS
%------------------------------------------------------------------------------

% Theorem 1: Boot success is reachable from initial state
fof(theorem_success_reachable, conjecture,
    reachable(power_on, boot_success)).

%------------------------------------------------------------------------------
% Additional theorems (uncomment one at a time to prove)
%------------------------------------------------------------------------------

% Theorem 2: All terminal states are reachable from initial
% fof(theorem_all_terminals_reachable, conjecture,
%     (reachable(power_on, boot_success) &
%      reachable(power_on, no_boot_media) &
%      reachable(power_on, firmware_corrupt) &
%      reachable(power_on, secure_boot_fail) &
%      reachable(power_on, hardware_fail))).

% Theorem 3: Terminal states have no outgoing transitions
% fof(theorem_terminal_no_exit, conjecture,
%     ![T]: (terminal_state(T) => ~?[S]: transition(T, S))).

% Theorem 4: Success and failure are mutually exclusive
% fof(theorem_exclusive_outcomes, conjecture,
%     ![S]: ~(success_state(S) & failure_state(S))).

% Theorem 5: Happy path exists (8 steps to success)
% fof(theorem_happy_path, conjecture,
%     steps(power_on, boot_success,
%           succ(succ(succ(succ(succ(succ(succ(succ(zero)))))))))).

% Theorem 6: Failure states are terminal
% fof(theorem_failure_terminal, conjecture,
%     ![S]: (failure_state(S) => terminal_state(S))).

% Theorem 7: From loading state, can reach firmware_corrupt
% fof(theorem_firmware_corrupt_from_loading, conjecture,
%     ![S]: (loading_state(S) => reachable(S, firmware_corrupt))).

% Theorem 8: Secure boot failure only from loading states
% fof(theorem_secure_boot_from_loading, conjecture,
%     ![S]: (transition(S, secure_boot_fail) => loading_state(S))).

% Theorem 9: Hardware failure only from execution states
% fof(theorem_hardware_fail_from_exec, conjecture,
%     ![S]: (transition(S, hardware_fail) => execution_state(S))).

% Theorem 10: Non-terminal states have successors
% fof(theorem_non_terminal_progress, conjecture,
%     ![S]: ((boot_state(S) & ~terminal_state(S)) =>
%            ?[S2]: transition(S, S2))).

%------------------------------------------------------------------------------
% End of file
%------------------------------------------------------------------------------
