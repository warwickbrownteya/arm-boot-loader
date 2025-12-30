%------------------------------------------------------------------------------
% ARM Boot FSA - Kripke Semantics / Modal Logic Encoding
% TPTP format for Vampire theorem prover
% Based on Kripke semantics ontology
% Generated: 2025-12-27
%
% Usage: vampire --mode casc arm_boot_kripke.p
%        vampire --proof tptp arm_boot_kripke.p
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% Kripke Frame: Possible Worlds
%------------------------------------------------------------------------------

% Possible worlds (boot states)
fof(world_power_on, axiom, possible_world(w_power_on)).
fof(world_rom_exec, axiom, possible_world(w_rom_execution)).
fof(world_bootcode_loading, axiom, possible_world(w_bootcode_loading)).
fof(world_bootcode_exec, axiom, possible_world(w_bootcode_execution)).
fof(world_startelf_loading, axiom, possible_world(w_startelf_loading)).
fof(world_startelf_exec, axiom, possible_world(w_startelf_execution)).
fof(world_kernel_loading, axiom, possible_world(w_kernel_loading)).
fof(world_kernel_exec, axiom, possible_world(w_kernel_execution)).
fof(world_success, axiom, possible_world(w_boot_success)).
fof(world_failure, axiom, possible_world(w_failure)).

% World enumeration
fof(world_enumeration, axiom,
    ![W]: (possible_world(W) <=>
        (W = w_power_on | W = w_rom_execution | W = w_bootcode_loading |
         W = w_bootcode_execution | W = w_startelf_loading | W = w_startelf_execution |
         W = w_kernel_loading | W = w_kernel_execution | W = w_boot_success |
         W = w_failure))).

%------------------------------------------------------------------------------
% Accessibility Relation (R)
%------------------------------------------------------------------------------

% Happy path accessibility
fof(access_power_rom, axiom, accessible(w_power_on, w_rom_execution)).
fof(access_rom_bootload, axiom, accessible(w_rom_execution, w_bootcode_loading)).
fof(access_bootload_bootexec, axiom, accessible(w_bootcode_loading, w_bootcode_execution)).
fof(access_bootexec_startload, axiom, accessible(w_bootcode_execution, w_startelf_loading)).
fof(access_startload_startexec, axiom, accessible(w_startelf_loading, w_startelf_execution)).
fof(access_startexec_kernload, axiom, accessible(w_startelf_execution, w_kernel_loading)).
fof(access_kernload_kernexec, axiom, accessible(w_kernel_loading, w_kernel_execution)).
fof(access_kernexec_success, axiom, accessible(w_kernel_execution, w_boot_success)).

% Failure accessibility (from any non-terminal world)
fof(access_rom_failure, axiom, accessible(w_rom_execution, w_failure)).
fof(access_bootload_failure, axiom, accessible(w_bootcode_loading, w_failure)).
fof(access_bootexec_failure, axiom, accessible(w_bootcode_execution, w_failure)).
fof(access_startload_failure, axiom, accessible(w_startelf_loading, w_failure)).
fof(access_startexec_failure, axiom, accessible(w_startelf_execution, w_failure)).
fof(access_kernload_failure, axiom, accessible(w_kernel_loading, w_failure)).
fof(access_kernexec_failure, axiom, accessible(w_kernel_execution, w_failure)).

% Reflexivity (worlds are accessible to themselves)
fof(reflexivity, axiom,
    ![W]: (possible_world(W) => accessible(W, W))).

% Terminal worlds have no further accessibility (except to themselves)
fof(success_terminal, axiom,
    ![W]: (accessible(w_boot_success, W) => W = w_boot_success)).

fof(failure_terminal, axiom,
    ![W]: (accessible(w_failure, W) => W = w_failure)).

%------------------------------------------------------------------------------
% Atomic Propositions
%------------------------------------------------------------------------------

% Propositions that hold at specific worlds
fof(prop_sd_accessible, axiom, holds(sd_accessible, w_bootcode_loading)).
fof(prop_bootcode_loaded, axiom, holds(bootcode_loaded, w_bootcode_execution)).
fof(prop_hardware_initializing, axiom, holds(hardware_initializing, w_bootcode_execution)).
fof(prop_startelf_loaded, axiom, holds(startelf_loaded, w_startelf_execution)).
fof(prop_videocore_ready, axiom, holds(videocore_ready, w_startelf_execution)).
fof(prop_kernel_loaded, axiom, holds(kernel_loaded, w_kernel_execution)).
fof(prop_boot_successful, axiom, holds(boot_successful, w_boot_success)).
fof(prop_boot_failed, axiom, holds(boot_failed, w_failure)).

%------------------------------------------------------------------------------
% Modal Operators
%------------------------------------------------------------------------------

% Necessarily (Box): φ holds in all accessible worlds
% box(P, W) means □P holds at world W
fof(box_definition, axiom,
    ![P, W]: (box(P, W) <=>
        (possible_world(W) & ![V]: (accessible(W, V) => holds(P, V))))).

% Possibly (Diamond): φ holds in some accessible world
% diamond(P, W) means ◇P holds at world W
fof(diamond_definition, axiom,
    ![P, W]: (diamond(P, W) <=>
        (possible_world(W) & ?[V]: (accessible(W, V) & holds(P, V))))).

% Duality: ◇P ≡ ¬□¬P
fof(modal_duality, axiom,
    ![P, W]: (diamond(P, W) <=> ~box(neg(P), W))).

% Negation of propositions
fof(negation_def, axiom,
    ![P, W]: (holds(neg(P), W) <=> ~holds(P, W))).

%------------------------------------------------------------------------------
% Modal Logic Axioms (System S4)
%------------------------------------------------------------------------------

% Axiom K: □(P → Q) → (□P → □Q)
fof(axiom_k, axiom,
    ![P, Q, W]: ((box(implies(P, Q), W) & box(P, W)) => box(Q, W))).

% Axiom T: □P → P (reflexivity of accessibility)
fof(axiom_t, axiom,
    ![P, W]: (box(P, W) => holds(P, W))).

% Axiom 4: □P → □□P (transitivity of accessibility)
% Note: This holds if accessibility is transitive
fof(axiom_4, axiom,
    ![P, W]: (box(P, W) => box(box_prop(P), W))).

% Axiom D: □P → ◇P (serial accessibility)
fof(axiom_d, axiom,
    ![P, W]: (box(P, W) => diamond(P, W))).

%------------------------------------------------------------------------------
% Transitive Closure of Accessibility (for temporal reasoning)
%------------------------------------------------------------------------------

% Base case
fof(eventually_base, axiom,
    ![W1, W2]: (accessible(W1, W2) => eventually_accessible(W1, W2))).

% Transitive case
fof(eventually_trans, axiom,
    ![W1, W2, W3]: ((eventually_accessible(W1, W2) & eventually_accessible(W2, W3)) =>
                    eventually_accessible(W1, W3))).

%------------------------------------------------------------------------------
% Boot Process Modal Properties
%------------------------------------------------------------------------------

% Irrevocability of success: once boot succeeds, it stays successful
fof(success_irrevocable, axiom,
    box(boot_successful, w_boot_success)).

% From failure, only failure is accessible
fof(failure_irrevocable, axiom,
    box(boot_failed, w_failure)).

% From initial state, success is possible (through the happy path)
fof(success_possible_initially, axiom,
    diamond(boot_successful, w_power_on)).

% From initial state, failure is also possible
fof(failure_possible_initially, axiom,
    diamond(boot_failed, w_power_on)).

%------------------------------------------------------------------------------
% THEOREMS TO PROVE
%------------------------------------------------------------------------------

% Theorem 1: Success is eventually reachable from power on
fof(theorem_success_eventually, conjecture,
    eventually_accessible(w_power_on, w_boot_success)).

% Uncomment to prove other theorems:

% Theorem 2: From success world, boot_successful necessarily holds
% fof(theorem_success_necessary, conjecture,
%     box(boot_successful, w_boot_success)).

% Theorem 3: Failure is possible from any non-terminal world
% fof(theorem_failure_possible, conjecture,
%     ![W]: ((possible_world(W) & W \= w_boot_success & W \= w_failure) =>
%            diamond(boot_failed, W))).

% Theorem 4: Success and failure are mutually exclusive at any world
% fof(theorem_success_failure_exclusive, conjecture,
%     ![W]: ~(holds(boot_successful, W) & holds(boot_failed, W))).

% Theorem 5: Reflexivity implies Axiom T holds
% fof(theorem_axiom_t_holds, conjecture,
%     ![P, W]: ((possible_world(W) & box(P, W)) => holds(P, W))).

%------------------------------------------------------------------------------
% End of file
%------------------------------------------------------------------------------
