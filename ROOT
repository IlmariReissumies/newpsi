chapter "New-Psi"

(*
 * A new formalisation of psi-calculi that no longer requires channels
 * to be symmetric and transitive.
 *)

session NewPsi = "HOL-Nominal" +
  theories
    "Chain"
    "Subst_Term"
    "Agent"
    "Frame"
    "Semantics"
    "Simulation"
    "Bisimulation"
    "Sim_Pres"
    "Bisim_Pres"
    "Sim_Struct_Cong"
    "Structural_Congruence"
    "Bisim_Struct_Cong"
    "Close_Subst"
    "Bisim_Subst"

(*
 * Prove that the new semantics is a conservative extension.
 *)

session OldPsi = NewPsi +
  theories
    "Old_Semantics"
    "Old_Simulation"
    "Old_Bisimulation"