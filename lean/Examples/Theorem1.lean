import Approximation
import Mathlib.Tactic.NormNum

/-! A one-state witness for the comparator slack sign in Appendix B.2. -/

namespace Kadp.Examples.Theorem1

open SargentStachurski.MarkovDecisionProcesses Kadp.Approximation

noncomputable def model : MDP Unit Unit := Kadp.Occupancy.ofCosts (1/2) (by norm_num) (by norm_num)
  (fun _ _ => 0) (fun _ _ _ => 1) (by simp) (by simp)

theorem comparator_slack_sign :
    let J : Unit → ℝ := fun _ => 1
    let X : Fin 1 → Unit := fun _ => ()
    (max (optimalBellman model J () - J ()) 0 = 0) ∧
    (¬ SlackFeasible model X J (fun _ => 0)) ∧
    (bellmanResidual model J () = 1/2) ∧
    SlackFeasible model X J (fun _ => 1/2) := by
  norm_num [optimalBellman, MDP.T, MDP.B, model, Kadp.Occupancy.ofCosts, SlackFeasible, bellmanResidual]

end Kadp.Examples.Theorem1
