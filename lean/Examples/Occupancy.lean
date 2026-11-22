import Occupancy
import Mathlib.Tactic.NormNum

/-! The two-state, two-action example from the discounted occupancy note.
`false` denotes state s and action A; `true` denotes state t and action B. -/

namespace Kadp.Examples.Occupancy

open Matrix SargentStachurski.MarkovDecisionProcesses Kadp.Occupancy

noncomputable def model : MDP Bool Bool := ofCosts (1 / 2) (by norm_num) (by norm_num)
  (fun _ a => if a then 2 else 1)
  (fun _ a y => if a then (if y then 1 else 0) else 1 / 2)
  (by intro x a y; cases a <;> cases y <;> norm_num)
  (by intro x a; cases a <;> norm_num [Fintype.sum_bool])

def initial (x : Bool) : ℝ := if x then 0 else 1
def candidate (x : Bool) : ℝ := if x then 2 else 3

theorem initial_distribution : IsDistribution initial := by
  constructor
  · intro x; cases x <;> norm_num [initial]
  · norm_num [initial, Fintype.sum_bool]

/-- Starting at s, the discounted mass is 2/3 at s and 1/3 at t. -/
theorem occupancy : discountedOccupancy model id initial = fun x => if x then 1 / 3 else 2 / 3 := by
  symm
  apply occupancy_unique
  funext x
  cases x <;> norm_num [initial, model, ofCosts, MDP.Pσ, vecMul, dotProduct, Fintype.sum_bool]

theorem policy_cost : policyCost model id = fun x => if x then 4 else 8 / 3 := by
  symm
  apply policyCost_unique
  funext x
  cases x <;> norm_num [costBellman, model, ofCosts, MDP.rσ, MDP.Pσ, mulVec, dotProduct,
    Fintype.sum_bool]

theorem residual : candidate - costBellman model id candidate = fun x => if x then -1 else 3 / 4 := by
  funext x
  cases x <;> norm_num [candidate, costBellman, model, ofCosts, MDP.rσ, MDP.Pσ, mulVec,
    dotProduct, Fintype.sum_bool]

/-- The two residuals have opposite signs. Their discounted mean gives exactly the
initial cost error after dividing by 1 - α. -/
theorem errors :
    initial ⬝ᵥ (candidate - policyCost model id) = 1 / 3 ∧
    discountedOccupancy model id initial ⬝ᵥ (candidate - costBellman model id candidate) = 1 / 6 := by
  rw [occupancy, policy_cost, residual]
  norm_num [initial, candidate, dotProduct, Fintype.sum_bool]

end Kadp.Examples.Occupancy
