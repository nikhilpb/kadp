import Idealized
import Weighted

/-! A weighted comparison with an unattained infimum. Both states are absorbing,
and only the second state incurs cost. -/

namespace Kadp.Examples.Theorem2

open Matrix SargentStachurski.MarkovDecisionProcesses
open Kadp.Occupancy Kadp.Approximation Kadp.Idealized

noncomputable def model : MDP Bool Unit := ofCosts (1 / 2) (by norm_num) (by norm_num)
  (fun x _ => if x then 5 else 0) (fun x _ y => if y = x then 1 else 0)
  (by intros; positivity) (by intro x _; simp)

def policy (_ : Bool) : Unit := ()
noncomputable def initial (x : Bool) : ℝ := if x then 1 / 10 else 9 / 10

theorem initial_distribution : IsDistribution initial := by
  constructor
  · intro x; cases x <;> norm_num [initial]
  · norm_num [initial, Fintype.sum_bool]

theorem optimal_policy : model.IsOptimal policy := by
  obtain ⟨μ, hμ⟩ := model.exists_isOptimal
  rwa [Subsingleton.elim μ policy] at hμ

theorem occupancy : discountedOccupancy model policy initial = initial := by
  symm
  apply occupancy_unique
  funext x
  cases x <;> norm_num [initial, model, ofCosts, MDP.Pσ, vecMul, dotProduct, Fintype.sum_bool]

theorem optimal_cost : optimalCost model = fun x => if x then 10 else 0 := by
  change -model.vstar = _
  rw [← optimal_policy.2]
  symm
  apply policyCost_unique
  funext x
  cases x <;> norm_num [costBellman, model, ofCosts, MDP.rσ, MDP.Pσ, mulVec, dotProduct,
    Fintype.sum_bool]

/-- Zero feature and offset radii leave just the zero fit. Its weighted L¹ error is one. -/
theorem fit_and_error (p : Parameters ℝ 0 0) :
    fit (fun _ : Bool => (0 : ℝ)) p = 0 ∧
    weightedL1 initial (optimalCost model - fit (fun _ : Bool => (0 : ℝ)) p) = 1 := by
  have hb := abs_nonpos_iff.mp p.property.2
  have hfit : fit (fun _ : Bool => (0 : ℝ)) p = 0 := by ext; simp [fit, hb]
  rw [hfit, optimal_cost, sub_zero]
  norm_num [weightedL1, initial, Fintype.sum_bool]


open Kadp.Weighted

theorem drift_eq_one (ψ : Weight Bool) : drift model ψ = 1 := by
  have hr (xa : Bool × Unit) :
      (∑ y, ψ.val y * model.P xa.1 xa.2 y) / ψ.val xa.1 = 1 := by
    have hpos := lt_of_lt_of_le zero_lt_one (ψ.property xa.1)
    simp [model, ofCosts, hpos.ne', mul_ite]
  unfold drift
  simp_rw [hr]
  simp

theorem weighted_error (ψ : Weight Bool) :
    weightedSup ψ (optimalCost model - 0) = 10 / ψ.val true := by
  rw [sub_zero, optimal_cost, weightedSup]
  have hpos := lt_of_lt_of_le zero_lt_one (ψ.property true)
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 10 / ψ.val true)).mpr
    intro x
    cases x <;> simp [Real.norm_eq_abs, abs_of_pos hpos, (by positivity : 0 ≤ 10 / ψ.val true)]
  · have h := norm_le_pi_norm (fun x : Bool => (if x then (10 : ℝ) else 0) / ψ.val x) true
    simpa [Real.norm_eq_abs, abs_of_pos hpos] using h

/-- Every admissible weight has a strictly positive excess over seven. -/
theorem comparator_value (ψ : Weight Bool) :
    comparatorBound model policy initial 0 ψ = 7 + 63 * ψ.val false / ψ.val true := by
  rw [comparatorBound, weighted_error, occupancy, drift_eq_one]
  have hpos := lt_of_lt_of_le zero_lt_one (ψ.property true)
  change _ * (initial ⬝ᵥ ψ.val + 2 * (initial ⬝ᵥ ψ.val) * (1 + 1 / 2 * 1) / (1 - 1 / 2)) = _
  norm_num [dotProduct, Fintype.sum_bool, initial]
  field_simp
  ring

def weight (t : ℝ) (ht : 1 ≤ t) : Weight Bool :=
  ⟨fun x => if x then t else 1, by intro x; cases x <;> simp [ht]⟩

theorem comparator_values :
    comparatorBound model policy initial 0 (weight 1 le_rfl) = 70 ∧
    comparatorBound model policy initial 0 (weight 10 (by norm_num)) = 133 / 10 := by
  norm_num [comparator_value, weight]

theorem infimum_not_attained :
    (⨅ ψ : Weight Bool, comparatorBound model policy initial 0 ψ) = 7 ∧
    ∀ ψ : Weight Bool, 7 < comparatorBound model policy initial 0 ψ := by
  have hstrict (ψ : Weight Bool) : 7 < comparatorBound model policy initial 0 ψ := by
    rw [comparator_value]
    have hpos (x : Bool) := lt_of_lt_of_le zero_lt_one (ψ.property x)
    have : 0 < 63 * ψ.val false / ψ.val true := by positivity [hpos false, hpos true]
    linarith
  refine ⟨?_, hstrict⟩
  letI : Nonempty (Weight Bool) := ⟨weight 1 le_rfl⟩
  apply le_antisymm _ (le_ciInf fun ψ => (hstrict ψ).le)
  by_contra! h
  let d := (⨅ ψ : Weight Bool, comparatorBound model policy initial 0 ψ) - 7
  have hd : 0 < d := sub_pos.mpr h
  let t := 1 + 63 / d
  have ht : 1 ≤ t := le_add_of_nonneg_right (by positivity)
  have hlo : BddBelow (Set.range (comparatorBound model policy initial 0)) :=
    ⟨7, Set.forall_mem_range.mpr fun ψ => (hstrict ψ).le⟩
  have hinf := ciInf_le hlo (weight t ht)
  rw [comparator_value] at hinf
  change _ ≤ 7 + 63 * 1 / t at hinf
  have hs : 63 / t < d := by
    apply (div_lt_iff₀ (zero_lt_one.trans_le ht)).mpr
    dsimp only [t]
    field_simp
    linarith
  dsimp only [d] at hs
  linarith

end Kadp.Examples.Theorem2
