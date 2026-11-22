import Kadp.KernelPolicy
import Mathlib.Tactic.NormNum

/-! Two states and two actions. In the note, false/true denote states s/t and
    actions A/B respectively. Each action moves to the state with its own index. -/

namespace Kadp.Examples.KernelPolicy

open SampledRSALP

noncomputable def problem : SampledRSALP Bool Bool ℝ 1 where
  sample := fun _ => false
  sample_pos := by decide
  feature := fun x => if x then 2 else 1
  cost := fun x a => if x then 0 else if a then 1 else 5 / 4
  transition := fun _ a y => if a = y then 1 else 0
  transition_nonneg := by intros; split <;> norm_num
  transition_sum := by simp
  ν := fun x => if x then 1 / 4 else 3 / 4
  π := fun _ => 1 / 2
  ν_pos := by intro x; cases x <;> norm_num
  π_pos := by norm_num
  π_sum := by norm_num [Fintype.sum_bool]
  α := 1 / 2
  α_pos := by norm_num
  α_lt_one := by norm_num
  κ := 2
  κ_pos := by norm_num
  Γ := 1
  Γ_pos := by norm_num

noncomputable def K (x y : Bool) : ℝ := problem.feature x * problem.feature y

private theorem K_eq (x y : Bool) : K x y = inner ℝ (problem.feature x) (problem.feature y) := by
  simp [K, mul_comm]

def allocation (_ : Fin 1) (a : Bool) : ℝ := if a then 0 else 2

/-- The displayed primal point and multiplier are both optimal. -/
theorem optima : IsGreatest problem.primalValues (21 / 8) ∧ problem.DualFeasible allocation ∧
    ∀ k, problem.DualFeasible k → problem.kernelObjective K allocation ≤ problem.kernelObjective K k := by
  have hp : problem.PrimalFeasible (1 / 2) 2 (fun _ => 0) := by
    constructor
    · simp
    · intro i a
      cases a <;> norm_num [value, problem, Fintype.sum_bool, Real.inner_apply]
  have hl : problem.DualFeasible allocation := by
    norm_num [DualFeasible, allocation, problem, Fin.forall_fin_one, Fintype.sum_bool,
      Bool.forall_bool]
  have hP : problem.primalObjective (1 / 2) 2 (fun _ => 0) = 21 / 8 := by
    norm_num [primalObjective, weight, problem, Real.inner_apply]
  have hG : problem.correctedDualObjective allocation = 21 / 8 := by
    norm_num [correctedDualObjective, allocation, meanFeature, multiplierFeature,
      featureDiff_eq, weight, problem, Fintype.sum_bool, Real.norm_eq_abs]
  refine ⟨⟨⟨_, _, _, hp, hP⟩, ?_⟩, hl, ?_⟩
  · rintro _ ⟨z, b, s, h, rfl⟩
    exact (problem.weakDuality h hl).trans_eq hG
  · intro k hk
    have h := (problem.dualObjective_le_iff allocation k).mpr
      (hG.trans_le (hP ▸ problem.weakDuality hp hk))
    simpa only [← problem.kernelObjective_add_constant K_eq, add_le_add_iff_right] using h

theorem kernel_predictions : problem.kernelValue K allocation false = 1 / 2 ∧
    problem.kernelValue K allocation true = 1 := by
  norm_num [kernelValue, K, allocation, weight, problem, Fintype.sum_bool]

theorem greedy_sets : problem.greedyActions (problem.kernelValue K allocation) false = Set.univ ∧
    problem.greedyActions (problem.kernelValue K allocation) true = {false} := by
  have hJ : problem.kernelValue K allocation = fun x => if x then 1 else 1 / 2 := by
    funext x
    cases x
    · exact kernel_predictions.1
    · exact kernel_predictions.2
  rw [hJ]
  constructor <;> ext a <;> cases a <;>
    norm_num [greedyActions, actionScore, Fintype.sum_bool, Bool.forall_bool, problem]

/-- In row (s,B), restricting both coefficient sums to positive-probability
    successors changes Q from 0 to 1 and R from 1 to 5/2. -/
theorem successors_only_changes_coefficients :
    let successors := Finset.univ.filter fun y => 0 < problem.transition false true y
    let q := fun y => problem.q false y true
    problem.kernelGram K 0 true 0 true = 0 ∧
    (∑ y ∈ successors, ∑ z ∈ successors, q y * q z * K y z) = 1 ∧
    problem.kernelLinear K 0 true = 1 ∧
    problem.Γ * problem.cost false true -
      (∑ y ∈ successors, problem.weight false * q y * K false y) = 5 / 2 := by
  have hset : (Finset.univ.filter fun y => 0 < problem.transition false true y) = {true} := by
    ext y
    cases y <;> norm_num [problem]
  dsimp only
  rw [hset, problem.kernelGram_eq K_eq, problem.kernelLinear_eq K_eq]
  norm_num [gramCoeff, linearCoeff, weight, q, problem, K, Real.inner_apply, Fintype.sum_bool]

end Kadp.Examples.KernelPolicy
