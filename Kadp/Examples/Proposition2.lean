import Kadp.SampledRSALP
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! A two-coordinate example where solving the printed subproblem (22) can
    return the same iterate even though (9) has a strictly better feasible point. -/

namespace Kadp.Examples.Proposition2

open SampledRSALP

/-- One draw of the first state. The two actions select their respective
    successor states deterministically. -/
noncomputable def problem : SampledRSALP Bool Bool ℝ 1 where
  sample := fun _ => false
  sample_pos := by decide
  feature := fun x => if x then 2 else 0
  cost := fun _ a => if a then -1 else 0
  transition := fun _ a y => if a = y then 1 else 0
  transition_nonneg := by intros; split <;> norm_num
  transition_sum := by simp
  ν := fun _ => 1 / 2
  π := fun _ => 1 / 2
  ν_pos := by norm_num
  π_pos := by norm_num
  π_sum := by norm_num [Fintype.sum_bool]
  α := 1 / 2
  α_pos := by norm_num
  α_lt_one := by norm_num
  κ := 2
  κ_pos := by norm_num
  Γ := 1
  Γ_pos := by norm_num

noncomputable def allocation (u : ℝ) (_ : Fin 1) (a : Bool) : ℝ := if a then u else 2 - u

/-- With both coordinates free, the complement of the working set in (22)
    is empty. Its quadratic sum has coefficient one. -/
noncomputable def printedObjective (l : Fin 1 → Bool → ℝ) : ℝ :=
  (∑ i, ∑ a, ∑ j, ∑ b, l j b * problem.gramCoeff i a j b * l i a) +
    ∑ i, ∑ a, l i a * problem.linearCoeff i a

theorem allocation_feasible (u : ℝ) :
    problem.DualFeasible (allocation u) ↔ 0 ≤ u ∧ u ≤ 2 := by
  norm_num [DualFeasible, allocation, problem, Fin.forall_fin_one, Fintype.sum_bool,
    Bool.forall_bool, and_comm]

theorem objectives (u : ℝ) :
    problem.dualObjective (allocation u) = u ^ 2 / 2 - u ∧
    printedObjective (allocation u) = u ^ 2 - u := by
  norm_num [dualObjective, printedObjective, dualConstant, gramCoeff, linearCoeff,
    weight, q, problem, allocation, Real.inner_apply, Fintype.sum_bool]
  constructor <;> ring

/-- The mass equality forces every feasible point to lie on the displayed line. -/
private theorem eq_allocation {l : Fin 1 → Bool → ℝ} (hl : problem.DualFeasible l) :
    l = allocation (l 0 true) := by
  have hmass := hl.2.2
  norm_num [problem, Fintype.sum_bool] at hmass
  funext i a
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  cases a
  · dsimp [allocation]
    linarith
  · rfl

/-- The current iterate at u = 1/2 uniquely minimizes (22) on the whole
    feasible set. The feasible iterate at u = 1 strictly improves (9). -/
theorem printed22_stalls :
    problem.DualFeasible (allocation (1 / 2)) ∧
    (∀ l, problem.DualFeasible l → l ≠ allocation (1 / 2) →
      printedObjective (allocation (1 / 2)) < printedObjective l) ∧
    problem.DualFeasible (allocation 1) ∧
    problem.dualObjective (allocation 1) < problem.dualObjective (allocation (1 / 2)) := by
  refine ⟨(allocation_feasible _).mpr (by norm_num), ?_,
    (allocation_feasible _).mpr (by norm_num), ?_⟩
  · intro l hl hne
    have heq := eq_allocation hl
    have hu : l 0 true ≠ 1 / 2 := fun h => hne (heq.trans (congrArg allocation h))
    calc
      printedObjective (allocation (1 / 2)) = (1 / 2 : ℝ) ^ 2 - 1 / 2 := (objectives _).2
      _ < (l 0 true) ^ 2 - l 0 true := by nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hu)]
      _ = printedObjective (allocation (l 0 true)) := (objectives _).2.symm
      _ = printedObjective l := congrArg printedObjective heq.symm
  · rw [(objectives _).1, (objectives _).1]
    norm_num

end Kadp.Examples.Proposition2
