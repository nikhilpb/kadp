import Kadp.SampledRSALP
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Kadp.Examples.Proposition1

open SampledRSALP

/-- One state, action and draw. The ambient feature space is the real line. -/
noncomputable def singleton (g k : ℝ) (hk : 0 < k) : SampledRSALP Unit Unit ℝ 1 where
  sample := fun _ => ()
  sample_pos := by decide
  feature := fun _ => 0
  cost := fun _ _ => g
  transition := fun _ _ _ => 1
  transition_nonneg := by simp
  transition_sum := by simp
  ν := fun _ => 1
  π := fun _ => 1
  ν_pos := by simp
  π_pos := by simp
  ν_sum := by simp
  π_sum := by simp
  α := 1 / 2
  α_pos := by norm_num
  α_lt_one := by norm_num
  κ := k
  κ_pos := hk
  Γ := 2
  Γ_pos := by norm_num

private theorem primal_feasible_iff (g k : ℝ) (hk : 0 < k) (z b : ℝ) (s : Fin 1 → ℝ) :
    (singleton g k hk).PrimalFeasible z b s ↔ 0 ≤ s 0 ∧ b ≤ g + 1 / 2 * b + s 0 := by
  simp [PrimalFeasible, value, singleton, Fin.forall_fin_one]

private theorem primal_objective_eq (g k : ℝ) (hk : 0 < k) (z b : ℝ) (s : Fin 1 → ℝ) :
    (singleton g k hk).primalObjective z b s = b - k * s 0 - z ^ 2 := by
  norm_num [primalObjective, singleton, Real.inner_apply]

private theorem dual_feasible_iff (g k : ℝ) (hk : 0 < k) (l : Fin 1 → Unit → ℝ) :
    (singleton g k hk).DualFeasible l ↔ 0 ≤ l 0 () ∧ l 0 () ≤ k ∧ l 0 () = 2 := by
  norm_num [DualFeasible, singleton, Fin.forall_fin_one]
  exact fun _ _ => ⟨fun h => h (), fun h a => by cases a; exact h⟩

private theorem dual_objective_eq (g k : ℝ) (hk : 0 < k) (l : Fin 1 → Unit → ℝ) :
    (singleton g k hk).dualObjective l = 2 * g * l 0 () := by
  norm_num [dualObjective, gramCoeff, linearCoeff, dualConstant, singleton]

/-- (6) exceeds any real bound at cost zero and penalty one. -/
theorem primal_unbounded : ¬ BddAbove (singleton 0 1 (by norm_num)).primalValues := by
  rintro ⟨M, hM⟩
  let t := max M 0 + 1
  have ht : 0 ≤ t := by dsimp [t]; linarith [le_max_right M 0]
  have hmem : t ∈ (singleton 0 1 (by norm_num)).primalValues := by
    refine ⟨0, 2 * t, fun _ => t, (primal_feasible_iff ..).mpr ⟨ht, ?_⟩, ?_⟩
    · linarith
    · rw [primal_objective_eq]
      linarith
  have h := hM hmem
  dsimp [t] at h
  linarith [le_max_left M 0]

/-- The row cap of (9) is one, while its total mass must be two. -/
theorem dual_infeasible : ¬ ∃ l, (singleton 0 1 (by norm_num)).DualFeasible l := by
  rintro ⟨l, hl⟩
  obtain ⟨_, hcap, hmass⟩ := (dual_feasible_iff ..).mp hl
  linarith

/-- With cost one and penalty four, the maximum of (6) is attained at two. -/
theorem primal_maximum_two : IsGreatest (singleton 1 4 (by norm_num)).primalValues 2 := by
  constructor
  · refine ⟨0, 2, fun _ => 0, (primal_feasible_iff ..).mpr ?_, ?_⟩
    · norm_num
    · rw [primal_objective_eq]
      norm_num
  · rintro v ⟨z, b, s, hf, rfl⟩
    obtain ⟨hs, hb⟩ := (primal_feasible_iff ..).mp hf
    rw [primal_objective_eq]
    nlinarith [sq_nonneg z]

/-- On the same data, (9) attains its minimum at four. -/
theorem dual_minimum_four : IsLeast (singleton 1 4 (by norm_num)).dualValues 4 := by
  constructor
  · refine ⟨fun _ _ => 2, (dual_feasible_iff ..).mpr ?_, ?_⟩
    · norm_num
    · rw [dual_objective_eq]
      norm_num
  · rintro v ⟨l, hf, rfl⟩
    obtain ⟨_, _, heq⟩ := (dual_feasible_iff ..).mp hf
    rw [dual_objective_eq, heq]
    norm_num

end Kadp.Examples.Proposition1
