import Kadp.Approximation
import Kadp.Idealized
import Kadp.ResidualComplexity
import Kadp.UniformDeviation

/-! The high-probability approximation guarantee for the idealized sampled program
(18). The event contains every optimizer of the original program with slacks. -/

namespace Kadp.Theorem1

open Matrix MeasureTheory SargentStachurski.MarkovDecisionProcesses
open Kadp.Occupancy Kadp.Approximation Kadp.Idealized

variable {S A H : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (M : MDP S A) (Φ : S → H) {C B : ℝ}

/-- An actual optimizer of (18), retaining one slack for each draw and the feature radii. -/
def IsOptimizer (ν : S → ℝ) {N : ℕ} (X : Fin N → S) (p : Parameters H C B) (s : Fin N → ℝ) : Prop :=
  SlackFeasible M X (fit Φ p) s ∧ ∀ (q : Parameters H C B) t,
    SlackFeasible M X (fit Φ q) t → slackObjective M ν (fit Φ q) t ≤ slackObjective M ν (fit Φ p) s

omit [DecidableEq S] [DecidableEq A] in
/-- Every draw admits a maximizer of the original, slack-constrained program. -/
theorem exists_optimizer (ν : S → ℝ) {N : ℕ} (X : Fin N → S) (hC : 0 ≤ C) (hB : 0 ≤ B) :
    ∃ (p : Parameters H C B) (s : Fin N → ℝ), IsOptimizer M Φ ν X p s := by
  letI := parameters_nonempty (H := H) hC hB
  obtain ⟨_, ⟨p, rfl⟩, s, hs, hmax⟩ := exists_slackOptimizer M ν X
    (Set.range (fit Φ : Parameters H C B → S → ℝ)) (Set.range_nonempty _) (compact_fits Φ)
  exact ⟨p, s, hs, fun q t ht => hmax _ (Set.mem_range_self q) t ht⟩

noncomputable def bestError (C B : ℝ) : ℝ :=
  ⨅ p : Parameters H C B, ‖optimalCost M - fit Φ p‖

/-- The infimum in (19) is attained, including when the feature Hilbert space has
infinite dimension. Only the compact set of fitted value vectors is needed. -/
theorem exists_best_fit (hC : 0 ≤ C) (hB : 0 ≤ B) :
    ∃ p : Parameters H C B, bestError M Φ C B = ‖optimalCost M - fit Φ p‖ := by
  letI := parameters_nonempty (H := H) hC hB
  obtain ⟨_, ⟨p, rfl⟩, hp⟩ := (compact_fits (C := C) (B := B) Φ).exists_isMinOn
    (Set.range_nonempty _) (f := fun J => ‖optimalCost M - J‖)
    ((continuous_const.sub continuous_id).norm.continuousOn)
  exact ⟨p, le_antisymm (ciInf_le ⟨0, Set.forall_mem_range.mpr fun _ => norm_nonneg _⟩ p)
    (le_ciInf fun q => hp (Set.mem_range_self q))⟩

omit [DecidableEq S] [DecidableEq A] in
/-- The envelope in Lemma 3 also bounds the positive Bellman residual. At each
state a greedy action realizes the Bellman minimum for this fit. -/
theorem abs_bellmanResidual_le (hC : 0 ≤ C) (hB : 0 ≤ B) (p : Parameters H C B) (x : S) :
    |bellmanResidual M (fit Φ p) x| ≤ envelope Φ M C B / 2 := by
  let μ := M.greedy (-(fit Φ p))
  have heq : costBellman M μ (fit Φ p) = optimalBellman M (fit Φ p) := by
    rw [costBellman_eq_neg_reward, optimalBellman, M.Tσ_eq_T_of_isGreedy (M.isGreedy_greedy _)]
  unfold bellmanResidual
  rw [← heq]
  exact abs_residual_le Φ M μ hC hB p x

variable [MeasurableSpace S] [MeasurableSingletonClass S]

/-- Independent draws from the discounted occupancy of the designated policy. -/
noncomputable def sampleLaw (μ : S → A) (ν : S → ℝ) (hν : IsDistribution ν) (N : ℕ) :
    Measure (Fin N → S) :=
  Measure.pi (fun _ : Fin N => (samplingPMF _ (occupancy_isDistribution M μ hν)).toMeasure)

omit [DecidableEq A] in
private theorem uniform_policy_residual (μ : S → A) (ν : S → ℝ) (hν : IsDistribution ν)
    (hC : 0 ≤ C) (hB : 0 ≤ B) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ₁ : δ < 1)
    {N : ℕ} (hN : 0 < N)
    (hsize : (envelope Φ M C B * (1 + Real.sqrt (2 * Real.log (1 / δ)))) ^ 2 / ε ^ 2 ≤ N) :
    1 - δ ≤ (sampleLaw M μ ν hν N).real {X | ∀ p : Parameters H C B,
      discountedOccupancy M μ ν ⬝ᵥ policyResidual M μ (fit Φ p) ≤
        sampleMean X (policyResidual M μ (fit Φ p)) + ε} := by
  letI := parameters_nonempty (H := H) hC hB
  let D := envelope Φ M C B
  let f (p : Parameters H C B) := policyResidual M μ (fit Φ p)
  have hf (p : Parameters H C B) (x : S) : |f p x| ≤ D / 2 := abs_residual_le Φ M μ hC hB p x
  rcases (envelope_nonneg Φ M hC hB).eq_or_lt with hzero | hpos
  · have h (p : Parameters H C B) : policyResidual M μ (fit Φ p) = 0 := by
      funext x
      have hz := hf p x
      rw [show D = 0 from hzero.symm, zero_div, abs_nonpos_iff] at hz
      exact hz
    have hall : {X : Fin N → S | ∀ p : Parameters H C B,
        discountedOccupancy M μ ν ⬝ᵥ policyResidual M μ (fit Φ p) ≤
          sampleMean X (policyResidual M μ (fit Φ p)) + ε} = Set.univ := by
      simp [h, sampleMean, hε.le]
    rw [hall]
    simpa [sampleLaw] using (sub_le_self 1 hδ.le)
  · let π := discountedOccupancy M μ ν
    let hπ := occupancy_isDistribution M μ hν
    let P := (samplingPMF π hπ).toMeasure
    have hrad (X : Fin N → S) : empiricalRademacherComplexity_without_abs N
        (fun i x => -f i x) X ≤ (D / 2) / Real.sqrt N := by
      let w := fun p : Parameters H C B => p.val.1
      let b := fun p : Parameters H C B => (1 - M.β) * p.val.2
      have hb (p : Parameters H C B) : |b p| ≤ (1 - M.β) * B := by
        rw [show |b p| = (1 - M.β) * |p.val.2| by
          simp [b, abs_mul, abs_of_pos (sub_pos.mpr M.β_lt_one)]]
        exact mul_le_mul_of_nonneg_left p.property.2 (sub_nonneg.mpr M.β_lt_one.le)
      have he := empirical_negative_residual_le hN (featureDifference Φ M μ) w b
        (fun x => -M.rσ μ x) X (norm_featureDifference Φ M μ) (fun p => p.property.1) hb
      simp only [f, policyResidual, fit_residual_eq]
      refine he.trans (div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _))
      dsimp only [D, envelope]
      have h₁ := mul_nonneg hC (mul_nonneg (norm_nonneg Φ) (by linarith only [M.β_pos] : 0 ≤ 1 + M.β))
      have h₂ := mul_nonneg (sub_nonneg.mpr M.β_lt_one.le) hB
      linarith [norm_nonneg M.r]
    have hu := uniform_population_le_empirical P f hpos hε hδ hδ₁ hf hrad hsize
    simpa only [P, sampling_integral, π, f, sampleLaw, sampleMean, div_eq_inv_mul] using hu

/-- The stronger guarantee: simultaneously for all maximizers of (18), at confidence
1 − δ, with only one sampling error term. -/
theorem strengthened (μ : S → A) (hμ : M.IsOptimal μ) (ν : S → ℝ) (hν : IsDistribution ν)
    (hC : 0 ≤ C) (hB : 0 ≤ B) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ₁ : δ < 1)
    {N : ℕ} (hN : 0 < N)
    (hsize : (envelope Φ M C B * (1 + Real.sqrt (2 * Real.log (1 / δ)))) ^ 2 / ε ^ 2 ≤ N) :
    1 - δ ≤ (sampleLaw M μ ν hν N).real {X | ∀ (p : Parameters H C B) s,
      IsOptimizer M Φ ν X p s → weightedL1 ν (optimalCost M - fit Φ p) ≤
        (3 + M.β) / (1 - M.β) * bestError M Φ C B + 2 * ε / (1 - M.β)} := by
  obtain ⟨q, hq⟩ := exists_best_fit M Φ hC hB
  refine (uniform_policy_residual M Φ μ ν hν hC hB hε hδ hδ₁ hN hsize).trans (measureReal_mono ?_ ?_)
  · intro X hd p s hp
    rw [hq]
    apply oracle_bound M μ ν X hN hμ hν _ _ ε _ (hd p)
    exact sampleObjective_le_of_maximizes M ν X _ _ s hp.1 (hp.2 q)
  · unfold sampleLaw
    finiteness

/-- Theorem 1, equation (19), with the paper's sample threshold, approximation
coefficient, sampling error and confidence. -/
theorem theorem1 (μ : S → A) (hμ : M.IsOptimal μ) (ν : S → ℝ) (hν : IsDistribution ν)
    (hC : 0 ≤ C) (hB : 0 ≤ B) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    {N : ℕ} (hN : 0 < N)
    (hsize : (envelope Φ M C B * (1 + Real.sqrt (2 * Real.log (1 / δ)))) ^ 2 / ε ^ 2 ≤ N) :
    1 - δ - δ ^ 4 ≤ (sampleLaw M μ ν hν N).real {X | ∀ (p : Parameters H C B) s,
      IsOptimizer M Φ ν X p s → weightedL1 ν (optimalCost M - fit Φ p) ≤
        (3 + M.β) / (1 - M.β) * bestError M Φ C B + 4 * ε / (1 - M.β)} := by
  by_cases hδ₁ : δ < 1
  swap
  · exact (by linarith [le_of_not_gt hδ₁, pow_nonneg hδ.le 4] : 1 - δ - δ ^ 4 ≤ 0).trans measureReal_nonneg
  refine (sub_le_self _ (by positivity : 0 ≤ δ ^ 4)).trans
    ((strengthened M Φ μ hμ ν hν hC hB hε hδ hδ₁ hN hsize).trans (measureReal_mono ?_ ?_))
  · intro X h p s hp
    apply (h p s hp).trans
    apply add_le_add le_rfl
    exact div_le_div_of_nonneg_right (by linarith only [hε] : 2 * ε ≤ 4 * ε) (sub_nonneg.mpr M.β_lt_one.le)
  · unfold sampleLaw
    finiteness

end Kadp.Theorem1
