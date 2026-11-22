import Theorem3

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
theorem uniform_policy_residual (μ : S → A) (ν : S → ℝ) (hν : IsDistribution ν)
    (hC : 0 ≤ C) (hB : 0 ≤ B) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ₁ : δ < 1)
    {N : ℕ} (hN : 0 < N)
    (hsize : (envelope Φ M C B * (1 + Real.sqrt (2 * Real.log (1 / δ)))) ^ 2 / ε ^ 2 ≤ N) :
    1 - δ ≤ (sampleLaw M μ ν hν N).real {X | ∀ p : Parameters H C B,
      discountedOccupancy M μ ν ⬝ᵥ policyResidual M μ (fit Φ p) ≤
        sampleMean X (policyResidual M μ (fit Φ p)) + ε} := by
  let π := discountedOccupancy M μ ν
  let hπ := occupancy_isDistribution M μ hν
  let P := (samplingPMF π hπ).toMeasure
  let f (p : Parameters H C B) := policyResidual M μ (fit Φ p)
  let E : Set (Fin N → S) := {X | ε ≤ ⨆ p, π ⬝ᵥ f p - sampleMean X (f p)}
  have htail : (Measure.pi (fun _ : Fin N => P)).real E ≤ δ := by
    simpa only [E, f, P, sampling_integral] using
      Theorem3.theorem3 M Φ μ P hC hB hε hδ hδ₁ hN hsize
  have hgood : 1 - δ ≤ (Measure.pi (fun _ : Fin N => P)).real Eᶜ := by
    rw [probReal_compl_eq_one_sub E.toFinite.measurableSet]
    linarith
  refine hgood.trans (measureReal_mono ?_)
  intro X hX p
  have hneg (q : Parameters H C B) (x : S) : |-f q x| ≤ envelope Φ M C B / 2 := by
    rw [abs_neg]
    exact abs_residual_le Φ M μ hC hB q x
  have hle := FoML.ToFoML.le_oneSidedDeviation (μ := P) hN id hneg X p
  simp only [FoML.ToFoML.oneSidedDeviation, id_eq, integral_neg, Finset.sum_neg_distrib,
    mul_neg, neg_sub_neg, P, sampling_integral, ← div_eq_inv_mul] at hle
  change π ⬝ᵥ f p - sampleMean X (f p) ≤ ⨆ q, π ⬝ᵥ f q - sampleMean X (f q) at hle
  change ¬ε ≤ ⨆ q, π ⬝ᵥ f q - sampleMean X (f q) at hX
  change π ⬝ᵥ f p ≤ sampleMean X (f p) + ε
  linarith [lt_of_not_ge hX]

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
