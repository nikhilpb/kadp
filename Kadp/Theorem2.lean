import Kadp.PopulationComparison
import Kadp.Weighted

/-! The weighted approximation guarantee for the idealized sampled program (18). -/

namespace Kadp.Theorem2

open Matrix MeasureTheory SargentStachurski.MarkovDecisionProcesses
open Kadp.Occupancy Kadp.Approximation Kadp.Idealized Kadp.Theorem1

variable {S A H : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (M : MDP S A) (Φ : S → H) {C B : ℝ}

/-- The signed initial error plus the population penalty for the positive Bellman residual. -/
noncomputable def populationCriterion (μ : S → A) (ν V : S → ℝ) : ℝ :=
  ν ⬝ᵥ (optimalCost M - V) +
    2 / (1 - M.β) * (discountedOccupancy M μ ν ⬝ᵥ bellmanResidual M V)

/-- Choose the comparator before sampling, by minimizing a continuous function of the
fitted value vector. This avoids requiring an extremizing Lyapunov weight. -/
theorem exists_population_minimizer (μ : S → A) (ν : S → ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B) :
    ∃ q : Parameters H C B, ∀ p : Parameters H C B,
      populationCriterion M μ ν (fit Φ q) ≤ populationCriterion M μ ν (fit Φ p) := by
  letI := parameters_nonempty (H := H) hC hB
  have hc : Continuous (populationCriterion M μ ν) := by
    unfold populationCriterion dotProduct
    have hres := continuous_bellmanResidual M
    fun_prop
  obtain ⟨_, ⟨q, rfl⟩, hmin⟩ := (compact_fits (C := C) (B := B) Φ).exists_isMinOn
    (Set.range_nonempty _) hc.continuousOn
  exact ⟨q, fun p => hmin (Set.mem_range_self p)⟩

open Kadp.Weighted

/-- The joint infimum over bounded affine fits and all weights ψ ≥ 1 in (25). -/
noncomputable def bestWeightedBound (μ : S → A) (ν : S → ℝ) (C B : ℝ) : ℝ :=
  ⨅ pair : Parameters H C B × Weight S, comparatorBound M μ ν (fit Φ pair.1) pair.2

variable [MeasurableSpace S] [MeasurableSingletonClass S]

/-- Theorem 2, equation (25). On the same draw every optimizer satisfies the bound
against the joint infimum, whether or not any admissible weight attains it. -/
theorem theorem2 (μ : S → A) (hμ : M.IsOptimal μ) (ν : S → ℝ) (hν : IsDistribution ν)
    (hC : 0 ≤ C) (hB : 0 ≤ B) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    {N : ℕ} (hN : 0 < N)
    (hsize : (envelope Φ M C B * (1 + Real.sqrt (2 * Real.log (1 / δ)))) ^ 2 / ε ^ 2 ≤ N) :
    1 - δ - δ ^ 4 ≤ (sampleLaw M μ ν hν N).real {X | ∀ (p : Parameters H C B) s,
      IsOptimizer M Φ ν X p s → weightedL1 ν (optimalCost M - fit Φ p) ≤
        bestWeightedBound M Φ μ ν C B + 4 * ε / (1 - M.β)} := by
  by_cases hδ₁ : δ < 1
  swap
  · exact (by linarith [le_of_not_gt hδ₁, pow_nonneg hδ.le 4] : 1 - δ - δ ^ 4 ≤ 0).trans measureReal_nonneg
  obtain ⟨q, hmin⟩ := exists_population_minimizer M Φ μ ν hC hB
  letI := parameters_nonempty (H := H) hC hB
  letI : Nonempty (Weight S) := ⟨unitWeight S⟩
  have hbound : populationCriterion M μ ν (fit Φ q) ≤ bestWeightedBound M Φ μ ν C B := by
    apply le_ciInf
    intro pair
    exact (hmin pair.1).trans (population_le_comparatorBound M μ ν (fit Φ pair.1) pair.2 hν)
  refine (fixed_comparator M Φ μ hμ ν hν hC hB hε hδ hδ₁ hN hsize q).trans (measureReal_mono ?_ ?_)
  · intro X h p s hp
    exact (h p s hp).trans (add_le_add hbound le_rfl)
  · unfold sampleLaw
    finiteness

end Kadp.Theorem2
