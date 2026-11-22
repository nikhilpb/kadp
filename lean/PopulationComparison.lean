import Theorem1

/-! The empirical optimizer compared with a fixed value function in population.
The two deviations have opposite directions: the fitted fixed-policy residual
can exceed its sample mean, while the comparator can incur excess sample slack. -/

namespace Kadp.Theorem2

open Matrix MeasureTheory SargentStachurski.MarkovDecisionProcesses
open Kadp.Occupancy Kadp.Approximation Kadp.Idealized Kadp.Theorem1

variable {S A H : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
  (M : MDP S A)

/-- The deterministic part of (26), using the two one-sided deviations. -/
theorem error_le_population (μ : S → A) (hμ : M.IsOptimal μ) (ν : S → ℝ)
    (hν : IsDistribution ν) {N : ℕ} (X : Fin N → S) (J V : S → ℝ) (ε : ℝ)
    (hfit : sampleObjective M ν X V ≤ sampleObjective M ν X J)
    (hdev : discountedOccupancy M μ ν ⬝ᵥ policyResidual M μ J ≤
      sampleMean X (policyResidual M μ J) + ε)
    (hcomp : sampleMean X (bellmanResidual M V) ≤
      discountedOccupancy M μ ν ⬝ᵥ bellmanResidual M V + ε) :
    weightedL1 ν (optimalCost M - J) ≤ ν ⬝ᵥ (optimalCost M - V) +
      2 / (1 - M.β) * (discountedOccupancy M μ ν ⬝ᵥ bellmanResidual M V) +
      4 * ε / (1 - M.β) := by
  refine (error_le_sample_comparator M μ ν X hμ hν J V ε hfit hdev).trans ?_
  have hscale : 0 ≤ 2 / (1 - M.β) :=
    div_nonneg (by norm_num) (sub_nonneg.mpr M.β_lt_one.le)
  calc
    _ ≤ ν ⬝ᵥ (optimalCost M - V) + 2 / (1 - M.β) *
        (discountedOccupancy M μ ν ⬝ᵥ bellmanResidual M V + ε + ε) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add hcomp le_rfl) hscale)
    _ = _ := by ring

variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] (Φ : S → H) {C B : ℝ}
variable [MeasurableSpace S] [MeasurableSingletonClass S]

/-- Simultaneous control of all sampled optimizers for one prespecified comparator.
The confidence follows by removing its upper-tail failure set from the fitted
class's uniform lower-deviation event. -/
theorem fixed_comparator (μ : S → A) (hμ : M.IsOptimal μ) (ν : S → ℝ)
    (hν : IsDistribution ν) (hC : 0 ≤ C) (hB : 0 ≤ B)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ₁ : δ < 1)
    {N : ℕ} (hN : 0 < N)
    (hsize : (envelope Φ M C B * (1 + Real.sqrt (2 * Real.log (1 / δ)))) ^ 2 / ε ^ 2 ≤ N)
    (q : Parameters H C B) :
    1 - δ - δ ^ 4 ≤ (sampleLaw M μ ν hν N).real {X | ∀ (p : Parameters H C B) s,
      IsOptimizer M Φ ν X p s → weightedL1 ν (optimalCost M - fit Φ p) ≤
        ν ⬝ᵥ (optimalCost M - fit Φ q) +
        2 / (1 - M.β) * (discountedOccupancy M μ ν ⬝ᵥ bellmanResidual M (fit Φ q)) +
        4 * ε / (1 - M.β)} := by
  let law := sampleLaw M μ ν hν N
  letI : IsProbabilityMeasure law := by unfold law sampleLaw; infer_instance
  let π := discountedOccupancy M μ ν
  let hπ := occupancy_isDistribution M μ hν
  let f := bellmanResidual M (fit Φ q)
  let uniform : Set (Fin N → S) := {X | ∀ p : Parameters H C B,
    π ⬝ᵥ policyResidual M μ (fit Φ p) ≤ sampleMean X (policyResidual M μ (fit Φ p)) + ε}
  let bad : Set (Fin N → S) := {X | ε ≤ sampleMean X f - π ⬝ᵥ f}
  have huniform : 1 - δ ≤ law.real uniform :=
    uniform_policy_residual M Φ μ ν hν hC hB hε hδ hδ₁ hN hsize
  have hf (x : S) : f x ∈ Set.Icc 0 (envelope Φ M C B / 2) :=
    ⟨le_max_right _ _, (le_abs_self _).trans (abs_bellmanResidual_le M Φ hC hB q x)⟩
  have hbad : law.real bad ≤ δ ^ 4 := by
    have ht := fixed_comparator_tail (samplingPMF π hπ).toMeasure f hN
      (envelope_nonneg Φ M hC hB) hε hδ hδ₁ hf hsize
    simpa only [law, sampleLaw, bad, sampleMean, div_eq_inv_mul, π, sampling_integral] using ht
  have hboth : 1 - δ - δ ^ 4 ≤ law.real (uniform \ bad) := by
    have hsplit := measureReal_inter_add_sdiff (μ := law) (s := uniform) bad.toFinite.measurableSet
    have hpart : law.real (uniform ∩ bad) ≤ law.real bad := measureReal_mono Set.inter_subset_right
    linarith
  refine hboth.trans (measureReal_mono ?_ (by finiteness))
  intro X hX p s hp
  have hcomp := lt_of_not_ge (show ¬ ε ≤ sampleMean X f - π ⬝ᵥ f from hX.2)
  exact error_le_population M μ hμ ν hν X (fit Φ p) (fit Φ q) ε
    (sampleObjective_le_of_maximizes M ν X _ _ s hp.1 (hp.2 q)) (hX.1 p)
    (show sampleMean X f ≤ π ⬝ᵥ f + ε by linarith only [hcomp])

end Kadp.Theorem2
