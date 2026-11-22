import SamplingLaw
import Theorem2

/-! The weighted-oracle form of the sampling-law bounds in Appendix B.3.
The comparator and its population slack are chosen using the actual draw law. -/

namespace Kadp.SamplingLaw

open Matrix MeasureTheory SargentStachurski.MarkovDecisionProcesses
open Kadp.Occupancy Kadp.Approximation Kadp.Idealized Kadp.Theorem1 Kadp.Weighted

variable {S A H : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (M : MDP S A) (Φ : S → H) {C B : ℝ}

/-- The joint infimum in (25), using the actual state law ρ in the slack term. -/
noncomputable def weightedInfimum (ν ρ : S → ℝ) (C B : ℝ) : ℝ :=
  ⨅ pair : Parameters H C B × Weight S,
    weightedSup pair.2 (optimalCost M - fit Φ pair.1) *
      (ν ⬝ᵥ pair.2.val + 2 * (ρ ⬝ᵥ pair.2.val) * (1 + M.β * drift M pair.2) / (1 - M.β))

theorem weightedInfimum_occupancy (μ : S → A) (ν : S → ℝ) (C B : ℝ) :
    weightedInfimum M Φ ν (discountedOccupancy M μ ν) C B =
      Kadp.Theorem2.bestWeightedBound M Φ μ ν C B := rfl

/-- Minimize the continuous population criterion before drawing any states.
The minimizer is valid for every Lyapunov weight, so no weight need attain the infimum. -/
private theorem exists_weighted_comparator (ν ρ : S → ℝ) (hν : IsDistribution ν)
    (hρ : IsDistribution ρ) (hC : 0 ≤ C) (hB : 0 ≤ B) :
    ∃ q : Parameters H C B, ν ⬝ᵥ (optimalCost M - fit Φ q) +
      2 / (1 - M.β) * (ρ ⬝ᵥ bellmanResidual M (fit Φ q)) ≤ weightedInfimum M Φ ν ρ C B := by
  letI := parameters_nonempty (H := H) hC hB
  letI : Nonempty (Weight S) := ⟨unitWeight S⟩
  let F (V : S → ℝ) := ν ⬝ᵥ (optimalCost M - V) + 2 / (1 - M.β) * (ρ ⬝ᵥ bellmanResidual M V)
  have hc : Continuous F := by
    dsimp [F, dotProduct]
    have hres := continuous_bellmanResidual M
    fun_prop
  obtain ⟨_, ⟨q,rfl⟩, hmin⟩ := (compact_fits (C := C) (B := B) Φ).exists_isMinOn
    (Set.range_nonempty _) hc.continuousOn
  refine ⟨q, le_ciInf (fun ⟨p,ψ⟩ => ?_)⟩
  let V := fit Φ p
  let d := weightedSup ψ (optimalCost M - V)
  let k := d * (1 + M.β * drift M ψ)
  have initial : ν ⬝ᵥ (optimalCost M - V) ≤ d * (ν ⬝ᵥ ψ.val) := by
    rw [← smul_eq_mul, ← dotProduct_smul]
    exact dotProduct_le_dotProduct_of_nonneg_left
      (fun x => (le_abs_self _).trans (abs_le_weightedSup_mul ψ (optimalCost M - V) x)) hν.nonneg
  have residual : ρ ⬝ᵥ bellmanResidual M V ≤ k * (ρ ⬝ᵥ ψ.val) := by
    rw [← smul_eq_mul, ← dotProduct_smul]
    exact dotProduct_le_dotProduct_of_nonneg_left (bellmanResidual_le_weight M V ψ) hρ.nonneg
  refine (hmin (Set.mem_range_self p)).trans ?_
  refine (add_le_add initial (mul_le_mul_of_nonneg_left residual
    (div_nonneg (by norm_num) (sub_nonneg.mpr M.β_lt_one.le)))).trans_eq ?_
  change d * _ + _ * (k * _) = d * _
  dsimp only [k]
  ring

variable [MeasurableSpace S] [MeasurableSingletonClass S]

/-- Total variation gives an additive correction to the joint weighted infimum,
under the iid law actually used for fitting. -/
theorem tv_weighted_infimum (μ : S → A) (hμ : M.IsOptimal μ) (ν ρ : S → ℝ)
    (hν : IsDistribution ν) (hρ : IsDistribution ρ) (hC : 0 ≤ C) (hB : 0 ≤ B)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) {N : ℕ} (hN : 0 < N)
    (hsize : (envelope Φ M C B * (1 + Real.sqrt (2 * Real.log (1 / δ)))) ^ 2 / ε ^ 2 ≤ N) :
    1 - δ - δ ^ 4 ≤ (iid ρ hρ N).real {X | ∀ (p : Parameters H C B) s, IsOptimizer M Φ ν X p s →
      weightedL1 ν (optimalCost M - fit Φ p) ≤ weightedInfimum M Φ ν ρ C B +
        (4 * ε + envelope Φ M C B * totalVariation (discountedOccupancy M μ ν) ρ) / (1 - M.β)} := by
  by_cases hδ₁ : δ < 1
  swap
  · exact (by linarith [le_of_not_gt hδ₁, pow_nonneg hδ.le 4] : 1 - δ - δ^4 ≤ 0).trans measureReal_nonneg
  obtain ⟨q,hq⟩ := exists_weighted_comparator M Φ ν ρ hν hρ hC hB
  refine (tv_fixed_comparator M Φ μ hμ ν ρ hν hρ hC hB hε hδ hδ₁ hN hsize q).trans (measureReal_mono ?_)
  intro X h p s hp
  refine (h p s hp).trans ?_
  calc
    _ = (ν ⬝ᵥ (optimalCost M - fit Φ q) + 2 / (1 - M.β) * (ρ ⬝ᵥ bellmanResidual M (fit Φ q))) +
      (4 * ε + envelope Φ M C B * totalVariation (discountedOccupancy M μ ν) ρ) / (1 - M.β) := by ring
    _ ≤ _ := add_le_add hq le_rfl

/-- Density domination gives a weighted-oracle bound depending on the optimizer's
observed slack average. It allows zero mass states without division by ρ. -/
theorem ratio_weighted_infimum (μ : S → A) (hμ : M.IsOptimal μ) (ν ρ : S → ℝ)
    (hν : IsDistribution ν) (hρ : IsDistribution ρ) (hC : 0 ≤ C) (hB : 0 ≤ B)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) {N : ℕ} (hN : 0 < N)
    (hsize : (envelope Φ M C B * (1 + Real.sqrt (2 * Real.log (1 / δ)))) ^ 2 / ε ^ 2 ≤ N)
    {k : ℝ} (hk : 0 ≤ k) (hdom : ∀ x, discountedOccupancy M μ ν x ≤ (1+k)*ρ x) :
    1 - δ - δ ^ 4 ≤ (iid ρ hρ N).real {X | ∀ (p : Parameters H C B) s, IsOptimizer M Φ ν X p s →
      weightedL1 ν (optimalCost M - fit Φ p) ≤ weightedInfimum M Φ ν ρ C B +
        2 / (1 - M.β) * ((2+k)*ε + k*((∑ i, s i)/N))} := by
  by_cases hδ₁ : δ < 1
  swap
  · exact (by linarith [le_of_not_gt hδ₁, pow_nonneg hδ.le 4] : 1 - δ - δ^4 ≤ 0).trans measureReal_nonneg
  obtain ⟨q,hq⟩ := exists_weighted_comparator M Φ ν ρ hν hρ hC hB
  refine (ratio_fixed_comparator M Φ μ hμ ν ρ hν hρ hC hB hε hδ hδ₁ hN hsize q hk hdom).trans
    (measureReal_mono ?_)
  intro X h p s hp
  refine (h p s hp).trans ?_
  calc
    _ = (ν ⬝ᵥ (optimalCost M - fit Φ q) + 2 / (1 - M.β) * (ρ ⬝ᵥ bellmanResidual M (fit Φ q))) +
      2 / (1 - M.β) * ((2+k)*ε + k*((∑ i, s i)/N)) := by ring
    _ ≤ _ := add_le_add hq le_rfl

end Kadp.SamplingLaw
