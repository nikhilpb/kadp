import Kadp.Approximation
import Kadp.Idealized
import Kadp.OneSidedConcentration
import Kadp.ResidualComplexity
import Kadp.UniformDeviation

/-! Theorem 3 of Bhat et al. for independent draws from any finite-state law. -/

namespace Kadp.Theorem3

open MeasureTheory FoML.ToFoML SargentStachurski.MarkovDecisionProcesses
open Kadp.Approximation Kadp.Idealized

variable {S A H : Type*} [Fintype S] [Fintype A] [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] (M : MDP S A) (Φ : S → H) (μ : S → A) {C B : ℝ}

/-- Corollary 1 on a fixed sample, in the sign orientation for a
population-minus-empirical deviation. FoML uses signed sums normalized by (1/N). -/
private theorem empirical_negative_policyResidual_le (hC : 0 ≤ C) (hB : 0 ≤ B)
    {N : ℕ} (hN : 0 < N) (X : Fin N → S) :
    empiricalRademacherComplexity_without_abs N
      (fun (p : Parameters H C B) x => -policyResidual M μ (fit Φ p) x) X ≤
      (envelope Φ M C B / 2) / Real.sqrt N := by
  letI := parameters_nonempty (H := H) hC hB
  let w := fun p : Parameters H C B => p.val.1
  let b := fun p : Parameters H C B => (1 - M.β) * p.val.2
  have hb (p : Parameters H C B) : |b p| ≤ (1 - M.β) * B := by
    rw [show |b p| = (1 - M.β) * |p.val.2| by
      simp [b, abs_mul, abs_of_pos (sub_pos.mpr M.β_lt_one)]]
    exact mul_le_mul_of_nonneg_left p.property.2 (sub_nonneg.mpr M.β_lt_one.le)
  have he := empirical_negative_residual_le hN (featureDifference Φ M μ) w b
    (fun x => -M.rσ μ x) X (norm_featureDifference Φ M μ) (fun p => p.property.1) hb
  simp only [policyResidual, fit_residual_eq]
  refine he.trans (div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _))
  unfold envelope
  have h₁ := mul_nonneg hC (mul_nonneg (norm_nonneg Φ) (by linarith only [M.β_pos] : 0 ≤ 1 + M.β))
  have h₂ := mul_nonneg (sub_nonneg.mpr M.β_lt_one.le) hB
  linarith [norm_nonneg M.r]

/-- Theorem 3. For any fixed policy and any sampling distribution, the probability
that the supremum of the population-minus-sample residual reaches ε is at most δ.
The supremum ranges over all affine fits satisfying the two radius constraints. -/
theorem theorem3 [MeasurableSpace S] [MeasurableSingletonClass S]
    (P : Measure S) [IsProbabilityMeasure P]
    (hC : 0 ≤ C) (hB : 0 ≤ B) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ₁ : δ < 1)
    {N : ℕ} (hN : 0 < N)
    (hsize : (envelope Φ M C B * (1 + Real.sqrt (2 * Real.log (1 / δ)))) ^ 2 / ε ^ 2 ≤ N) :
    (Measure.pi (fun _ : Fin N => P)).real {X | ε ≤ ⨆ p : Parameters H C B,
      (∫ x, policyResidual M μ (fit Φ p) x ∂P) - sampleMean X (policyResidual M μ (fit Φ p))} ≤ δ := by
  letI := parameters_nonempty (H := H) hC hB
  let D := envelope Φ M C B
  let f (p : Parameters H C B) := policyResidual M μ (fit Φ p)
  have hf (p : Parameters H C B) (x : S) : |f p x| ≤ D / 2 := abs_residual_le Φ M μ hC hB p x
  change (Measure.pi (fun _ : Fin N => P)).real
    {X | ε ≤ ⨆ p, (∫ x, f p x ∂P) - sampleMean X (f p)} ≤ δ
  rcases (envelope_nonneg Φ M hC hB).eq_or_lt with hzero | hpos
  · have hzero_f (p : Parameters H C B) : f p = 0 := by
      funext x
      have hz := hf p x
      rwa [show D = 0 from hzero.symm, zero_div, abs_nonpos_iff] at hz
    simp [hzero_f, sampleMean, hε.not_ge, hδ.le]
  · have hrad : rademacherComplexity_without_abs N (fun p x => -f p x) P id ≤
        (D / 2) / Real.sqrt N := by
      unfold rademacherComplexity_without_abs
      calc
        _ ≤ ∫ _ : Fin N → S, (D / 2) / Real.sqrt N ∂Measure.pi (fun _ => P) :=
          integral_mono Integrable.of_finite (integrable_const _) fun X =>
            empirical_negative_policyResidual_le M Φ μ hC hB hN X
        _ = _ := by simp
    have hradius : confidenceRadius 1 (D / 2) δ N ≤ confidenceRadius 1 D δ N :=
      mul_le_mul_of_nonneg_right (by dsimp [D]; linarith) (Real.sqrt_nonneg _)
    have hthreshold := (confidence_and_complexity_le hpos hε hsize).2
    have htail := populationDeviation_tail_neg P f hN (half_pos hpos) hδ hδ₁ hf
    refine le_trans ?_ htail
    refine measureReal_mono ?_ (measure_ne_top _ _)
    intro X hX
    exact ((add_le_add (mul_le_mul_of_nonneg_left hrad (by norm_num)) hradius).trans hthreshold).trans
      (by simpa only [Set.mem_setOf_eq, sampleMean, div_eq_inv_mul] using hX)

end Kadp.Theorem3
