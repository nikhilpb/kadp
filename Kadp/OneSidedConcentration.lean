import FoML.ToFoML.OneSidedDeviation
import FoML.ForMathlib.Probability.Confidence

/-! Lemma 1 of *Kernel-based approximate dynamic programming*. On a countable
discrete state space (in particular, a finite state space), the topology of
pointwise convergence gives every indexed function class a countably dense
subclass. FoML's one-sided symmetrization and McDiarmid bound therefore apply
even when the class itself is uncountable. -/

namespace Kadp

open MeasureTheory FoML.ToFoML
open scoped BigOperators

variable {S ι : Type*} [MeasurableSpace S]

/-- The paper's expected Rademacher complexity. The outer expectation samples
the states independently from `P`; the finite average samples the independent
fair signs. The signed sum uses the paper's factor `2/n`. -/
noncomputable def paperRademacherComplexity (n : ℕ) (f : ι → S → ℝ)
    (P : Measure S) : ℝ :=
  ∫ X : Fin n → S, (Fintype.card (Signs n) : ℝ)⁻¹ *
    ∑ σ : Signs n, ⨆ i, (2 / (n : ℝ)) * ∑ j, (σ j : ℝ) * f i (X j)
    ∂Measure.pi (fun _ => P)

/-- Conversion from the paper's normalization to FoML's. -/
theorem paperRademacherComplexity_eq (n : ℕ) (f : ι → S → ℝ) (P : Measure S) :
    paperRademacherComplexity n f P = 2 * rademacherComplexity_without_abs n f P id := by
  unfold paperRademacherComplexity rademacherComplexity_without_abs
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with X
  unfold empiricalRademacherComplexity_without_abs
  simp only [Function.id_comp]
  rw [mul_left_comm 2]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Real.mul_iSup_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [div_eq_mul_inv, mul_assoc]

/-- Reversing every sign preserves its joint distribution. Consequently a
class and its pointwise negative have the same expected complexity. -/
theorem rademacherComplexity_neg_eq (n : ℕ) (f : ι → S → ℝ) (P : Measure S) :
    rademacherComplexity_without_abs n (fun i x => -f i x) P id =
      rademacherComplexity_without_abs n f P id := by
  unfold rademacherComplexity_without_abs
  apply integral_congr_ae
  filter_upwards with X
  unfold empiricalRademacherComplexity_without_abs
  congr 1
  simpa only [negSigns_apply_coe, neg_mul, mul_neg] using
    sum_signs_neg_eq (fun σ : Signs n =>
      ⨆ i, (n : ℝ)⁻¹ * ∑ j, (σ j : ℝ) * f i ((id ∘ X) j))

/-- The population-minus-empirical tail in the orientation of FoML's
one-sided deviation applied to the negated class. -/
theorem populationDeviation_tail_neg [Countable S] [MeasurableSingletonClass S] [Nonempty ι]
    (P : Measure S) [IsProbabilityMeasure P] (f : ι → S → ℝ) {n : ℕ} {B δ : ℝ}
    (hn : 0 < n) (hB : 0 < B) (hδ : 0 < δ) (hδ₁ : δ < 1) (hf : ∀ i x, |f i x| ≤ B) :
    (Measure.pi (fun _ : Fin n => P)).real {X |
      2 * rademacherComplexity_without_abs n (fun i x => -f i x) P id + confidenceRadius 1 B δ n ≤
        ⨆ i, (∫ x, f i x ∂P) - (n : ℝ)⁻¹ * ∑ j, f i (X j)} ≤ δ := by
  classical
  letI : Nonempty S := nonempty_of_isProbabilityMeasure P
  let G (i : ι) (x : S) := -f i x
  letI : TopologicalSpace ι := TopologicalSpace.induced G inferInstance
  letI : SecondCountableTopology ι := TopologicalSpace.secondCountableTopology_induced ι (S → ℝ) G
  have hG : Continuous G := continuous_induced_dom
  have hcont (x : S) : Continuous fun i => G i x := (continuous_apply x).comp hG
  have hmeas (i : ι) : Measurable (G i) := measurable_of_countable _
  have hbound (i : ι) (x : S) : |G i x| ≤ B := by simpa [G] using hf i x
  have hrad : 0 ≤ confidenceRadius 1 B δ n := by unfold confidenceRadius; positivity
  have htail := oneSidedDeviation_tail_bound_countable_of_pos (μ := P) (n := n)
    (denseRestriction G) (measurable_denseRestriction_apply hmeas) id measurable_id hB
    (abs_denseRestriction_le hbound) hrad
  have hexp := mul_exp_neg_confidenceRadius_sq hn (κ := 1) (by norm_num) hB hδ hδ₁.le
  rw [one_mul] at hexp
  rw [hexp, ← rademacherComplexity_without_abs_denseRestriction n G hcont P id,
    ← oneSidedDeviation_denseRestriction n G hmeas id measurable_id hbound hcont P] at htail
  simpa only [measureReal_def, G, oneSidedDeviation, Function.id_comp, id_eq, integral_neg,
    Finset.sum_neg_distrib, mul_neg, neg_sub_neg] using htail

/-- Corrected Lemma 1. With a positive uniform absolute bound and a nonempty
sample, the closed upper-tail event has probability at most `δ`. -/
theorem lemma1_populationDeviation_tail [Countable S] [MeasurableSingletonClass S] [Nonempty ι]
    (P : Measure S) [IsProbabilityMeasure P] (f : ι → S → ℝ) {n : ℕ} {B δ : ℝ}
    (hn : 0 < n) (hB : 0 < B) (hδ : 0 < δ) (hδ₁ : δ < 1) (hf : ∀ i x, |f i x| ≤ B) :
    (Measure.pi (fun _ : Fin n => P)).real {X |
      paperRademacherComplexity n f P + Real.sqrt (2 * B ^ 2 * Real.log (1 / δ) / n) ≤
        ⨆ i, (∫ x, f i x ∂P) - (n : ℝ)⁻¹ * ∑ j, f i (X j)} ≤ δ := by
  have h := populationDeviation_tail_neg P f hn hB hδ hδ₁ hf
  rw [rademacherComplexity_neg_eq, ← paperRademacherComplexity_eq] at h
  have hr : Real.sqrt (2 * B ^ 2 * Real.log (1 / δ) / n) = confidenceRadius 1 B δ n := by
    rw [show 2 * B ^ 2 * Real.log (1 / δ) / n = B ^ 2 * (2 * Real.log (1 / δ) / n) by ring,
      Real.sqrt_mul (sq_nonneg B), Real.sqrt_sq hB.le]
    rfl
  rwa [hr]

/-- At envelope zero the singleton zero class has zero complexity and zero
deviation on every sample. The probability of the paper's closed event is
one, disproving its unqualified bound for every `δ < 1`. -/
theorem lemma1_zero_envelope_probability (P : Measure S) [IsProbabilityMeasure P] (n : ℕ) (δ : ℝ) :
    (Measure.pi (fun _ : Fin n => P)).real {X |
      paperRademacherComplexity n (fun (_ : Unit) (_ : S) => (0 : ℝ)) P +
        Real.sqrt (2 * (0 : ℝ) ^ 2 * Real.log (1 / δ) / n) ≤
          ⨆ _ : Unit, (∫ _ : S, (0 : ℝ) ∂P) - (n : ℝ)⁻¹ * ∑ j : Fin n, (fun _ : S => (0 : ℝ)) (X j)} = 1 := by
  simp [paperRademacherComplexity]

end Kadp
