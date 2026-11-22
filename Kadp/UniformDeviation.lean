import FoML.ToFoML.OneSidedDeviation
import FoML.ForMathlib.Probability.Confidence

/-! A uniform population-to-sample bound for a finite state space. -/

namespace Kadp

open MeasureTheory FoML.ToFoML
open scoped BigOperators

/-- A reindexed class has no larger one-sided empirical Rademacher complexity. -/
private theorem oneSidedComplexity_reindex_le {S I J : Type*} [Nonempty J]
    {n : ℕ} (hn : 0 < n) (G : I → S → ℝ) (e : J → I) (X : Fin n → S)
    {b : ℝ} (hG : ∀ i x, |G i x| ≤ b) :
    empiricalRademacherComplexity_without_abs n (fun j => G (e j)) X ≤
      empiricalRademacherComplexity_without_abs n G X := by
  unfold empiricalRademacherComplexity_without_abs
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => ?_) (by positivity)
  apply ciSup_le
  intro j
  refine le_ciSup (f := fun i => (n : ℝ)⁻¹ * ∑ k, (σ k : ℝ) * G i (X k)) ⟨b, ?_⟩ (e j)
  rintro _ ⟨i, rfl⟩
  refine (le_abs_self _).trans (abs_normalized_fin_sum_le hn
    (fun k x => (σ k : ℝ) * G i x) X fun k x => ?_)
  simpa [abs_mul, abs_sigma] using hG i x

/-- The sample threshold makes room for twice the expected complexity and the tail radius. -/
theorem confidence_and_complexity_le {D ε δ : ℝ} {n : ℕ}
    (hD : 0 < D) (hε : 0 < ε)
    (hn : (D * (1 + Real.sqrt (2 * Real.log (1 / δ)))) ^ 2 / ε ^ 2 ≤ n) :
    0 < n ∧ 2 * ((D / 2) / Real.sqrt n) + confidenceRadius 1 D δ n ≤ ε := by
  have hnum : 0 < D * (1 + Real.sqrt (2 * Real.log (1 / δ))) := by positivity
  have hnR : 0 < (n : ℝ) := lt_of_lt_of_le (div_pos (sq_pos_of_pos hnum) (sq_pos_of_pos hε)) hn
  have hroot := Real.sqrt_pos.2 hnR
  have hscale : D * (1 + Real.sqrt (2 * Real.log (1 / δ))) ≤ ε * Real.sqrt n := by
    apply (sq_le_sq₀ hnum.le (by positivity)).mp
    rw [mul_pow ε, Real.sq_sqrt hnR.le, mul_comm (ε ^ 2)]
    exact (div_le_iff₀ (sq_pos_of_pos hε)).mp hn
  refine ⟨Nat.cast_pos.mp hnR, ?_⟩
  unfold confidenceRadius
  rw [Real.sqrt_div' _ hnR.le]
  field_simp [hroot.ne']
  linarith

/-- At the stated sample size, every member of a uniformly bounded class satisfies the
population bound on the same event. Each possible failing sample supplies one violating
index. Since the sample space is finite, those indices suffice for the countable-class
Rademacher tail bound even when the original index type is uncountable. -/
theorem uniform_population_le_empirical {S ι : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] [Nonempty ι] (P : Measure S) [IsProbabilityMeasure P]
    (f : ι → S → ℝ) {n : ℕ} {D ε δ : ℝ} (hD : 0 < D) (hε : 0 < ε)
    (hδ : 0 < δ) (hδ₁ : δ < 1) (hf : ∀ i x, |f i x| ≤ D / 2)
    (hR : ∀ X : Fin n → S, empiricalRademacherComplexity_without_abs n
      (fun i x => -f i x) X ≤ (D / 2) / Real.sqrt n)
    (hn : (D * (1 + Real.sqrt (2 * Real.log (1 / δ)))) ^ 2 / ε ^ 2 ≤ n) :
    1 - δ ≤ (Measure.pi (fun _ : Fin n => P)).real
      {X | ∀ i, (∫ x, f i x ∂P) ≤ (n : ℝ)⁻¹ * ∑ j, f i (X j) + ε} := by
  classical
  letI : Nonempty S := nonempty_of_isProbabilityMeasure P
  obtain ⟨hnpos, hscale⟩ := confidence_and_complexity_le hD hε hn
  let good (X : Fin n → S) (i : ι) :=
    (∫ x, f i x ∂P) ≤ (n : ℝ)⁻¹ * ∑ j, f i (X j) + ε
  let witness (X : Fin n → S) := Classical.epsilon fun i => ¬good X i
  let G (Y : Fin n → S) (x : S) := -f (witness Y) x
  have hneg : ∀ i x, |-f i x| ≤ D / 2 := fun i x => (abs_neg _).le.trans (hf i x)
  have hG : ∀ Y x, |G Y x| ≤ D := fun Y x => (hneg (witness Y) x).trans (by linarith)
  have hrad : rademacherComplexity_without_abs n G P id ≤ (D / 2) / Real.sqrt n := by
    unfold rademacherComplexity_without_abs
    calc _ ≤ ∫ _ : Fin n → S, (D / 2) / Real.sqrt n ∂Measure.pi (fun _ => P) := by
              refine integral_mono Integrable.of_finite (integrable_const _) fun X => ?_
              exact (oneSidedComplexity_reindex_le hnpos (fun i x => -f i x)
                witness X hneg).trans (hR X)
      _ = _ := by simp
  have hrad_nonneg : 0 ≤ confidenceRadius 1 D δ n := by unfold confidenceRadius; positivity
  have htail := oneSidedDeviation_tail_bound_countable_of_pos (μ := P) (n := n)
    G (fun Y => measurable_of_finite _) id measurable_id hD hG hrad_nonneg
  have hexp := mul_exp_neg_confidenceRadius_sq hnpos (κ := 1) (by norm_num) hD hδ hδ₁.le
  rw [one_mul] at hexp
  rw [hexp] at htail
  let E : Set (Fin n → S) := {X | ∀ i, good X i}
  have hfail : (Measure.pi (fun _ : Fin n => P)).real Eᶜ ≤ δ := by
    refine (measureReal_mono (μ := Measure.pi fun _ : Fin n => P)
      (s₂ := {X | 2 * rademacherComplexity_without_abs n G P id +
      confidenceRadius 1 D δ n ≤ oneSidedDeviation n G P id (id ∘ X)}) ?_).trans htail
    intro X hX
    change ¬∀ i, good X i at hX
    have hbad : ¬good X (witness X) := Classical.epsilon_spec (Classical.not_forall.mp hX)
    have hdev := le_oneSidedDeviation (μ := P) hnpos id hG X X
    simp only [G, id_eq, integral_neg, Finset.sum_neg_distrib, mul_neg, sub_neg_eq_add] at hdev
    change ¬(∫ x, f (witness X) x ∂P) ≤ (n : ℝ)⁻¹ * ∑ j, f (witness X) (X j) + ε at hbad
    change 2 * rademacherComplexity_without_abs n G P id + confidenceRadius 1 D δ n ≤
      oneSidedDeviation n G P id X
    linarith [lt_of_not_ge hbad]
  rw [probReal_compl_eq_one_sub E.toFinite.measurableSet] at hfail
  change 1 - δ ≤ (Measure.pi (fun _ : Fin n => P)).real E
  linarith

/-- Lemma 3's upper tail for a fixed comparator. A single draw changes the average
by at most the width of the range, `D / 2`, divided by the sample size. -/
theorem fixed_comparator_tail {S : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (P : Measure S) [IsProbabilityMeasure P]
    (f : S → ℝ) {n : ℕ} {D ε δ : ℝ} (hnpos : 0 < n) (hD : 0 ≤ D) (hε : 0 < ε)
    (hδ : 0 < δ) (hδ₁ : δ < 1) (hf : ∀ x, f x ∈ Set.Icc 0 (D / 2))
    (hn : (D * (1 + Real.sqrt (2 * Real.log (1 / δ)))) ^ 2 / ε ^ 2 ≤ n) :
    (Measure.pi (fun _ : Fin n => P)).real
      {X | ε ≤ (n : ℝ)⁻¹ * ∑ j, f (X j) - (∫ x, f x ∂P)} ≤ δ ^ 4 := by
  classical
  rcases hD.eq_or_lt with hzero | hD
  · subst D
    have hz (x : S) : f x = 0 := le_antisymm (by simpa using (hf x).2) (hf x).1
    simp [hz, hε.not_ge, pow_nonneg hδ.le]
  letI : Nonempty S := nonempty_of_isProbabilityMeasure P
  let avg (X : Fin n → S) := (n : ℝ)⁻¹ * ∑ j, f (X j)
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hnpos
  have hchange (i : Fin n) (X : Fin n → S) (x : S) :
      |avg X - avg (Function.update X i x)| ≤ (n : ℝ)⁻¹ * (D / 2) := by
    simp only [avg, ← mul_sub, ← Finset.sum_sub_distrib]
    rw [Finset.sum_eq_single i, Function.update_self, abs_mul, abs_of_pos (inv_pos.mpr hnR)]
    · apply mul_le_mul_of_nonneg_left _ (inv_pos.mpr hnR).le
      exact abs_le.mpr ⟨by linarith [(hf x).2, (hf (X i)).1], by linarith [(hf x).1, (hf (X i)).2]⟩
    · intro j _ hj
      simp [Function.update_of_ne hj]
    · simp
  have hmean : (∫ X, avg X ∂Measure.pi (fun _ : Fin n => P)) = ∫ x, f x ∂P := by
    unfold avg
    rw [integral_const_mul, integral_finsetSum _ fun _ _ => Integrable.of_finite]
    simp_rw [integral_comp_eval (μ := fun _ : Fin n => P)
      (f := f) (measurable_of_finite f).aestronglyMeasurable]
    simp [hnR.ne']
  have hcoef : (n : ℝ) / D ^ 2 * Fintype.card (Fin n) * ((n : ℝ)⁻¹ * (D / 2)) ^ 2 ≤ 1 := by
    simp only [Fintype.card_fin]
    field_simp
    nlinarith [sq_nonneg ((n : ℝ) * D)]
  have htail := mcdiarmid_inequality_pos_iid_of_const (μ := P) (X' := id) measurable_id
    hchange (measurable_of_finite avg) hε.le hcoef
  simp only [Function.id_comp, hmean] at htail
  refine htail.trans ?_
  rw [← Real.exp_log (pow_pos hδ 4), Real.exp_le_exp, Real.log_pow]
  have hlog : 0 ≤ 2 * Real.log (1 / δ) :=
    mul_nonneg (by norm_num) (Real.log_nonneg ((le_div_iff₀ hδ).mpr (by linarith)))
  have hscale : D ^ 2 * (2 * Real.log (1 / δ)) ≤ (n : ℝ) * ε ^ 2 := calc
    _ = (D * Real.sqrt (2 * Real.log (1 / δ))) ^ 2 := by rw [mul_pow, Real.sq_sqrt hlog]
    _ ≤ (D * (1 + Real.sqrt (2 * Real.log (1 / δ)))) ^ 2 := by gcongr; linarith
    _ ≤ _ := (div_le_iff₀ (sq_pos_of_pos hε)).mp hn
  rw [one_div, Real.log_inv] at hscale
  rw [← mul_div_assoc, div_le_iff₀ (sq_pos_of_pos hD)]
  norm_num
  linarith

end Kadp
