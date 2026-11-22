import FoML.ToFoML.Contraction

/-! Fixed-sample complexity of the affine, fixed-policy residual in Lemma 2
and Corollary 1. FoML normalizes each signed sum by `1/n`. -/

namespace Kadp

open FoML.ToFoML
open scoped BigOperators

variable {S H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [Nonempty ι] {n : ℕ}

private theorem empirical_add_le (f h : ι → S → ℝ) (X : Fin n → S)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hf : ∀ i k, |f i (X k)| ≤ a) (hh : ∀ i k, |h i (X k)| ≤ b) :
    empiricalRademacherComplexity_without_abs n (fun i x => f i x + h i x) X ≤
      empiricalRademacherComplexity_without_abs n f X +
      empiricalRademacherComplexity_without_abs n h X := by
  unfold empiricalRademacherComplexity_without_abs
  rw [← mul_add, ← Finset.sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro σ _
  simp only [mul_add, Finset.sum_add_distrib]
  apply ciSup_add_le_add_ciSup
  · exact bddAbove_range_normalizedRademacherSum_of_bound id (fun _ => Or.inr rfl)
      f X ha hf σ
  · exact bddAbove_range_normalizedRademacherSum_of_bound id (fun _ => Or.inr rfl)
      h X hb hh σ

/-- Dimension-free linear complexity (Lemma 2), for any indexing of the
admissible weights and any feature map bounded by `L`. -/
theorem empirical_linear_le (hn : 0 < n) (D : S → H) (w : ι → H)
    (X : Fin n → S) {L C : ℝ} (hD : ∀ x, ‖D x‖ ≤ L) (hw : ∀ i, ‖w i‖ ≤ C) :
    empiricalRademacherComplexity_without_abs n (fun i x => inner ℝ (D x) (w i)) X ≤
      C * L / Real.sqrt n := by
  have hL := (norm_nonneg _).trans (hD (X ⟨0, hn⟩))
  have hC := (norm_nonneg _).trans (hw (Classical.arbitrary ι))
  let W (i : ι) : Metric.closedBall (0 : H) C := ⟨w i, mem_closedBall_zero_iff.mpr (hw i)⟩
  let F := rkhsPredictor (Λ := C) D
  have hF (u : Metric.closedBall (0 : H) C) (x : S) : |F u x| ≤ C * L :=
    (abs_hilbertPredictor_le u (D x)).trans (mul_le_mul_of_nonneg_left (hD x) hC)
  have heq (i : ι) (x : S) : inner ℝ (D x) (w i) = F (W i) x :=
    real_inner_comm _ _
  simp_rw [heq]
  calc
    _ ≤ empiricalRademacherComplexity n (fun i => F (W i)) X :=
      empiricalRademacherComplexity_without_abs_le_empiricalRademacherComplexity
        n _ X _ (mul_nonneg hC hL) (fun i k => hF (W i) (X k))
    _ ≤ empiricalRademacherComplexity n F X :=
      empiricalRademacherComplexity_reindex_le F W X (mul_nonneg hC hL) hF
    _ ≤ C * (n : ℝ)⁻¹ * Real.sqrt (∑ k, ‖D (X k)‖ ^ 2) :=
      hilbertPredictor_empiricalRademacherComplexity_le C hC (D ∘ X)
    _ ≤ C * (n : ℝ)⁻¹ * Real.sqrt (∑ _ : Fin n, L ^ 2) := by
      gcongr with k
      exact hD (X k)
    _ = C * L / Real.sqrt n := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq hL]
      have hs : Real.sqrt (n : ℝ) ≠ 0 := by positivity
      field_simp [hs]
      rw [Real.sq_sqrt (Nat.cast_nonneg n)]

private theorem empirical_affine_contraction_le (hn : 0 < n) (D : S → H) (w : ι → H)
    (c : ι → ℝ) (ψ : S → ℝ → ℝ) (X : Fin n → S) {L C b : ℝ}
    (hD : ∀ x, ‖D x‖ ≤ L) (hw : ∀ i, ‖w i‖ ≤ C) (hc : ∀ i, |c i| ≤ b)
    (hψ : ∀ x u v, |ψ x u - ψ x v| ≤ |u - v|) :
    empiricalRademacherComplexity_without_abs n
      (fun i x => ψ x (inner ℝ (D x) (w i) + c i)) X ≤
      (C * L + b) / Real.sqrt n := by
  have hL := (norm_nonneg _).trans (hD (X ⟨0, hn⟩))
  have hC := (norm_nonneg _).trans (hw (Classical.arbitrary ι))
  have hb := (abs_nonneg _).trans (hc (Classical.arbitrary ι))
  let f (i : ι) (x : S) := inner ℝ (D x) (w i)
  have hf (i : ι) (k : Fin n) : |f i (X k)| ≤ C * L := by
    rw [mul_comm]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul (hD _) (hw _) (norm_nonneg _) hL)
  have hcontr := empiricalRademacherComplexity_without_abs_contraction n
    (fun i x => f i x + c i) ψ X zero_le_one (add_nonneg (mul_nonneg hC hL) hb)
    (fun i k => (abs_add_le _ _).trans (add_le_add (hf i k) (hc i))) (by simpa using hψ)
  have hoffset := empirical_linear_le hn (fun _ : S => (1 : ℝ)) c X
    (L := 1) (C := b) (by simp) (by simpa [Real.norm_eq_abs] using hc)
  calc
    _ ≤ empiricalRademacherComplexity_without_abs n (fun i x => f i x + c i) X := by
      simpa only [one_mul] using hcontr
    _ ≤ empiricalRademacherComplexity_without_abs n f X +
        empiricalRademacherComplexity_without_abs n (fun i _ => c i) X :=
      empirical_add_le f (fun i _ => c i) X (mul_nonneg hC hL) hb hf (fun i _ => hc i)
    _ ≤ C * L / Real.sqrt n + b / Real.sqrt n := by
      apply add_le_add (empirical_linear_le hn D w X hD hw)
      simpa [Real.inner_apply] using hoffset
    _ = _ := (add_div _ _ _).symm

/-- Empirical form of Corollary 1 for the positive-part residual. The shared
cost enters the state-dependent contraction and needs no bound here. -/
theorem empirical_residual_le (hn : 0 < n) (D : S → H) (w : ι → H)
    (c : ι → ℝ) (g : S → ℝ) (X : Fin n → S) {L C b : ℝ}
    (hD : ∀ x, ‖D x‖ ≤ L) (hw : ∀ i, ‖w i‖ ≤ C) (hc : ∀ i, |c i| ≤ b) :
    empiricalRademacherComplexity_without_abs n
      (fun i x => max (inner ℝ (D x) (w i) + c i - g x) 0) X ≤
      (C * L + b) / Real.sqrt n := by
  apply empirical_affine_contraction_le hn D w c (fun x u => max (u - g x) 0) X hD hw hc
  intro x u v
  simpa only [sub_sub_sub_cancel_right] using abs_max_sub_max_le_abs (u - g x) (v - g x) 0

/-- The negated residual is the orientation used for the population-minus-
empirical deviation in Theorem 3. -/
theorem empirical_negative_residual_le (hn : 0 < n) (D : S → H) (w : ι → H)
    (c : ι → ℝ) (g : S → ℝ) (X : Fin n → S) {L C b : ℝ}
    (hD : ∀ x, ‖D x‖ ≤ L) (hw : ∀ i, ‖w i‖ ≤ C) (hc : ∀ i, |c i| ≤ b) :
    empiricalRademacherComplexity_without_abs n
      (fun i x => -max (inner ℝ (D x) (w i) + c i - g x) 0) X ≤
      (C * L + b) / Real.sqrt n := by
  apply empirical_affine_contraction_le hn D w c (fun x u => -max (u - g x) 0) X hD hw hc
  intro x u v
  rw [show -max (u - g x) 0 - -max (v - g x) 0 =
    -(max (u - g x) 0 - max (v - g x) 0) by ring, abs_neg]
  simpa only [sub_sub_sub_cancel_right] using abs_max_sub_max_le_abs (u - g x) (v - g x) 0

end Kadp
