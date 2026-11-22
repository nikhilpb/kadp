import Kadp.SampledRSALP
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Kadp.SampledRSALP

variable {S A H : Type*} [Fintype S] [Fintype A] {N : ℕ}
  (D : SampledRSALP S A H N)

/-- The row caps and the prescribed total mass in (9) are compatible exactly
    at or above the threshold, including the case when every row is saturated. -/
theorem dualFeasible_iff_penalty [Nonempty A] :
    (∃ l, D.DualFeasible l) ↔ 1 / (1 - D.α) ≤ D.κ := by
  classical
  have hN : (0 : ℝ) < N := by exact_mod_cast D.sample_pos
  have htotal (x : ℝ) : (∑ _ : Fin N, x / (N : ℝ)) = x := by
    simp [nsmul_eq_mul]
    field_simp
  constructor
  · rintro ⟨l, _, hcap, hmass⟩
    rw [← hmass, ← htotal D.κ]
    exact Finset.sum_le_sum fun i _ => hcap i
  · intro hκ
    let a₀ : A := Classical.choice ‹Nonempty A›
    let mass := 1 / (1 - D.α)
    have hmass : 0 < mass := one_div_pos.mpr (sub_pos.mpr D.α_lt_one)
    let l := fun (_ : Fin N) (a : A) => if a = a₀ then mass / N else 0
    have hrow (i : Fin N) : ∑ a, l i a = mass / N := by simp [l]
    refine ⟨l, ?_, ?_, ?_⟩
    · intro i a
      dsimp [l]
      split <;> positivity
    · intro i
      rw [hrow i]
      exact div_le_div_of_nonneg_right hκ hN.le
    · simpa only [hrow] using (htotal mass : (∑ _ : Fin N, mass / (N : ℝ)) = mass)

variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [DecidableEq S]

noncomputable def meanFeature : H :=
  (N : ℝ)⁻¹ • ∑ i, D.weight (D.sample i) • D.feature (D.sample i)

/-- The coefficients q sum the feature at the draw minus its discounted successor feature. -/
noncomputable def featureDiff (i : Fin N) (a : A) : H :=
  ∑ y, D.q (D.sample i) y a • D.feature y

omit [Fintype A] in
theorem featureDiff_eq (i : Fin N) (a : A) :
    D.featureDiff i a = D.feature (D.sample i) -
      D.α • ∑ y, D.transition (D.sample i) a y • D.feature y := by
  classical
  simp [featureDiff, q, sub_smul, Finset.sum_sub_distrib, mul_smul,
    Finset.smul_sum, ite_smul]

noncomputable def multiplierFeature (l : Fin N → A → ℝ) : H :=
  ∑ i, ∑ a, l i a • D.featureDiff i a

/-- The Lagrange dual function on the feasible multipliers, in primal value units. -/
noncomputable def correctedDualObjective (l : Fin N → A → ℝ) : ℝ :=
  (∑ i, ∑ a, l i a * D.cost (D.sample i) a) +
    ‖D.meanFeature - D.multiplierFeature l‖ ^ 2 / (2 * D.Γ)

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [DecidableEq S] in
private theorem compact_dualFeasible :
    IsCompact {l : Fin N → A → ℝ | D.DualFeasible l} := by
  let upper : Fin N → A → ℝ := fun _ _ => D.κ / N
  apply (isCompact_Icc (α := Fin N → A → ℝ) (a := 0) (b := upper)).of_isClosed_subset
  · simp only [DualFeasible, Set.setOf_and, Set.setOf_forall]
    apply IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun a => isClosed_le (by fun_prop) (by fun_prop))
    exact IsClosed.inter (isClosed_iInter fun i => isClosed_le (by fun_prop) (by fun_prop))
      (isClosed_eq (by fun_prop) (by fun_prop))
  · intro l hl
    refine ⟨hl.1, fun i a => ?_⟩
    exact (Finset.single_le_sum (fun c _ => hl.1 i c) (Finset.mem_univ a)).trans (hl.2.1 i)

theorem exists_dual_minimizer [Nonempty A] (hκ : 1 / (1 - D.α) ≤ D.κ) :
    ∃ l, D.DualFeasible l ∧ ∀ t, D.DualFeasible t →
      D.correctedDualObjective l ≤ D.correctedDualObjective t := by
  have hcont : Continuous D.correctedDualObjective := by
    unfold correctedDualObjective multiplierFeature
    fun_prop
  exact D.compact_dualFeasible.exists_isMinOn ((D.dualFeasible_iff_penalty).mpr hκ)
    hcont.continuousOn

omit [Fintype A] in
theorem gramCoeff_inner (i : Fin N) (a : A) (j : Fin N) (c : A) :
    D.gramCoeff i a j c = inner ℝ (D.featureDiff i a) (D.featureDiff j c) := by
  simp only [gramCoeff, featureDiff, sum_inner, real_inner_smul_left]
  simp only [inner_sum, real_inner_smul_right, Finset.mul_sum, mul_assoc]

omit [Fintype A] in
private theorem linearCoeff_inner (i : Fin N) (a : A) :
    D.linearCoeff i a = D.Γ * D.cost (D.sample i) a -
      inner ℝ D.meanFeature (D.featureDiff i a) := by
  simp only [linearCoeff, meanFeature, featureDiff, real_inner_smul_left, sum_inner]
  simp only [inner_sum, real_inner_smul_right, Finset.mul_sum, mul_assoc, div_eq_inv_mul]
  simp_rw [real_inner_comm (D.feature (D.sample _))]

/-- The Gram quadratic form is the squared norm of the multiplier feature. -/
theorem gram_quadratic_eq_norm_sq (l : Fin N → A → ℝ) :
    (∑ i, ∑ a, ∑ j, ∑ c, l i a * D.gramCoeff i a j c * l j c) =
    ‖D.multiplierFeature l‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [multiplierFeature, sum_inner, inner_sum, real_inner_smul_left,
    real_inner_smul_right, gramCoeff_inner]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro c _
  rw [real_inner_comm (D.featureDiff i a) (D.featureDiff j c)]
  ring

theorem dualObjective_normalization (l : Fin N → A → ℝ) :
    D.dualObjective l = D.Γ * D.correctedDualObjective l + D.dualConstant -
      ‖D.meanFeature‖ ^ 2 / 2 := by
  have hlin : (∑ i, ∑ a, D.linearCoeff i a * l i a) =
      D.Γ * (∑ i, ∑ a, l i a * D.cost (D.sample i) a) -
      inner ℝ D.meanFeature (D.multiplierFeature l) := by
    simp only [linearCoeff_inner, multiplierFeature, inner_sum, real_inner_smul_right,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro a _
    ring
  rw [dualObjective, D.gram_quadratic_eq_norm_sq, hlin, correctedDualObjective, norm_sub_sq_real]
  field_simp [D.Γ_pos.ne']
  ring

noncomputable def recoveredWeight (l : Fin N → A → ℝ) : H :=
  D.Γ⁻¹ • (D.meanFeature - D.multiplierFeature l)

noncomputable def constraintMargin (z : H) (b : ℝ) (s : Fin N → ℝ) (i : Fin N) (a : A) : ℝ :=
  D.cost (D.sample i) a + s i - inner ℝ (D.featureDiff i a) z - (1 - D.α) * b

omit [Fintype A] in
theorem primalFeasible_iff_margins (z : H) (b : ℝ) (s : Fin N → ℝ) :
    D.PrimalFeasible z b s ↔ (∀ i, 0 ≤ s i) ∧ ∀ i a, 0 ≤ D.constraintMargin z b s i a := by
  unfold PrimalFeasible
  apply and_congr_right
  intro _
  apply forall_congr'
  intro i
  apply forall_congr'
  intro a
  simp only [value, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, D.transition_sum,
    one_mul, constraintMargin, featureDiff_eq, inner_sub_left, real_inner_smul_left, sum_inner]
  constructor <;> intro h <;> linarith

omit [Fintype A] [DecidableEq S] in
private theorem primalObjective_eq (z : H) (b : ℝ) (s : Fin N → ℝ) :
    D.primalObjective z b s =
      inner ℝ D.meanFeature z + b - D.κ / N * (∑ i, s i) - D.Γ / 2 * ‖z‖ ^ 2 := by
  simp only [primalObjective, meanFeature, real_inner_smul_left, sum_inner,
    real_inner_self_eq_norm_sq, div_eq_inv_mul]

/-- The exact primal-dual gap for (6) and the corrected objective. -/
theorem dualityGap (l : Fin N → A → ℝ) (hl : D.DualFeasible l)
    (z : H) (b : ℝ) (s : Fin N → ℝ) :
    D.correctedDualObjective l - D.primalObjective z b s =
      D.Γ / 2 * ‖z - D.recoveredWeight l‖ ^ 2 +
      (∑ i, ∑ a, l i a * D.constraintMargin z b s i a) +
      ∑ i, (D.κ / N - ∑ a, l i a) * s i := by
  have hmass : (1 - D.α) * (∑ i, ∑ a, l i a) = 1 := by
    rw [hl.2.2, one_div, mul_inv_cancel₀ (sub_pos.mpr D.α_lt_one).ne']
  have hmass_b : (∑ i, ∑ a, l i a) * ((1 - D.α) * b) = b := by
    linear_combination b * hmass
  have hmargin :
      (∑ i, ∑ a, l i a * D.constraintMargin z b s i a) +
          (∑ i, (D.κ / N - ∑ a, l i a) * s i) =
      (∑ i, ∑ a, l i a * D.cost (D.sample i) a) +
        D.κ / N * (∑ i, s i) - inner ℝ (D.multiplierFeature l) z - b := by
    simp only [constraintMargin, mul_sub, mul_add, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, ← Finset.sum_mul, sub_mul, ← Finset.mul_sum,
      multiplierFeature, sum_inner, real_inner_smul_left]
    linear_combination -hmass_b
  rw [add_assoc, hmargin, correctedDualObjective, primalObjective_eq]
  have hsq : ‖z - D.recoveredWeight l‖ ^ 2 =
      ‖z‖ ^ 2 - 2 * D.Γ⁻¹ * inner ℝ (D.meanFeature - D.multiplierFeature l) z +
      (D.Γ⁻¹) ^ 2 * ‖D.meanFeature - D.multiplierFeature l‖ ^ 2 := by
    rw [norm_sub_sq_real, recoveredWeight, real_inner_smul_right, norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr D.Γ_pos), mul_pow, real_inner_comm z]
    ring
  rw [hsq, inner_sub_left]
  field_simp [D.Γ_pos.ne']
  ring

theorem weightError_le_gap {z : H} {b : ℝ} {s : Fin N → ℝ} {l : Fin N → A → ℝ}
    (hp : D.PrimalFeasible z b s) (hd : D.DualFeasible l) :
    D.Γ / 2 * ‖z - D.recoveredWeight l‖ ^ 2 ≤
      D.correctedDualObjective l - D.primalObjective z b s := by
  rw [D.dualityGap l hd]
  exact le_add_of_le_of_nonneg (le_add_of_nonneg_right
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun a _ =>
      mul_nonneg (hd.1 i a) (((D.primalFeasible_iff_margins z b s).mp hp).2 i a)))
    (Finset.sum_nonneg fun i _ => mul_nonneg (sub_nonneg.mpr (hd.2.1 i)) (hp.1 i))

theorem weakDuality {z : H} {b : ℝ} {s : Fin N → ℝ} {l : Fin N → A → ℝ}
    (hp : D.PrimalFeasible z b s) (hd : D.DualFeasible l) :
    D.primalObjective z b s ≤ D.correctedDualObjective l :=
  sub_nonneg.mp ((mul_nonneg (by linarith [D.Γ_pos]) (sq_nonneg _)).trans
    (D.weightError_le_gap hp hd))

theorem recoveredWeight_of_equal_values {z : H} {b : ℝ} {s : Fin N → ℝ} {l : Fin N → A → ℝ}
    (hp : D.PrimalFeasible z b s) (hd : D.DualFeasible l)
    (heq : D.correctedDualObjective l = D.primalObjective z b s) :
    z = D.recoveredWeight l := by
  have h := D.weightError_le_gap hp hd
  rw [heq, sub_self] at h
  by_contra hn
  exact (not_lt_of_ge h) (mul_pos (by linarith [D.Γ_pos])
    (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hn))))

omit [DecidableEq S] in
/-- Below the cap threshold the intercept and all slacks can grow together,
    giving unbounded primal values for every sampled problem. -/
theorem primal_unbounded_of_penalty_lt (hκ : D.κ < 1 / (1 - D.α)) :
    ¬ BddAbove D.primalValues := by
  classical
  have hα := sub_pos.mpr D.α_lt_one
  have hslope : 0 < 1 - D.κ * (1 - D.α) :=
    sub_pos.mpr ((lt_div_iff₀ hα).mp hκ)
  have hN : (0 : ℝ) < N := by exact_mod_cast D.sample_pos
  obtain ⟨K, hK⟩ := (Set.finite_range fun p : Fin N × A =>
    -D.cost (D.sample p.1) p.2).bddAbove
  let C := max K 0
  have hC : 0 ≤ C := le_max_right _ _
  have hcost (i : Fin N) (a : A) : -D.cost (D.sample i) a ≤ C :=
    le_trans (hK ⟨(i, a), rfl⟩) (le_max_left _ _)
  rintro ⟨M, hM⟩
  let b := (max M 0 + D.κ * C + 1) / (1 - D.κ * (1 - D.α))
  have hb : 0 ≤ b := by
    exact div_nonneg (by linarith [le_max_right M 0, mul_nonneg D.κ_pos.le hC]) hslope.le
  let s := (1 - D.α) * b + C
  have hf : D.PrimalFeasible 0 b (fun _ => s) := by
    constructor
    · exact fun _ => add_nonneg (mul_nonneg hα.le hb) hC
    · intro i a
      simp [value, ← Finset.sum_mul, D.transition_sum]
      dsimp [s]
      linarith [hcost i a]
  have hbound := hM (show D.primalObjective 0 b (fun _ => s) ∈ D.primalValues from
    ⟨0, b, _, hf, rfl⟩)
  have hobj : D.primalObjective 0 b (fun _ => s) = b - D.κ * s := by
    simp [primalObjective, nsmul_eq_mul]
    field_simp
  rw [hobj] at hbound
  have hid : b * (1 - D.κ * (1 - D.α)) = max M 0 + D.κ * C + 1 :=
    div_mul_cancel₀ _ hslope.ne'
  dsimp [s] at hbound
  linarith [le_max_left M 0]

end Kadp.SampledRSALP
