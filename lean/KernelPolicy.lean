import PrimalAttainment

/-! Kernel evaluation, the coefficients of the sampled QP, and all greedy actions. -/

namespace Kadp.SampledRSALP

variable {S A H : Type*} [Fintype S] [Fintype A] {N : ℕ} (D : SampledRSALP S A H N)

/-- The support used in (7), (8), (12) and (13) includes the current state. -/
noncomputable def neighborhood (x : S) (a : A) : Finset S := by
  classical
  exact Finset.univ.filter fun y => x = y ∨ 0 < D.transition x a y

variable [DecidableEq S]

omit [Fintype A] in
private theorem sum_neighborhood_eq (x : S) (a : A) (f : S → ℝ)
    (hf : ∀ y, D.q x y a = 0 → f y = 0) :
    ∑ y ∈ D.neighborhood x a, f y = ∑ y, f y := by
  apply Finset.sum_subset (Finset.subset_univ _)
  intro y _ hy
  simp [neighborhood] at hy
  exact hf y (by simp [q, hy.1, le_antisymm hy.2 (D.transition_nonneg x a y)])

/-- Equation (12), evaluated using only the kernel and the two neighborhoods. -/
noncomputable def kernelGram (K : S → S → ℝ) (i : Fin N) (a : A) (j : Fin N) (c : A) : ℝ :=
  ∑ y ∈ D.neighborhood (D.sample i) a, ∑ y' ∈ D.neighborhood (D.sample j) c,
    D.q (D.sample i) y a * D.q (D.sample j) y' c * K y y'

/-- Equation (13). The importance weight belongs to the sampled draw j. -/
noncomputable def kernelLinear (K : S → S → ℝ) (i : Fin N) (a : A) : ℝ :=
  D.Γ * D.cost (D.sample i) a -
    (∑ j, ∑ y ∈ D.neighborhood (D.sample i) a,
      D.weight (D.sample j) * D.q (D.sample i) y a * K (D.sample j) y) / N

/-- The quadratic objective used by the algorithm with its additive constant set to zero. -/
noncomputable def kernelObjective (K : S → S → ℝ) (l : Fin N → A → ℝ) : ℝ :=
  (∑ i, ∑ a, ∑ j, ∑ c, l i a * D.kernelGram K i a j c * l j c) / 2 +
  ∑ i, ∑ a, D.kernelLinear K i a * l i a

/-- Equation (14), evaluated at an arbitrary query x. -/
noncomputable def kernelValue (K : S → S → ℝ) (l : Fin N → A → ℝ) (x : S) : ℝ :=
  ((∑ i, D.weight (D.sample i) * K x (D.sample i)) / N -
    ∑ i, ∑ a, l i a * (K x (D.sample i) -
      D.α * ∑ y, D.transition (D.sample i) a y * K y x)) / D.Γ

noncomputable def actionScore (J : S → ℝ) (x : S) (a : A) : ℝ :=
  D.cost x a + D.α * ∑ y, D.transition x a y * J y

/-- Greedy actions minimize one-step cost, including all ties. -/
def greedyActions (J : S → ℝ) (x : S) : Set A :=
  {a | ∀ c, D.actionScore J x a ≤ D.actionScore J x c}

omit [Fintype A] [DecidableEq S] in
theorem actionScore_add_const (J : S → ℝ) (b : ℝ) (x : S) (a : A) :
    D.actionScore (fun y => J y + b) x a = D.actionScore J x a + D.α * b := by
  simp only [actionScore, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
    D.transition_sum, one_mul, add_assoc]

omit [Fintype A] [DecidableEq S] in
theorem greedyActions_add_const (J : S → ℝ) (b : ℝ) (x : S) :
    D.greedyActions (fun y => J y + b) x = D.greedyActions J x := by
  ext a
  simp [greedyActions, D.actionScore_add_const]

variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {K : S → S → ℝ} (hK : ∀ x y, K x y = inner ℝ (D.feature x) (D.feature y))

include hK

omit [Fintype A] in
theorem kernelGram_eq (i : Fin N) (a : A) (j : Fin N) (c : A) :
    D.kernelGram K i a j c = D.gramCoeff i a j c := by
  unfold kernelGram gramCoeff
  simp only [hK]
  have hinner (y : S) := D.sum_neighborhood_eq (D.sample j) c
    (fun y' => D.q (D.sample i) y a * D.q (D.sample j) y' c * inner ℝ (D.feature y) (D.feature y'))
    (fun y' h => by simp [h])
  simp_rw [hinner]
  exact D.sum_neighborhood_eq _ _ _ fun y h => by simp [h]

omit [Fintype A] in
theorem kernelLinear_eq (i : Fin N) (a : A) :
    D.kernelLinear K i a = D.linearCoeff i a := by
  unfold kernelLinear linearCoeff
  simp only [hK]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  apply Eq.trans (D.sum_neighborhood_eq _ _ _ (fun y h => by simp [h]))
  apply Finset.sum_congr rfl
  intro y _
  rw [real_inner_comm (D.feature y) (D.feature (D.sample j))]

/-- Symmetry and nonnegativity of the quadratic form, also for singular kernels. -/
theorem kernelGram_psd :
    (∀ i a j c, D.kernelGram K i a j c = D.kernelGram K j c i a) ∧
    ∀ t : Fin N → A → ℝ,
      0 ≤ ∑ i, ∑ a, ∑ j, ∑ c, t i a * D.kernelGram K i a j c * t j c := by
  simp only [D.kernelGram_eq hK]
  constructor
  · intro i a j c
    simp only [D.gramCoeff_inner]
    exact real_inner_comm _ _
  · intro t
    rw [D.gram_quadratic_eq_norm_sq]
    exact sq_nonneg _

theorem kernelObjective_add_constant (l : Fin N → A → ℝ) :
    D.kernelObjective K l + D.dualConstant = D.dualObjective l := by
  simp only [kernelObjective, dualObjective, D.kernelGram_eq hK, D.kernelLinear_eq hK]

theorem kernelObjective_normalization (l : Fin N → A → ℝ) :
    D.kernelObjective K l = D.Γ * D.correctedDualObjective l - ‖D.meanFeature‖ ^ 2 / 2 := by
  linarith [D.kernelObjective_add_constant hK l, D.dualObjective_normalization l]

theorem exists_kernel_minimizer [Nonempty A] (hκ : 1 / (1 - D.α) ≤ D.κ) :
    ∃ l, D.DualFeasible l ∧ ∀ k, D.DualFeasible k →
      D.kernelObjective K l ≤ D.kernelObjective K k := by
  obtain ⟨l, hl, hmin⟩ := D.exists_dual_minimizer hκ
  refine ⟨l, hl, fun k hk => ?_⟩
  simp only [D.kernelObjective_normalization hK, sub_le_sub_iff_right]
  exact mul_le_mul_of_nonneg_left (hmin k hk) D.Γ_pos.le

/-- Equations (11) and (14). Restoring the intercept recovers the entire fitted value. -/
theorem value_recovered_eq_kernel (l : Fin N → A → ℝ) (b : ℝ) (x : S) :
    D.value (D.recoveredWeight l) b x = D.kernelValue K l x + b := by
  have hdiff (i : Fin N) (a : A) : inner ℝ (D.feature x) (D.featureDiff i a) =
      K x (D.sample i) - D.α * ∑ y, D.transition (D.sample i) a y * K y x := by
    simp only [D.featureDiff_eq, inner_sub_right, real_inner_smul_right, inner_sum, hK]
    congr 2
    apply Finset.sum_congr rfl
    intro y _
    rw [real_inner_comm (D.feature x) (D.feature y)]
  simp only [value, recoveredWeight, real_inner_smul_right, inner_sub_right, multiplierFeature,
    inner_sum, hdiff, meanFeature, kernelValue, ← hK, div_eq_inv_mul]

/-- Any optimal primal fit and any optimizer of the actual kernel QP give the same
    greedy action set at every state. The QP omits the printed additive constant. -/
theorem kernelPolicy_of_optima [Nonempty A] {l : Fin N → A → ℝ} {z : H} {b : ℝ} {s : Fin N → ℝ}
    (hl : D.DualFeasible l)
    (hmin : ∀ k, D.DualFeasible k → D.kernelObjective K l ≤ D.kernelObjective K k)
    (hp : D.PrimalFeasible z b s) (hmax : IsGreatest D.primalValues (D.primalObjective z b s)) :
    (∀ x, D.value z b x = D.kernelValue K l x + b) ∧
    ∀ x, D.greedyActions (D.value z b) x = D.greedyActions (D.kernelValue K l) x := by
  have hprinted (k) (hk : D.DualFeasible k) : D.dualObjective l ≤ D.dualObjective k := by
    rw [← D.kernelObjective_add_constant hK l, ← D.kernelObjective_add_constant hK k]
    exact add_le_add (hmin k hk) le_rfl
  obtain ⟨b', s', hp', heq⟩ := D.primal_attains_of_printed_dual_minimizer hl hprinted
  have hupper := hmax.2 (show D.correctedDualObjective l ∈ D.primalValues from
    ⟨_, b', s', hp', heq⟩)
  have hz := D.recoveredWeight_of_equal_values hp hl (le_antisymm hupper (D.weakDuality hp hl))
  rw [hz]
  refine ⟨D.value_recovered_eq_kernel hK l b, fun x => ?_⟩
  rw [funext (D.value_recovered_eq_kernel hK l b)]
  exact D.greedyActions_add_const _ _ _

end Kadp.SampledRSALP
