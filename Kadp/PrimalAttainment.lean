import Kadp.Allocation
import Kadp.Duality
import Mathlib.Tactic.Module

/-! Strong duality and primal recovery for the corrected sampled program. -/

namespace Kadp.SampledRSALP

variable {S A H : Type*} [Fintype S] [Fintype A] {N : ℕ}
  (D : SampledRSALP S A H N)

private def mix (l k : Fin N → A → ℝ) (t : ℝ) :=
  fun i a => (1 - t) * l i a + t * k i a

private theorem dualFeasible_mix {l k : Fin N → A → ℝ} (hl : D.DualFeasible l)
    (hk : D.DualFeasible k) {t : ℝ} (ht : 0 ≤ t) (ht₁ : t ≤ 1) :
    D.DualFeasible (mix l k t) := by
  have hrow (i : Fin N) : ∑ a, mix l k t i a = (1 - t) * (∑ a, l i a) + t * ∑ a, k i a := by
    simp only [mix, Finset.sum_add_distrib, Finset.mul_sum]
  refine ⟨fun i a => add_nonneg (mul_nonneg (sub_nonneg.mpr ht₁) (hl.1 i a))
    (mul_nonneg ht (hk.1 i a)), ?_, ?_⟩
  · intro i
    rw [hrow]
    calc
      _ ≤ (1 - t) * (D.κ / N) + t * (D.κ / N) := add_le_add
        (mul_le_mul_of_nonneg_left (hl.2.1 i) (sub_nonneg.mpr ht₁))
        (mul_le_mul_of_nonneg_left (hk.2.1 i) ht)
      _ = _ := by ring
  · simp only [hrow, Finset.sum_add_distrib, ← Finset.mul_sum, hl.2.2, hk.2.2]
    ring

private noncomputable def linearCost (c l : Fin N → A → ℝ) : ℝ := ∑ i, ∑ a, l i a * c i a

private theorem linearCost_mix (c l k : Fin N → A → ℝ) (t : ℝ) :
    linearCost c (mix l k t) = (1 - t) * linearCost c l + t * linearCost c k := by
  simp only [linearCost, mix, add_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]

variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [DecidableEq S]

private noncomputable def reducedCost (z : H) (i : Fin N) (a : A) : ℝ :=
  D.cost (D.sample i) a - inner ℝ (D.featureDiff i a) z

private theorem gap_at_zero_offset (l : Fin N → A → ℝ) (hl : D.DualFeasible l) (z : H) :
    D.correctedDualObjective l - D.primalObjective z 0 (fun _ => 0) =
      D.Γ / 2 * ‖z - D.recoveredWeight l‖ ^ 2 + linearCost (D.reducedCost z) l := by
  simpa [constraintMargin, reducedCost, linearCost] using D.dualityGap l hl z 0 (fun _ => 0)

private theorem recoveredWeight_mix_sub (l k : Fin N → A → ℝ) (t : ℝ) :
    D.recoveredWeight l - D.recoveredWeight (mix l k t) =
      t • (D.recoveredWeight l - D.recoveredWeight k) := by
  have hf : D.multiplierFeature (mix l k t) =
      (1 - t) • D.multiplierFeature l + t • D.multiplierFeature k := by
    simp only [multiplierFeature, mix, add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]
  simp only [recoveredWeight, hf]
  module

/-- Optimality on each feasible segment implies optimality for the linear cost
    obtained at its starting point. The quadratic remainder is exact. -/
private theorem linearCost_minimal {l : Fin N → A → ℝ} (hl : D.DualFeasible l)
    (hmin : ∀ k, D.DualFeasible k → D.correctedDualObjective l ≤ D.correctedDualObjective k)
    (k : Fin N → A → ℝ) (hk : D.DualFeasible k) :
    linearCost (D.reducedCost (D.recoveredWeight l)) l ≤
      linearCost (D.reducedCost (D.recoveredWeight l)) k := by
  let z := D.recoveredWeight l
  let c := D.reducedCost z
  let B := D.Γ / 2 * ‖z - D.recoveredWeight k‖ ^ 2
  have hB : 0 ≤ B := mul_nonneg (by linarith [D.Γ_pos]) (sq_nonneg _)
  change linearCost c l ≤ linearCost c k
  by_contra! h
  obtain ⟨d, hd, hsmall⟩ := exists_pos_mul_lt (sub_pos.mpr h) B
  let t := min d 1
  have ht : 0 < t := lt_min hd zero_lt_one
  have hBt := lt_of_le_of_lt (mul_le_mul_of_nonneg_left (min_le_left d 1) hB) hsmall
  have hneg : t * (B * t + linearCost c k - linearCost c l) < 0 :=
    mul_neg_of_pos_of_neg ht (by change B * t < _ at hBt; linarith)
  have hmix := D.dualFeasible_mix hl hk ht.le (min_le_right d 1)
  have horigin : D.correctedDualObjective l - D.primalObjective z 0 (fun _ => 0) =
      linearCost c l := by simpa [z, c] using D.gap_at_zero_offset l hl z
  have hsegment : D.correctedDualObjective (mix l k t) - D.primalObjective z 0 (fun _ => 0) =
      B * t ^ 2 + ((1 - t) * linearCost c l + t * linearCost c k) := by
    rw [D.gap_at_zero_offset _ hmix, linearCost_mix]
    dsimp only [B, c, z]
    rw [D.recoveredWeight_mix_sub, norm_smul, Real.norm_eq_abs, abs_of_pos ht, mul_pow]
    ring
  nlinarith only [hneg, horigin, hsegment, hmin _ hmix]

/-- Every dual minimizer determines an optimal weight and admits an intercept
    and slacks attaining the same objective. -/
theorem primal_attains_of_dual_minimizer [Nonempty A] {l : Fin N → A → ℝ}
    (hl : D.DualFeasible l)
    (hmin : ∀ k, D.DualFeasible k → D.correctedDualObjective l ≤ D.correctedDualObjective k) :
    ∃ b s, D.PrimalFeasible (D.recoveredWeight l) b s ∧
      D.primalObjective (D.recoveredWeight l) b s = D.correctedDualObjective l := by
  letI : Nonempty (Fin N) := ⟨⟨0, D.sample_pos⟩⟩
  have hN : (0 : ℝ) < N := by exact_mod_cast D.sample_pos
  have hα := sub_pos.mpr D.α_lt_one
  let z := D.recoveredWeight l
  let c := D.reducedCost z
  let q := D.κ / N
  let M := 1 / (1 - D.α)
  have hcap : M ≤ Fintype.card (Fin N) * q := by
    calc
      M ≤ D.κ := D.dualFeasible_iff_penalty.mp ⟨l, hl⟩
      _ = _ := by simp only [Fintype.card_fin, q]; field_simp [hN.ne']
  obtain ⟨u, s, k, hs, hu, hk₀, hkcap, hkmass, hkcost⟩ :=
    exists_cutoff_allocation c (div_nonneg D.κ_pos.le hN.le) (one_div_pos.mpr hα) hcap
  have hk : D.DualFeasible k := ⟨hk₀, hkcap, hkmass⟩
  let b := u / (1 - D.α)
  have hb : (1 - D.α) * b = u := by dsimp [b]; field_simp [hα.ne']
  have hp : D.PrimalFeasible z b s := by
    apply (D.primalFeasible_iff_margins z b s).mpr
    refine ⟨hs, fun i a => ?_⟩
    have hi := hu i a
    dsimp [c, reducedCost] at hi
    rw [constraintMargin, hb]
    linarith
  refine ⟨b, s, hp, le_antisymm (D.weakDuality hp hl) ?_⟩
  have hlinear : linearCost c l ≤ u * M - q * ∑ i, s i := by
    exact (D.linearCost_minimal hl hmin k hk).trans_eq hkcost
  have hgap : D.correctedDualObjective l - D.primalObjective z 0 (fun _ => 0) =
      linearCost c l := by simpa [z, c] using D.gap_at_zero_offset l hl z
  have hoffset : D.primalObjective z b s =
      D.primalObjective z 0 (fun _ => 0) + b - q * ∑ i, s i := by
    simp [primalObjective, q]
    ring
  rw [show u * M = b by simp [M, b, div_eq_mul_inv]] at hlinear
  change D.correctedDualObjective l ≤ D.primalObjective z b s
  linarith

def correctedDualValues : Set ℝ :=
  {v | ∃ l, D.DualFeasible l ∧ D.correctedDualObjective l = v}

/-- The affine change of units in printed (9) preserves all comparisons. -/
theorem dualObjective_le_iff (l k : Fin N → A → ℝ) :
    D.dualObjective l ≤ D.dualObjective k ↔ D.correctedDualObjective l ≤ D.correctedDualObjective k := by
  rw [D.dualObjective_normalization l, D.dualObjective_normalization k]
  simp only [sub_le_sub_iff_right, add_le_add_iff_right, mul_le_mul_iff_right₀ D.Γ_pos]

/-- A minimizer returned by the printed QP recovers a feasible primal point
    at the corrected value. -/
theorem primal_attains_of_printed_dual_minimizer [Nonempty A] {l : Fin N → A → ℝ}
    (hl : D.DualFeasible l) (hmin : ∀ k, D.DualFeasible k → D.dualObjective l ≤ D.dualObjective k) :
    ∃ b s, D.PrimalFeasible (D.recoveredWeight l) b s ∧
      D.primalObjective (D.recoveredWeight l) b s = D.correctedDualObjective l :=
  D.primal_attains_of_dual_minimizer hl fun k hk => (D.dualObjective_le_iff l k).mp (hmin k hk)

/-- Strong duality under the sharp penalty hypothesis, including equality.
    Every optimal primal/dual pair satisfies the weight formula (10). -/
theorem strongDuality [Nonempty A] (hκ : 1 / (1 - D.α) ≤ D.κ) :
    ∃ v : ℝ, IsGreatest D.primalValues v ∧ IsLeast D.correctedDualValues v ∧
      ∀ z b s l, D.PrimalFeasible z b s → D.primalObjective z b s = v →
        D.DualFeasible l → D.correctedDualObjective l = v → z = D.recoveredWeight l := by
  obtain ⟨l, hl, hmin⟩ := D.exists_dual_minimizer hκ
  obtain ⟨b, s, hp, heq⟩ := D.primal_attains_of_dual_minimizer hl hmin
  refine ⟨D.correctedDualObjective l, ⟨⟨_, b, s, hp, heq⟩, ?_⟩, ⟨⟨l, hl, rfl⟩, ?_⟩, ?_⟩
  · rintro _ ⟨z', b', s', hp', rfl⟩
    exact D.weakDuality hp' hl
  · rintro _ ⟨k, hk, rfl⟩
    exact hmin k hk
  · intro z' b' s' k hp' hv hk hkv
    exact D.recoveredWeight_of_equal_values hp' hk (hkv.trans hv.symm)

/-- The full classification, combining strong duality with the behavior below the threshold. -/
theorem correctedProposition1 [Nonempty A] :
    (D.κ < 1 / (1 - D.α) → ¬ BddAbove D.primalValues ∧ ¬ ∃ l, D.DualFeasible l) ∧
    (1 / (1 - D.α) ≤ D.κ → ∃ v : ℝ,
      IsGreatest D.primalValues v ∧ IsLeast D.correctedDualValues v ∧
      ∀ z b s l, D.PrimalFeasible z b s → D.primalObjective z b s = v →
        D.DualFeasible l → D.correctedDualObjective l = v → z = D.recoveredWeight l) := by
  constructor
  · intro hκ
    exact ⟨D.primal_unbounded_of_penalty_lt hκ, fun h => hκ.not_ge (D.dualFeasible_iff_penalty.mp h)⟩
  · exact D.strongDuality

end Kadp.SampledRSALP
