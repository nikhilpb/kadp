import SamplingLaw

/-! A finite-state coupling for the empirical total-variation continuity sentence in
Appendix B.3. Every coordinate puts the common mass on the diagonal. Independent
pairs give the specified iid marginal samples and an exact agreement probability. -/

namespace Kadp.SamplingCoupling

open MeasureTheory SargentStachurski.MarkovDecisionProcesses
open Kadp.Idealized Kadp.SamplingLaw

variable {S : Type*} [Fintype S]

private theorem tv_symm (π ρ : S → ℝ) : totalVariation π ρ = totalVariation ρ π := by
  simp only [totalVariation, abs_sub_comm (π _) (ρ _)]

private theorem sum_min (π ρ : S → ℝ) (hπ : IsDistribution π) (hρ : IsDistribution ρ) :
    ∑ x, min (π x) (ρ x) = 1 - totalVariation π ρ := by
  have he (x) : π x + ρ x - |π x - ρ x| = 2 * min (π x) (ρ x) := by
    rcases le_total (π x) (ρ x) with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]; ring
  have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun x _ => he x)
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hπ.sum_eq_one, hρ.sum_eq_one,
    ← Finset.mul_sum] at hs
  unfold totalVariation
  linarith

/-- Place the common mass on the diagonal. Pair the residual masses independently,
dividing their product by their (common) total mass. At distance zero the residual
term vanishes under Lean's convention for real division by zero. -/
noncomputable def joint [DecidableEq S] (π ρ : S → ℝ) (z : S × S) : ℝ :=
  (if z.2 = z.1 then min (π z.1) (ρ z.1) else 0) +
  (π z.1 - min (π z.1) (ρ z.1)) * (ρ z.2 - min (π z.2) (ρ z.2)) / totalVariation π ρ

variable [DecidableEq S] (π ρ : S → ℝ) (hπ : IsDistribution π) (hρ : IsDistribution ρ)

private theorem joint_swap (x y : S) : joint π ρ (x,y) = joint ρ π (y,x) := by
  unfold joint
  rw [tv_symm π ρ]
  by_cases h : x = y
  · subst y; simp [min_comm, mul_comm]
  · simp [h, Ne.symm h, min_comm, mul_comm]

include hπ hρ

theorem joint_row (x : S) : ∑ y, joint π ρ (x,y) = π x := by
  have hrem : ∑ y, (ρ y - min (π y) (ρ y)) = totalVariation π ρ := by
    rw [Finset.sum_sub_distrib, hρ.sum_eq_one, sum_min π ρ hπ hρ]; ring
  simp only [joint, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    ← Finset.sum_div, ← Finset.mul_sum, hrem]
  by_cases hd : totalVariation π ρ = 0
  · have hs : ∑ y, |π y - ρ y| = 0 := by unfold totalVariation at hd; linarith
    have hx : |π x - ρ x| = 0 := congrFun ((Fintype.sum_eq_zero_iff_of_nonneg (fun y => abs_nonneg (π y - ρ y))).mp hs) x
    simp [hd, sub_eq_zero.mp (abs_eq_zero.mp hx)]
  · field_simp
    ring

theorem joint_col (y : S) : ∑ x, joint π ρ (x,y) = ρ y := by
  simp_rw [joint_swap π ρ]
  exact joint_row ρ π hρ hπ y

theorem joint_distribution : IsDistribution (joint π ρ) := by
  constructor
  · rintro ⟨x,y⟩
    unfold joint
    apply add_nonneg
    · split_ifs <;> simp [hπ.nonneg, hρ.nonneg]
    · apply div_nonneg (mul_nonneg (sub_nonneg.mpr (min_le_left ..)) (sub_nonneg.mpr (min_le_right ..)))
      unfold totalVariation
      positivity
  · rw [Fintype.sum_prod_type]
    simp only [joint_row π ρ hπ hρ, hπ.sum_eq_one]

omit hπ hρ in
private theorem joint_diag (x : S) : joint π ρ (x,x) = min (π x) (ρ x) := by
  rcases le_total (π x) (ρ x) with h | h
  · simp [joint, min_eq_left h]
  · simp [joint, min_eq_right h]

variable [MeasurableSpace S] [MeasurableSingletonClass S]

/-- Coordinate projections of the pair distribution have exactly the prescribed laws. -/
theorem joint_projections :
    let P := (samplingPMF (joint π ρ) (joint_distribution π ρ hπ hρ)).toMeasure
    MeasurePreserving Prod.fst P (samplingPMF π hπ).toMeasure ∧
    MeasurePreserving Prod.snd P (samplingPMF ρ hρ).toMeasure := by
  let γ := joint π ρ
  have hγ := joint_distribution π ρ hπ hρ
  constructor
  · refine ⟨measurable_fst, Measure.ext_of_singleton fun x => ?_⟩
    rw [Measure.map_apply measurable_fst (measurableSet_singleton _), PMF.toMeasure_apply_fintype,
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), Fintype.sum_prod_type]
    simp only [Set.indicator, Set.mem_preimage, Set.mem_singleton_iff, samplingPMF, PMF.ofFintype_apply]
    simp_rw [Finset.sum_ite_irrel, Finset.sum_const_zero]
    simp [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hγ.nonneg (_,i)), joint_row π ρ hπ hρ]
  · refine ⟨measurable_snd, Measure.ext_of_singleton fun x => ?_⟩
    rw [Measure.map_apply measurable_snd (measurableSet_singleton _), PMF.toMeasure_apply_fintype,
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), Fintype.sum_prod_type_right]
    simp only [Set.indicator, Set.mem_preimage, Set.mem_singleton_iff, samplingPMF, PMF.ofFintype_apply]
    simp_rw [Finset.sum_ite_irrel, Finset.sum_const_zero]
    simp [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hγ.nonneg (i,_)), joint_col π ρ hπ hρ]

/-- The coordinates of the iid pair sample have the two required product marginals. -/
theorem iid_projections (N : ℕ) :
    let law := iid (joint π ρ) (joint_distribution π ρ hπ hρ) N
    MeasurePreserving (fun Z i => (Z i).1) law (iid π hπ N) ∧
    MeasurePreserving (fun Z i => (Z i).2) law (iid ρ hρ N) :=
  ⟨measurePreserving_pi _ _ (fun _ => (joint_projections π ρ hπ hρ).1),
   measurePreserving_pi _ _ (fun _ => (joint_projections π ρ hπ hρ).2)⟩

/-- Exact probability that every pair agrees, including the empty sample. -/
theorem iid_agreement (N : ℕ) :
    (iid (joint π ρ) (joint_distribution π ρ hπ hρ) N).real
      {Z | ∀ i, (Z i).1 = (Z i).2} = (1 - totalVariation π ρ)^N := by
  let γ := joint π ρ
  let P := (samplingPMF γ (joint_distribution π ρ hπ hρ)).toMeasure
  let D : Set (S × S) := {z | z.1 = z.2}
  have hD : P D = ENNReal.ofReal (1 - totalVariation π ρ) := by
    rw [← sum_min π ρ hπ hρ, ENNReal.ofReal_sum_of_nonneg (fun i _ => le_min (hπ.nonneg i) (hρ.nonneg i))]
    simp only [P, PMF.toMeasure_apply_fintype, Fintype.sum_prod_type, Set.indicator, D, Set.mem_setOf_eq,
      samplingPMF, PMF.ofFintype_apply, γ]
    simp [joint_diag]
  let E : Set (Fin N → S × S) := Set.univ.pi (fun _ => D)
  have heq : {Z : Fin N → S × S | ∀ i, (Z i).1 = (Z i).2} = E := by ext Z; simp [E,D]
  rw [heq]
  change ((Measure.pi (fun _ : Fin N => P)) (Set.univ.pi (fun _ => D))).toReal = _
  rw [Measure.pi_pi]
  simp only [hD, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.toReal_pow]
  have hmass : 0 ≤ 1 - totalVariation π ρ := by
    rw [← sum_min π ρ hπ hρ]
    exact Finset.sum_nonneg fun i _ => le_min (hπ.nonneg i) (hρ.nonneg i)
  rw [ENNReal.toReal_ofReal hmass]

/-- Probability of any disagreement is at most N times the population TV. Whenever
the two samples agree their empirical laws agree, even for sample-dependent tests. -/
theorem iid_mismatch_le (N : ℕ) :
    (iid (joint π ρ) (joint_distribution π ρ hπ hρ) N).real
      {Z | ∃ i, (Z i).1 ≠ (Z i).2} ≤ N * totalVariation π ρ := by
  let E : Set (Fin N → S × S) := {Z | ∀ i, (Z i).1 = (Z i).2}
  have heq : {Z : Fin N → S × S | ∃ i, (Z i).1 ≠ (Z i).2} = Eᶜ := by ext; simp [E]
  rw [heq, probReal_compl_eq_one_sub E.toFinite.measurableSet]
  have hd : totalVariation π ρ ≤ 1 := by
    have := Finset.sum_nonneg (s := Finset.univ) (fun i _ => le_min (hπ.nonneg i) (hρ.nonneg i))
    rw [sum_min π ρ hπ hρ] at this
    linarith
  have h := one_add_mul_le_pow (show -2 ≤ -totalVariation π ρ by linarith) N
  rw [← sub_eq_add_neg] at h
  change 1 - (iid (joint π ρ) (joint_distribution π ρ hπ hρ) N).real {Z | ∀ i, (Z i).1 = (Z i).2} ≤ _
  rw [iid_agreement π ρ hπ hρ N]
  linarith

/-- Empirical law, retaining the multiplicity of each observed state. -/
noncomputable def empirical {N : ℕ} (X : Fin N → S) (x : S) : ℝ :=
  Approximation.sampleMean X (fun y => if y = x then 1 else 0)

/-- A coupling bound for the empirical TV itself. In particular, for fixed N the
probability of any positive empirical TV tends to zero as the population TV does. -/
theorem empirical_tv_positive_le (N : ℕ) :
    (iid (joint π ρ) (joint_distribution π ρ hπ hρ) N).real
      {Z | 0 < totalVariation (empirical fun i => (Z i).1) (empirical fun i => (Z i).2)} ≤
        N * totalVariation π ρ := by
  refine (measureReal_mono ?_).trans (iid_mismatch_le π ρ hπ hρ N)
  intro Z hZ
  by_contra! heq
  have ha : (fun i => (Z i).1) = (fun i => (Z i).2) := by
    funext i
    by_contra h
    exact heq ⟨i, h⟩
  change 0 < totalVariation (empirical fun i => (Z i).1) (empirical fun i => (Z i).2) at hZ
  simp [ha, totalVariation] at hZ

omit hπ hρ in
/-- With independent samples, even equal population laws can yield different
empirical laws. One draw from each fair two-state law gives positive TV half the time. -/
theorem independent_fair_one :
    let ρ := Counterexample.bitLaw (1/2)
    let Q := (samplingPMF ρ (Counterexample.bitLaw_distribution (by norm_num))).toMeasure
    (Q.prod Q).real {z : Bool × Bool |
      0 < totalVariation (empirical (fun _ : Fin 1 => z.1)) (empirical (fun _ : Fin 1 => z.2))} = 1/2 := by
  let ρ := Counterexample.bitLaw (1/2)
  let Q := (samplingPMF ρ (Counterexample.bitLaw_distribution (by norm_num))).toMeasure
  let A : Set (Bool × Bool) := {false} ×ˢ {true}
  let B : Set (Bool × Bool) := {true} ×ˢ {false}
  have heq : {z : Bool × Bool | 0 < totalVariation (empirical (fun _ : Fin 1 => z.1))
      (empirical (fun _ : Fin 1 => z.2))} = A ∪ B := by
    ext ⟨x,y⟩
    cases x <;> cases y <;> norm_num [totalVariation, empirical, Approximation.sampleMean, A, B]
  have hd : Disjoint A B := by simp [A, B]
  have hm (x : Bool) : Q.real {x} = 1/2 := by
    cases x <;> norm_num [Measure.real, Q, samplingPMF, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
      ρ, Counterexample.bitLaw]
  change (Q.prod Q).real _ = _
  rw [heq, measureReal_union hd B.toFinite.measurableSet]
  simp only [A, B, measureReal_prod_prod, hm]
  norm_num

end Kadp.SamplingCoupling
