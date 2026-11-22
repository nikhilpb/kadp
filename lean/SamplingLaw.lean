import PopulationComparison

/-! Appendix B.3. Changing the sampling law in the radius-constrained program (18).
All product probabilities below concern the law actually used to fit the optimizer. -/

namespace Kadp.SamplingLaw

open Matrix MeasureTheory SargentStachurski.MarkovDecisionProcesses
open Kadp.Approximation Kadp.Idealized Kadp.Occupancy Kadp.Theorem1

variable {S : Type*} [Fintype S]

/-- The probability convention for total variation, one half of the ℓ¹ distance. -/
noncomputable def totalVariation (π ρ : S → ℝ) : ℝ := (∑ x, |π x - ρ x|) / 2

/-- A nonnegative function with range in [0,L] costs at most L times standard TV.
The subtraction of L/2 uses the equality of the two probability masses. -/
theorem transport_tv (π ρ : S → ℝ) (hπ : IsDistribution π) (hρ : IsDistribution ρ)
    (f : S → ℝ) {L : ℝ} (hf : ∀ x, f x ∈ Set.Icc 0 L) :
    π ⬝ᵥ f - ρ ⬝ᵥ f ≤ L * totalVariation π ρ := by
  calc
    _ = ∑ x, (π x - ρ x) * (f x - L/2) := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, sub_mul, dotProduct,
        hπ.sum_eq_one, hρ.sum_eq_one, sub_self, sub_zero]
    _ ≤ ∑ x, |π x - ρ x| * (L / 2) := by
      apply Finset.sum_le_sum
      intro x _
      refine (le_abs_self _).trans ?_
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact abs_le.mpr ⟨by linarith [(hf x).1], by linarith [(hf x).2]⟩
    _ = _ := by rw [← Finset.sum_mul, totalVariation]; ring

/-- Domination is defined without division, including zero-mass states. -/
theorem transport_ratio (π ρ f : S → ℝ) {k : ℝ}
    (hdom : ∀ x, π x ≤ (1 + k) * ρ x) (hf : ∀ x, 0 ≤ f x) :
    π ⬝ᵥ f ≤ (1 + k) * (ρ ⬝ᵥ f) := by
  unfold dotProduct
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun x _ => by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hdom x) (hf x)

/-- Opposite point masses attain the TV bound already for a 0–1 slack. -/
theorem sharp_tv :
    let π : Bool → ℝ := fun x => if x then 1 else 0
    let ρ : Bool → ℝ := fun x => if x then 0 else 1
    π ⬝ᵥ π - ρ ⬝ᵥ π = 1 ∧ totalVariation π ρ = 1 := by
  norm_num [dotProduct, totalVariation, Fintype.sum_bool]

variable {A H : Type*} [Fintype A] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (M : MDP S A) (Φ : S → H) {C B : ℝ}
variable [MeasurableSpace S] [MeasurableSingletonClass S]

/-- The product law of the observed draws. -/
noncomputable def iid (ρ : S → ℝ) (hρ : IsDistribution ρ) (N : ℕ) : Measure (Fin N → S) :=
  Measure.pi (fun _ : Fin N => (samplingPMF ρ hρ).toMeasure)

instance (ρ : S → ℝ) (hρ : IsDistribution ρ) (N : ℕ) : IsProbabilityMeasure (iid ρ hρ N) := by
  unfold iid
  infer_instance

/-- Apply Theorem 3 under the actual sampling law, uniformly over all fits. -/
theorem uniform_actual (μ : S → A) (ρ : S → ℝ) (hρ : IsDistribution ρ)
    (hC : 0 ≤ C) (hB : 0 ≤ B) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ₁ : δ < 1)
    {N : ℕ} (hN : 0 < N)
    (hsize : (envelope Φ M C B * (1 + Real.sqrt (2 * Real.log (1 / δ)))) ^ 2 / ε ^ 2 ≤ N) :
    1 - δ ≤ (iid ρ hρ N).real {X | ∀ p : Parameters H C B,
      ρ ⬝ᵥ policyResidual M μ (fit Φ p) ≤ sampleMean X (policyResidual M μ (fit Φ p)) + ε} := by
  let f (p : Parameters H C B) := policyResidual M μ (fit Φ p)
  let E : Set (Fin N → S) := {X | ε ≤ ⨆ p, ρ ⬝ᵥ f p - sampleMean X (f p)}
  have he : (iid ρ hρ N).real E ≤ δ := by
    simpa only [iid, E, f, sampling_integral] using
      Theorem3.theorem3 M Φ μ (samplingPMF ρ hρ).toMeasure hC hB hε hδ hδ₁ hN hsize
  have hgood : 1 - δ ≤ (iid ρ hρ N).real Eᶜ := by
    rw [probReal_compl_eq_one_sub E.toFinite.measurableSet]
    linarith
  refine hgood.trans (measureReal_mono ?_)
  intro X hX p
  have hbound : BddAbove (Set.range fun q : Parameters H C B => ρ ⬝ᵥ f q - sampleMean X (f q)) := by
    refine ⟨envelope Φ M C B / 2, ?_⟩
    rintro _ ⟨q, rfl⟩
    have hmean : 0 ≤ sampleMean X (f q) :=
      div_nonneg (Finset.sum_nonneg fun _ _ => le_max_right _ _) (Nat.cast_nonneg _)
    have hpop := dotProduct_le_dotProduct_of_nonneg_left
      (v := fun _ : S => envelope Φ M C B / 2)
      (fun x => (le_abs_self _).trans (abs_residual_le Φ M μ hC hB q x)) hρ.nonneg
    refine (sub_le_self _ hmean).trans ?_
    simpa only [f, policyResidual, dotProduct, ← Finset.sum_mul, hρ.sum_eq_one, one_mul] using hpop
  have hp := le_ciSup hbound p
  change ¬ ε ≤ ⨆ q, ρ ⬝ᵥ f q - sampleMean X (f q) at hX
  change ρ ⬝ᵥ f p ≤ sampleMean X (f p) + ε
  linarith [lt_of_not_ge hX]

variable [DecidableEq S] [DecidableEq A]

omit [MeasurableSpace S] [MeasurableSingletonClass S] [DecidableEq A] in
private theorem tv_deviation (μ : S → A) (ν ρ : S → ℝ) (hν : IsDistribution ν)
    (hρ : IsDistribution ρ) (hC : 0 ≤ C) (hB : 0 ≤ B) {ε : ℝ} {N : ℕ}
    (X : Fin N → S) (p : Parameters H C B)
    (hdev : ρ ⬝ᵥ policyResidual M μ (fit Φ p) ≤ sampleMean X (policyResidual M μ (fit Φ p)) + ε) :
    discountedOccupancy M μ ν ⬝ᵥ policyResidual M μ (fit Φ p) ≤
      sampleMean X (policyResidual M μ (fit Φ p)) +
      (ε + envelope Φ M C B / 2 * totalVariation (discountedOccupancy M μ ν) ρ) := by
  have ht := transport_tv _ _ (occupancy_isDistribution M μ hν) hρ (policyResidual M μ (fit Φ p))
    (fun x => ⟨le_max_right _ _, (le_abs_self _).trans (abs_residual_le Φ M μ hC hB p x)⟩)
  linarith only [ht, hdev]

/-- An unconditional TV bound relative to the best uniform approximation. -/
theorem tv_best_fit (μ : S → A) (hμ : M.IsOptimal μ) (ν ρ : S → ℝ)
    (hν : IsDistribution ν) (hρ : IsDistribution ρ) (hC : 0 ≤ C) (hB : 0 ≤ B)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ₁ : δ < 1) {N : ℕ} (hN : 0 < N)
    (hsize : (envelope Φ M C B * (1 + Real.sqrt (2 * Real.log (1 / δ)))) ^ 2 / ε ^ 2 ≤ N) :
    1 - δ ≤ (iid ρ hρ N).real {X | ∀ (p : Parameters H C B) s, IsOptimizer M Φ ν X p s →
      weightedL1 ν (optimalCost M - fit Φ p) ≤ (3 + M.β) / (1 - M.β) * bestError M Φ C B +
      2 * (ε + envelope Φ M C B / 2 * totalVariation (discountedOccupancy M μ ν) ρ) / (1 - M.β)} := by
  obtain ⟨q, hq⟩ := exists_best_fit M Φ hC hB
  refine (uniform_actual M Φ μ ρ hρ hC hB hε hδ hδ₁ hN hsize).trans (measureReal_mono ?_)
  intro X hX p s hp
  rw [hq]
  exact oracle_bound M μ ν X hN hμ hν _ _ _
    (sampleObjective_le_of_maximizes M ν X _ _ s hp.1 (hp.2 q))
    (tv_deviation M Φ μ ν ρ hν hρ hC hB X p (hX p))

/-- A comparator is chosen before sampling; the optimizer can depend arbitrarily on the draws. -/
private theorem fixed_of_transfer (μ : S → A) (hμ : M.IsOptimal μ) (ν ρ : S → ℝ)
    (hν : IsDistribution ν) (hρ : IsDistribution ρ) (hC : 0 ≤ C) (hB : 0 ≤ B)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ₁ : δ < 1) {N : ℕ} (hN : 0 < N)
    (hsize : (envelope Φ M C B * (1 + Real.sqrt (2 * Real.log (1 / δ)))) ^ 2 / ε ^ 2 ≤ N)
    (q : Parameters H C B) (allowance : (Fin N → ℝ) → ℝ)
    (ht : ∀ X (p : Parameters H C B) s, IsOptimizer M Φ ν X p s →
      ρ ⬝ᵥ policyResidual M μ (fit Φ p) ≤ sampleMean X (policyResidual M μ (fit Φ p)) + ε →
      discountedOccupancy M μ ν ⬝ᵥ policyResidual M μ (fit Φ p) ≤
        sampleMean X (policyResidual M μ (fit Φ p)) + allowance s) :
    1 - δ - δ ^ 4 ≤ (iid ρ hρ N).real {X | ∀ (p : Parameters H C B) s, IsOptimizer M Φ ν X p s →
      weightedL1 ν (optimalCost M - fit Φ p) ≤ ν ⬝ᵥ (optimalCost M - fit Φ q) +
        2 / (1 - M.β) * (ρ ⬝ᵥ bellmanResidual M (fit Φ q) + ε + allowance s)} := by
  let f := bellmanResidual M (fit Φ q)
  let good : Set (Fin N → S) := {X | ∀ p : Parameters H C B,
    ρ ⬝ᵥ policyResidual M μ (fit Φ p) ≤ sampleMean X (policyResidual M μ (fit Φ p)) + ε}
  let bad : Set (Fin N → S) := {X | ε ≤ sampleMean X f - ρ ⬝ᵥ f}
  have hu : 1 - δ ≤ (iid ρ hρ N).real good := uniform_actual M Φ μ ρ hρ hC hB hε hδ hδ₁ hN hsize
  have hb : (iid ρ hρ N).real bad ≤ δ ^ 4 := by
    simpa only [iid, bad, sampleMean, div_eq_inv_mul, sampling_integral] using
      fixed_comparator_tail (samplingPMF ρ hρ).toMeasure f hN (envelope_nonneg Φ M hC hB)
        hε hδ hδ₁ (fun x => ⟨le_max_right _ _,
          (le_abs_self _).trans (abs_bellmanResidual_le M Φ hC hB q x)⟩) hsize
  have hboth : 1 - δ - δ ^ 4 ≤ (iid ρ hρ N).real (good \ bad) := by
    have hs := measureReal_inter_add_sdiff (μ := iid ρ hρ N) (s := good) bad.toFinite.measurableSet
    have hi : (iid ρ hρ N).real (good ∩ bad) ≤ (iid ρ hρ N).real bad :=
      measureReal_mono Set.inter_subset_right
    linarith
  refine hboth.trans (measureReal_mono ?_)
  intro X hX p s hp
  have hc : sampleMean X f ≤ ρ ⬝ᵥ f + ε := by
    have := lt_of_not_ge (show ¬ ε ≤ sampleMean X f - ρ ⬝ᵥ f from hX.2)
    linarith
  refine (error_le_sample_comparator M μ ν X hμ hν _ _ _
    (sampleObjective_le_of_maximizes M ν X _ _ s hp.1 (hp.2 q)) (ht X p s hp (hX.1 p))).trans ?_
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add hc le_rfl)
    (div_nonneg (by norm_num) (sub_nonneg.mpr M.β_lt_one.le)))

/-- Fixed-comparator TV bound, requiring no likelihood ratio or coupled ideal sample. -/
theorem tv_fixed_comparator (μ : S → A) (hμ : M.IsOptimal μ) (ν ρ : S → ℝ)
    (hν : IsDistribution ν) (hρ : IsDistribution ρ) (hC : 0 ≤ C) (hB : 0 ≤ B)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ₁ : δ < 1) {N : ℕ} (hN : 0 < N)
    (hsize : (envelope Φ M C B * (1 + Real.sqrt (2 * Real.log (1 / δ)))) ^ 2 / ε ^ 2 ≤ N)
    (q : Parameters H C B) :
    1 - δ - δ ^ 4 ≤ (iid ρ hρ N).real {X | ∀ (p : Parameters H C B) s, IsOptimizer M Φ ν X p s →
      weightedL1 ν (optimalCost M - fit Φ p) ≤ ν ⬝ᵥ (optimalCost M - fit Φ q) +
        2 / (1 - M.β) * (ρ ⬝ᵥ bellmanResidual M (fit Φ q) + ε +
          (ε + envelope Φ M C B / 2 * totalVariation (discountedOccupancy M μ ν) ρ))} :=
  fixed_of_transfer M Φ μ hμ ν ρ hν hρ hC hB hε hδ hδ₁ hN hsize q _
    (fun X p _ _ hd => tv_deviation M Φ μ ν ρ hν hρ hC hB X p hd)

/-- The ratio correction uses the observed optimal slacks. The fitted concentration
error is multiplied by the density bound, even when all observed slacks vanish. -/
theorem ratio_fixed_comparator (μ : S → A) (hμ : M.IsOptimal μ) (ν ρ : S → ℝ)
    (hν : IsDistribution ν) (hρ : IsDistribution ρ) (hC : 0 ≤ C) (hB : 0 ≤ B)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ₁ : δ < 1) {N : ℕ} (hN : 0 < N)
    (hsize : (envelope Φ M C B * (1 + Real.sqrt (2 * Real.log (1 / δ)))) ^ 2 / ε ^ 2 ≤ N)
    (q : Parameters H C B) {k : ℝ} (hk : 0 ≤ k) (hdom : ∀ x, discountedOccupancy M μ ν x ≤ (1+k)*ρ x) :
    1 - δ - δ ^ 4 ≤ (iid ρ hρ N).real {X | ∀ (p : Parameters H C B) s, IsOptimizer M Φ ν X p s →
      weightedL1 ν (optimalCost M - fit Φ p) ≤ ν ⬝ᵥ (optimalCost M - fit Φ q) +
        2 / (1 - M.β) * (ρ ⬝ᵥ bellmanResidual M (fit Φ q) + ε +
          ((1+k)*ε + k*((∑ i, s i)/N)))} := by
  refine fixed_of_transfer M Φ μ hμ ν ρ hν hρ hC hB hε hδ hδ₁ hN hsize q _ ?_
  intro X p s hp hd
  let f := policyResidual M μ (fit Φ p)
  have hr := transport_ratio _ ρ f hdom (fun _ => le_max_right _ _)
  have hmean : sampleMean X f ≤ (∑ i, s i)/N := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact Finset.sum_le_sum fun i _ => (policyResidual_le_bellmanResidual M μ hμ.1 _ _).trans
      ((slackFeasible_iff ..).mp hp.1 i)
  change ρ ⬝ᵥ f ≤ sampleMean X f + ε at hd
  change discountedOccupancy M μ ν ⬝ᵥ f ≤ sampleMean X f + ((1+k)*ε + k*((∑ i, s i)/N))
  linarith only [hr, mul_le_mul_of_nonneg_left hd (by linarith : 0 ≤ 1+k),
    mul_le_mul_of_nonneg_left hmean hk]

namespace Counterexample

/-- Probability t of drawing false. -/
noncomputable def bitLaw (t : ℝ) (x : Bool) : ℝ := if x then 1-t else t

theorem bitLaw_distribution {t : ℝ} (ht : t ∈ Set.Icc 0 1) : IsDistribution (bitLaw t) := by
  constructor
  · intro x
    cases x <;> simp [bitLaw, ht.1, ht.2]
  · simp [bitLaw]

theorem ratio_two {t : ℝ} (ht : t ∈ Set.Icc 0 1) (x : Bool) :
    bitLaw t x ≤ (1+1)*bitLaw (1/2) x := by
  cases x <;> norm_num [bitLaw] <;> linarith [ht.1, ht.2]

/-- Every fitted slack in the example below is a positive multiple of this indicator. -/
def indicator (x : Bool) : ℝ := (x.toNat : ℝ)

private def countTrue {N : ℕ} (X : Fin N → Bool) : ℕ := ∑ i, (X i).toNat

private theorem mean_indicator {N : ℕ} (X : Fin N → Bool) :
    sampleMean X indicator = (countTrue X : ℝ) / N := by
  simp [sampleMean, countTrue, indicator]

private theorem fair_low (n : ℕ) :
    (iid (bitLaw (1/2)) (bitLaw_distribution (by norm_num)) (2*n+1)).real
      {X | 2 * countTrue X < 2*n+1} = 1/2 := by
  let ρ := bitLaw (1/2)
  have hρ : IsDistribution ρ := bitLaw_distribution (by norm_num)
  let Q := (samplingPMF ρ hρ).toMeasure
  let flip (X : Fin (2*n+1) → Bool) := fun i => !(X i)
  let low : Set (Fin (2*n+1) → Bool) := {X | 2 * countTrue X < 2*n+1}
  let law := iid ρ hρ (2*n+1)
  have hp : MeasurePreserving Bool.not Q Q := by
    refine ⟨measurable_of_finite _, Measure.ext_of_singleton fun x => ?_⟩
    rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton _)]
    have hpre : Bool.not ⁻¹' {x} = {!x} := by ext b; cases b <;> cases x <;> simp
    rw [hpre]
    simp only [Q, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), samplingPMF,
      PMF.ofFintype_apply, ρ, bitLaw]
    cases x <;> norm_num
  have hflip : MeasurePreserving flip law law := measurePreserving_pi _ _ (fun _ => hp)
  have hpre : flip ⁻¹' low = lowᶜ := by
    ext X
    have hcnt : countTrue (flip X) + countTrue X = 2*n+1 := by
      unfold countTrue
      rw [← Finset.sum_add_distrib]
      have hs (i) : (flip X i).toNat + (X i).toNat = 1 := by
        simp only [flip]; cases X i <;> decide
      simp [hs]
    change 2 * countTrue (flip X) < 2*n+1 ↔ ¬2 * countTrue X < 2*n+1
    omega
  have hm := congrArg ENNReal.toReal (hflip.measure_preimage low.toFinite.measurableSet.nullMeasurableSet)
  change law.real (flip ⁻¹' low) = law.real low at hm
  rw [hpre, probReal_compl_eq_one_sub low.toFinite.measurableSet] at hm
  change law.real low = 1/2
  linarith

/-- For every odd sample size and every coupling with the two stipulated iid
marginals, the probability that the printed empirical ratio fails is at least
1/2 − Nt. The bound is 1/2 for the fixed ideal law t=0 and at least 1/4 for the
strictly positive ideal law t=1/(4N). The approximate law is fair throughout. -/
theorem coupling_failure {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) {t : ℝ} (ht : t ∈ Set.Icc 0 1) (Y X : Ω → Fin (2*n+1) → Bool)
    (hY : MeasurePreserving Y P (iid (bitLaw t) (bitLaw_distribution ht) (2*n+1)))
    (hX : MeasurePreserving X P (iid (bitLaw (1/2)) (bitLaw_distribution (by norm_num)) (2*n+1))) :
    1/2 - (2*n+1 : ℕ)*t ≤ P.real {ω |
      sampleMean (Y ω) indicator - sampleMean (X ω) indicator > sampleMean (X ω) indicator} := by
  let allTrue : Fin (2*n+1) → Bool := fun _ => true
  let low : Set (Fin (2*n+1) → Bool) := {Z | 2 * countTrue Z < 2*n+1}
  let A := Y ⁻¹' {allTrue}
  let B := X ⁻¹' low
  have hA : P.real A = (1-t)^(2*n+1) := by
    unfold A Measure.real
    rw [hY.measure_preimage (measurableSet_singleton _).nullMeasurableSet, iid, Measure.pi_singleton]
    simp [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), samplingPMF, bitLaw,
      allTrue, ENNReal.toReal_ofReal (sub_nonneg.mpr ht.2)]
  have hB : P.real B = 1/2 := by
    change (P (X ⁻¹' low)).toReal = _
    rw [hX.measure_preimage low.toFinite.measurableSet.nullMeasurableSet]
    exact fair_low n
  have hAB : P.real A + P.real B - 1 ≤ P.real (A ∩ B) := by
    have h := measureReal_union_add_inter (μ := P) (s := A) (hX.measurable low.toFinite.measurableSet)
    linarith [measureReal_le_one (μ := P) (s := A ∪ B)]
  have hfail : A ∩ B ⊆ {ω |
      sampleMean (Y ω) indicator - sampleMean (X ω) indicator > sampleMean (X ω) indicator} := by
    intro ω hω
    have hy : Y ω = allTrue := hω.1
    have hx : 2 * countTrue (X ω) < 2*n+1 := hω.2
    have hNr : 0 < ((2*n+1 : ℕ) : ℝ) := by positivity
    have hs : sampleMean allTrue indicator = 1 := by
      simp [sampleMean, allTrue, indicator]
      positivity
    change sampleMean (X ω) indicator < sampleMean (Y ω) indicator - sampleMean (X ω) indicator
    rw [hy, hs, mean_indicator]
    have hlt : (2 : ℝ) * countTrue (X ω) < ((2*n+1 : ℕ) : ℝ) := by exact_mod_cast hx
    have hd := (div_lt_iff₀ hNr).mpr (show (countTrue (X ω) : ℝ) < (1/2) * ((2*n+1 : ℕ) : ℝ) by linarith)
    linarith
  have hber := one_add_mul_le_pow (show -2 ≤ -t by linarith [ht.2]) (2*n+1)
  rw [← sub_eq_add_neg] at hber
  refine le_trans ?_ (hAB.trans (measureReal_mono hfail))
  rw [hA, hB]
  linarith

/-- Absorbing, one-action dynamics, with cost −1 at true and +1 at false. -/
noncomputable def model : MDP Bool Unit := ofCosts (1/2) (by norm_num) (by norm_num)
  (fun x _ => if x then -1 else 1) (fun x _ y => if y = x then 1 else 0)
  (by intros; positivity) (by intro x _; simp)

theorem occupancy_eq (ν : Bool → ℝ) : discountedOccupancy model (fun _ => ()) ν = ν := by
  symm
  apply occupancy_unique
  funext x
  cases x <;> norm_num [model, ofCosts, MDP.Pσ, vecMul, dotProduct, Fintype.sum_bool] <;> ring

/-- With positive feature and offset radii, every admissible fit has canonical
slack equal to a strictly positive multiple of the indicator. -/
theorem slack_shape (p : Parameters ℝ 1 1) :
    0 < 1 + p.val.2 / 2 ∧
    bellmanResidual model (fit (fun _ => (0 : ℝ)) p) = fun x => (1 + p.val.2/2) * indicator x := by
  have hb := abs_le.mp p.property.2
  refine ⟨by linarith, ?_⟩
  let J := fit (fun _ : Bool => (0 : ℝ)) p
  let μ : Bool → Unit := fun _ => ()
  have hg : model.greedy (-J) = μ := Subsingleton.elim _ _
  have he := model.Tσ_eq_T_of_isGreedy (model.isGreedy_greedy (-J))
  rw [hg] at he
  funext x
  change max (J x - -(model.T (-J) x)) 0 = _
  rw [← he, MDP.Tσ_apply]
  cases x <;> norm_num [J, fit, model, ofCosts, indicator, Fintype.sum_bool] <;>
    grind

/-- Actual optimal solutions exist on each draw with these strictly positive radii.
Using canonical slacks for their fitted values retains optimality. -/
theorem optimizer_with_indicator (ν : Bool → ℝ) {N : ℕ} (X : Fin N → Bool) :
    ∃ p : Parameters ℝ 1 1, IsOptimizer model (fun _ => (0 : ℝ)) ν X p
      (fun i => (1 + p.val.2/2) * indicator (X i)) := by
  obtain ⟨p, s, hp⟩ := exists_optimizer model (fun _ => (0 : ℝ)) ν X
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
  have hs := (slack_shape p).2
  refine ⟨p, (slackFeasible_iff ..).mpr (fun i => (congrFun hs (X i)).le), ?_⟩
  intro q t ht
  refine ((hp.2 q t ht).trans (slackObjective_le_sampleObjective model ν X _ s hp.1)).trans_eq ?_
  simp [sampleObjective, sampleMean, slackObjective, hs]

private theorem mean_scale {N : ℕ} (Z : Fin N → Bool) (a : ℝ) :
    sampleMean Z (fun x => a * indicator x) = a * sampleMean Z indicator := by
  simp only [sampleMean, ← Finset.mul_sum]
  ring

/-- The failure bound holds for the canonical statewise slack of any sample-dependent
fit, hence in particular for any selection of optimizers obtained from the actual draws. -/
theorem coupling_failure_fitted {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) {t : ℝ} (ht : t ∈ Set.Icc 0 1) (Y X : Ω → Fin (2*n+1) → Bool)
    (hY : MeasurePreserving Y P (iid (bitLaw t) (bitLaw_distribution ht) (2*n+1)))
    (hX : MeasurePreserving X P (iid (bitLaw (1/2)) (bitLaw_distribution (by norm_num)) (2*n+1)))
    (p : (Fin (2*n+1) → Bool) → Parameters ℝ 1 1) :
    1/2 - (2*n+1 : ℕ)*t ≤ P.real {ω |
      let s := bellmanResidual model (fit (fun _ => (0 : ℝ)) (p (X ω)))
      sampleMean (Y ω) s - sampleMean (X ω) s > sampleMean (X ω) s} := by
  refine (coupling_failure P n ht Y X hY hX).trans (measureReal_mono ?_)
  intro ω hω
  obtain ⟨ha, hs⟩ := slack_shape (p (X ω))
  change sampleMean (X ω) _ < sampleMean (Y ω) _ - sampleMean (X ω) _
  rw [hs, mean_scale, mean_scale, ← mul_sub, mul_lt_mul_iff_right₀ ha]
  exact hω

end Counterexample
end Kadp.SamplingLaw
