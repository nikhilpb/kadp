import Kadp.Occupancy
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-! Affine fits and the occupancy sampling law for the idealized program (18). -/

namespace Kadp.Idealized

open Matrix MeasureTheory SargentStachurski.MarkovDecisionProcesses
open scoped BigOperators

variable {S A H : Type*} [Fintype S] [Fintype A]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Feasible feature weights and intercepts. -/
def Parameters (H : Type*) [NormedAddCommGroup H] (C B : ℝ) :=
  {p : H × ℝ // ‖p.1‖ ≤ C ∧ |p.2| ≤ B}

omit [InnerProductSpace ℝ H] in
theorem parameters_nonempty {C B : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B) :
    Nonempty (Parameters H C B) :=
  ⟨⟨(0, 0), by simpa using And.intro hC hB⟩⟩

variable (Φ : S → H) {C B : ℝ}

noncomputable def fit (p : Parameters H C B) (x : S) : ℝ := inner ℝ (Φ x) p.val.1 + p.val.2

/-- The admissible value vectors form a compact set even when the feature space is
infinite dimensional. Projection onto the finite feature span preserves every fit. -/
theorem compact_fits : IsCompact (Set.range (fit Φ : Parameters H C B → S → ℝ)) := by
  let U := Submodule.span ℝ (Set.range Φ)
  letI : FiniteDimensional ℝ U := FiniteDimensional.span_of_finite ℝ (Set.finite_range Φ)
  let eval : U × ℝ → S → ℝ := fun q x => inner ℝ (Φ x) (q.1 : H) + q.2
  have hc : Continuous eval := by
    apply continuous_pi
    intro x
    exact (continuous_const.inner (U.subtypeL.continuous.comp continuous_fst)).add continuous_snd
  have heq : Set.range (fit Φ : Parameters H C B → S → ℝ) =
      eval '' (Metric.closedBall (0 : U) C ×ˢ Set.Icc (-B) B) := by
    ext J
    constructor
    · rintro ⟨p, rfl⟩
      refine ⟨(U.orthogonalProjectionOnto p.val.1, p.val.2), ⟨?_, abs_le.mp p.property.2⟩, ?_⟩
      · simpa only [Metric.mem_closedBall, dist_zero_right] using
          (U.norm_orthogonalProjectionOnto_apply_le p.val.1).trans p.property.1
      · funext x
        let u : U := ⟨Φ x, Submodule.subset_span (Set.mem_range_self x)⟩
        exact congrArg (· + p.val.2) (U.inner_orthogonalProjectionOnto_eq_of_mem_left u p.val.1)
    · rintro ⟨⟨w,b⟩, ⟨hw,hb⟩, rfl⟩
      refine ⟨⟨((w : H), b), ?_, abs_le.mpr hb⟩, rfl⟩
      change ‖w‖ ≤ C
      simpa only [Metric.mem_closedBall, dist_zero_right] using hw
  rw [heq]
  exact ((isCompact_closedBall (0 : U) C).prod isCompact_Icc).image hc

/-- Convert a finite probability row (possibly with zero coordinates) to its probability mass function. -/
noncomputable def samplingPMF (ν : S → ℝ) (hν : IsDistribution ν) : PMF S :=
  PMF.ofFintype (fun x => ENNReal.ofReal (ν x)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => hν.nonneg x), hν.sum_eq_one, ENNReal.ofReal_one])

theorem sampling_integral [MeasurableSpace S] [MeasurableSingletonClass S]
    (ν : S → ℝ) (hν : IsDistribution ν) (f : S → ℝ) :
    ∫ x, f x ∂(samplingPMF ν hν).toMeasure = ν ⬝ᵥ f := by
  rw [PMF.integral_eq_sum]
  simp [samplingPMF, ENNReal.toReal_ofReal, hν.nonneg, dotProduct]

variable (M : MDP S A) (μ : S → A)

/-- The feature difference for a fixed policy. -/
noncomputable def featureDifference (x : S) : H :=
  Φ x - M.β • ∑ y, M.Pσ μ x y • Φ y

theorem norm_featureDifference (x : S) :
    ‖featureDifference Φ M μ x‖ ≤ ‖Φ‖ * (1 + M.β) := by
  have hP := M.isMarkov_Pσ μ
  have hmean : ‖∑ y, M.Pσ μ x y • Φ y‖ ≤ ‖Φ‖ := calc
    _ ≤ ∑ y, ‖M.Pσ μ x y • Φ y‖ := norm_sum_le _ _
    _ = ∑ y, M.Pσ μ x y * ‖Φ y‖ := by simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hP.nonneg _ _)]
    _ ≤ ∑ y, M.Pσ μ x y * ‖Φ‖ := Finset.sum_le_sum fun y _ =>
      mul_le_mul_of_nonneg_left (norm_le_pi_norm Φ y) (hP.nonneg x y)
    _ = _ := by rw [← Finset.sum_mul, hP.rowsum, one_mul]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, Real.norm_of_nonneg M.β_pos.le]
  nlinarith [norm_le_pi_norm Φ x, mul_le_mul_of_nonneg_left hmean M.β_pos.le]

theorem fit_residual_eq (p : Parameters H C B) (x : S) :
    fit Φ p x - Occupancy.costBellman M μ (fit Φ p) x =
      inner ℝ (featureDifference Φ M μ x) p.val.1 + (1 - M.β) * p.val.2 - (-M.rσ μ x) := by
  simp only [fit, Occupancy.costBellman, Pi.add_apply, Pi.neg_apply, Pi.smul_apply,
    smul_eq_mul, mulVec, dotProduct, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
    (M.isMarkov_Pσ μ).rowsum, one_mul, featureDifference, inner_sub_left, real_inner_smul_left,
    sum_inner]
  ring

/-- The coefficient in the sample threshold Ξ, before its confidence factor. -/
noncomputable def envelope (C B : ℝ) : ℝ :=
  4 * C * ‖Φ‖ * (1 + M.β) + 4 * B * (1 - M.β) + 2 * ‖M.r‖

omit [InnerProductSpace ℝ H] in
theorem envelope_nonneg (hC : 0 ≤ C) (hB : 0 ≤ B) : 0 ≤ envelope Φ M C B := by
  unfold envelope
  positivity [M.β_pos, M.β_lt_one]

theorem abs_residual_le (hC : 0 ≤ C) (hB : 0 ≤ B) (p : Parameters H C B) (x : S) :
    |max (fit Φ p x - Occupancy.costBellman M μ (fit Φ p) x) 0| ≤ envelope Φ M C B / 2 := by
  rw [abs_of_nonneg (le_max_right _ _), max_le_iff, fit_residual_eq]
  refine ⟨?_, div_nonneg (envelope_nonneg Φ M hC hB) (by norm_num)⟩
  have hinner := (real_inner_le_norm (featureDifference Φ M μ x) p.val.1).trans
    (mul_le_mul (norm_featureDifference Φ M μ x) p.property.1 (norm_nonneg _) (by positivity [M.β_pos]))
  have hoff := mul_le_mul_of_nonneg_left ((le_abs_self p.val.2).trans p.property.2) (sub_nonneg.mpr M.β_lt_one.le)
  have hcost : M.rσ μ x ≤ ‖M.r‖ :=
    (le_abs_self _).trans ((norm_le_pi_norm (M.r x) (μ x)).trans (norm_le_pi_norm M.r x))
  have hpos : 0 ≤ C * (‖Φ‖ * (1 + M.β)) + B * (1 - M.β) := by positivity [M.β_pos, M.β_lt_one]
  unfold envelope
  linarith

end Kadp.Idealized
