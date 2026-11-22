import Occupancy
import MarkovDecisionProcesses.Bellman
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-! The deterministic part of Theorem 1. Samples are indexed by draws, so a state
occurring twice contributes twice to the slack penalty in (18). -/

namespace Kadp.Approximation

open Matrix SargentStachurski.MarkovDecisionProcesses Kadp.Occupancy

variable {S A : Type*} [Fintype S] [Fintype A] (M : MDP S A)

/-- Cost minimization, using the negative of the upstream reward Bellman operator. -/
noncomputable def optimalBellman (J : S → ℝ) : S → ℝ := -M.T (-J)

noncomputable def policyResidual (μ : S → A) (J : S → ℝ) (x : S) : ℝ :=
  max (J x - costBellman M μ J x) 0

noncomputable def bellmanResidual (J : S → ℝ) (x : S) : ℝ :=
  max (J x - optimalBellman M J x) 0

/-- Feasibility of the slack variables in (18), for a given candidate and draw. -/
def SlackFeasible {N : ℕ} (X : Fin N → S) (J : S → ℝ) (s : Fin N → ℝ) : Prop :=
  ∀ i, 0 ≤ s i ∧ J (X i) ≤ optimalBellman M J (X i) + s i

/-- At every draw the positive Bellman residual is exactly the least feasible slack. -/
theorem slackFeasible_iff {N : ℕ} (X : Fin N → S) (J : S → ℝ) (s : Fin N → ℝ) :
    SlackFeasible M X J s ↔ ∀ i, bellmanResidual M J (X i) ≤ s i := by
  simp only [SlackFeasible, bellmanResidual, max_le_iff, sub_le_iff_le_add', and_comm]

/-- Expanding the Bellman constraint recovers the individual action constraints of (18).
For `ofCosts` the feasible action set is the entire action space. -/
theorem slackFeasible_iff_actions {N : ℕ} (X : Fin N → S) (J : S → ℝ) (s : Fin N → ℝ) :
    SlackFeasible M X J s ↔ ∀ i, 0 ≤ s i ∧ ∀ a ∈ M.Γ (X i),
      J (X i) ≤ -M.B (-J) (X i) a + s i := by
  constructor
  · intro h i
    refine ⟨(h i).1, fun a ha => ?_⟩
    exact (h i).2.trans (add_le_add (neg_le_neg (M.B_le_T (-J) ha)) le_rfl)
  · intro h i
    refine ⟨(h i).1, ?_⟩
    have hmin := (h i).2 (M.greedy (-J) (X i)) (M.greedy_mem _ _)
    have hgreedy := congrFun (M.Tσ_eq_T_of_isGreedy (M.isGreedy_greedy (-J))) (X i)
    change M.B (-J) (X i) (M.greedy (-J) (X i)) = M.T (-J) (X i) at hgreedy
    simpa only [optimalBellman, Pi.neg_apply, hgreedy] using hmin

noncomputable def sampleMean {N : ℕ} (X : Fin N → S) (f : S → ℝ) : ℝ :=
  (∑ i, f (X i)) / N

noncomputable def weightedL1 (ν J : S → ℝ) : ℝ := ∑ x, ν x * |J x|

/-- The objective in (18) after eliminating the slack variables. -/
noncomputable def sampleObjective {N : ℕ} (ν : S → ℝ) (X : Fin N → S) (J : S → ℝ) : ℝ :=
  ν ⬝ᵥ J - 2 / (1 - M.β) * sampleMean X (bellmanResidual M J)

/-- The objective with the slack variables retained. -/
noncomputable def slackObjective {N : ℕ} (ν J : S → ℝ) (s : Fin N → ℝ) : ℝ :=
  ν ⬝ᵥ J - 2 / (1 - M.β) * ((∑ i, s i) / N)

theorem slackObjective_le_sampleObjective {N : ℕ} (ν : S → ℝ) (X : Fin N → S)
    (J : S → ℝ) (s : Fin N → ℝ) (hs : SlackFeasible M X J s) :
    slackObjective M ν J s ≤ sampleObjective M ν X J := by
  apply sub_le_sub_left
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (by norm_num) (sub_nonneg.mpr M.β_lt_one.le))
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ => (slackFeasible_iff ..).1 hs i)
    (Nat.cast_nonneg N)

/-- Every optimizer of (18) dominates the comparator in the reduced objective. -/
theorem sampleObjective_le_of_maximizes {N : ℕ} (ν : S → ℝ) (X : Fin N → S)
    (J V : S → ℝ) (s : Fin N → ℝ) (hs : SlackFeasible M X J s)
    (hmax : ∀ t, SlackFeasible M X V t → slackObjective M ν V t ≤ slackObjective M ν J s) :
    sampleObjective M ν X V ≤ sampleObjective M ν X J :=
  (hmax (fun i => bellmanResidual M V (X i)) ((slackFeasible_iff ..).2 fun _ => le_rfl)).trans
    (slackObjective_le_sampleObjective M ν X J s hs)

theorem continuous_bellmanResidual (x : S) :
    Continuous (fun J => bellmanResidual M J x) := by
  have hLip : LipschitzWith ⟨M.β, M.β_pos.le⟩ M.T :=
    LipschitzWith.of_dist_le_mul fun v w => by
      simp only [dist_eq_norm]
      exact M.isContractionOn_T.norm_sub_le v (Set.mem_univ _) w (Set.mem_univ _)
  have hT : Continuous (optimalBellman M) := (hLip.continuous.comp continuous_neg).neg
  exact ((continuous_apply x).sub ((continuous_apply x).comp hT)).max continuous_const

theorem continuous_sampleObjective {N : ℕ} (ν : S → ℝ) (X : Fin N → S) :
    Continuous (sampleObjective M ν X) := by
  have hres := continuous_bellmanResidual M
  unfold sampleObjective sampleMean dotProduct
  fun_prop

/-- On a nonempty compact set of candidate values, the original program (18)
attains a maximum. The maximizing slack vector may be chosen pointwise minimal. -/
theorem exists_slackOptimizer {N : ℕ} (ν : S → ℝ) (X : Fin N → S) (F : Set (S → ℝ))
    (hF : F.Nonempty) (hcomp : IsCompact F) :
    ∃ J ∈ F, ∃ s, SlackFeasible M X J s ∧ ∀ V ∈ F, ∀ t, SlackFeasible M X V t →
      slackObjective M ν V t ≤ slackObjective M ν J s := by
  obtain ⟨J, hJ, hmax⟩ := hcomp.exists_isMaxOn hF (continuous_sampleObjective M ν X).continuousOn
  refine ⟨J, hJ, fun i => bellmanResidual M J (X i), (slackFeasible_iff ..).2 (fun _ => le_rfl), ?_⟩
  intro V hV t ht
  exact (slackObjective_le_sampleObjective M ν X V t ht).trans ((isMaxOn_iff.mp hmax) V hV)

theorem policyResidual_le_bellmanResidual (μ : S → A) (hμ : M.IsFeasible μ) (J : S → ℝ) :
    policyResidual M μ J ≤ bellmanResidual M J := by
  intro x
  apply max_le_max_right
  apply sub_le_sub_left
  rw [costBellman_eq_neg_reward]
  exact neg_le_neg (M.Tσ_le_T ⟨μ, hμ⟩ (-J) x)

variable [DecidableEq S]

/-- One-sided residual propagation: discounted accumulation of positive residuals
bounds the amount by which a candidate overestimates the policy cost at each state. -/
theorem positive_error_le_resolvent (μ : S → A) (J : S → ℝ) :
    (fun x => max (J x - policyCost M μ x) 0) ≤
      (1 - M.β • M.Pσ μ)⁻¹ *ᵥ policyResidual M μ J := by
  let R := { M with r := fun x _ => policyResidual M μ J x }
  have hzero : (0 : S → ℝ) ≤ R.Tσ μ 0 := by
    intro x
    simp only [R.Tσ_apply, Pi.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero, add_zero]
    exact le_max_right _ _
  have hsub : J - policyCost M μ ≤ R.Tσ μ (J - policyCost M μ) := by
    rw [R.Tσ_eq]
    change J - policyCost M μ ≤ policyResidual M μ J + M.β • (M.Pσ μ *ᵥ (J - policyCost M μ))
    rw [mulVec_sub, smul_sub]
    intro x
    have hfix := congrFun (costBellman_policyCost M μ) x
    have hres : J x - costBellman M μ J x ≤ policyResidual M μ J x := le_max_left _ _
    simp only [costBellman, Pi.sub_apply, Pi.add_apply, Pi.neg_apply] at hfix hres ⊢
    linarith only [hfix, hres]
  have hle := le_fixedPt_of_le_apply (R.Tσ_monotone μ) hsub (R.tendsto_iterate_Tσ μ _)
  have hnonneg := le_fixedPt_of_le_apply (R.Tσ_monotone μ) hzero (R.tendsto_iterate_Tσ μ _)
  rw [R.vσ_eq_inv μ] at hle hnonneg
  exact fun x => max_le (hle x) (hnonneg x)

/-- Occupancy averages the accumulated positive residual in the initial distribution. -/
theorem positive_error_le_occupancy (μ : S → A) (ν J : S → ℝ) (hν : IsDistribution ν) :
    ν ⬝ᵥ (fun x => max (J x - policyCost M μ x) 0) ≤
      (discountedOccupancy M μ ν ⬝ᵥ policyResidual M μ J) / (1 - M.β) := by
  apply (dotProduct_le_dotProduct_of_nonneg_left (positive_error_le_resolvent M μ J) hν.nonneg).trans
  apply le_of_eq
  rw [discountedOccupancy, smul_dotProduct, smul_eq_mul, dotProduct_mulVec]
  field_simp [sub_ne_zero.mpr M.β_lt_one.ne']

variable [DecidableEq A]

noncomputable def optimalCost : S → ℝ := -M.vstar

theorem optimalBellman_optimalCost : optimalBellman M (optimalCost M) = optimalCost M := by
  simp only [optimalBellman, optimalCost, neg_neg, M.isFixedPt_T_vstar.eq]

/-- Uniform pointwise control of the comparator's positive Bellman residual.
Consequently the comparator requires no sampling deviation estimate. -/
theorem bellmanResidual_le (V : S → ℝ) (x : S) :
    bellmanResidual M V x ≤ (1 + M.β) * ‖optimalCost M - V‖ := by
  have hcon := M.isContractionOn_T.norm_sub_le M.vstar (Set.mem_univ _) (-V) (Set.mem_univ _)
  rw [M.isFixedPt_T_vstar.eq] at hcon
  have hnorm : ‖M.vstar - -V‖ = ‖optimalCost M - V‖ := by
    rw [← norm_neg (optimalCost M - V)]
    congr 1
    unfold optimalCost
    abel
  rw [hnorm] at hcon
  have hTx := (norm_le_pi_norm (M.vstar - M.T (-V)) x).trans hcon
  have hVx := norm_le_pi_norm (optimalCost M - V) x
  simp only [Real.norm_eq_abs, Pi.sub_apply, optimalCost, Pi.neg_apply] at hTx hVx
  apply max_le
  · change V x - -(M.T (-V) x) ≤ (1 + M.β) * ‖-M.vstar - V‖
    linarith only [(abs_le.mp hTx).1, (abs_le.mp hVx).1]
  · exact mul_nonneg (by linarith only [M.β_pos]) (norm_nonneg _)

omit [Fintype S] [DecidableEq S] in
private theorem sampleMean_mono {N : ℕ} (X : Fin N → S) {f g : S → ℝ} (h : f ≤ g) :
    sampleMean X f ≤ sampleMean X g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ => h (X i)) (Nat.cast_nonneg N)

omit [Fintype S] [DecidableEq S] in
private theorem sampleMean_le_const {N : ℕ} (X : Fin N → S) (hN : 0 < N)
    {f : S → ℝ} {c : ℝ} (hf : ∀ x, f x ≤ c) : sampleMean X f ≤ c := by
  have h := sampleMean_mono X (g := fun _ => c) hf
  simpa [sampleMean, nsmul_eq_mul, Nat.ne_of_gt hN] using h

omit [DecidableEq S] in
private theorem weightedL1_split (ν U J : S → ℝ) :
    weightedL1 ν (U - J) = ν ⬝ᵥ U - ν ⬝ᵥ J + 2 * (ν ⬝ᵥ fun x => max (J x - U x) 0) := by
  simp only [weightedL1, dotProduct, ← Finset.sum_sub_distrib, Finset.mul_sum,
    ← Finset.sum_add_distrib, Pi.sub_apply]
  apply Finset.sum_congr rfl
  intro x _
  rcases le_total (J x) (U x) with hx | hx
  · rw [abs_of_nonneg (sub_nonneg.mpr hx), max_eq_right (sub_nonpos.mpr hx)]
    ring
  · rw [abs_of_nonpos (sub_nonpos.mpr hx), max_eq_left (sub_nonneg.mpr hx)]
    ring

/-- The common part of (19) and (25). Sample optimality pays for the comparator's
empirical slack, and the single fitted-policy deviation costs ε. -/
theorem error_le_sample_comparator (μ : S → A) (ν : S → ℝ) {N : ℕ} (X : Fin N → S)
    (hμ : M.IsOptimal μ) (hν : IsDistribution ν) (J V : S → ℝ) (ε : ℝ)
    (hfit : sampleObjective M ν X V ≤ sampleObjective M ν X J)
    (hdev : discountedOccupancy M μ ν ⬝ᵥ policyResidual M μ J ≤
      sampleMean X (policyResidual M μ J) + ε) :
    weightedL1 ν (optimalCost M - J) ≤ ν ⬝ᵥ (optimalCost M - V) +
      2 / (1 - M.β) * (sampleMean X (bellmanResidual M V) + ε) := by
  have hβ : 0 < 1 - M.β := sub_pos.mpr M.β_lt_one
  have hcost : policyCost M μ = optimalCost M := congrArg Neg.neg hμ.2
  have hpos := positive_error_le_occupancy M μ ν J hν
  rw [hcost] at hpos
  have hgen := hdev.trans (add_le_add (sampleMean_mono X (policyResidual_le_bellmanResidual M μ hμ.1 J)) le_rfl)
  rw [weightedL1_split, dotProduct_sub]
  unfold sampleObjective at hfit
  have hfit' := mul_le_mul_of_nonneg_right hfit hβ.le
  have hpos' := (le_div_iff₀ hβ).mp hpos
  field_simp [hβ.ne'] at hfit' ⊢
  nlinarith only [hfit', hpos', hgen]

/-- The pathwise oracle inequality behind (19). Only the fitted function's
fixed-policy residual needs a one-sided generalization estimate. Every comparator
is controlled pointwise, giving the stronger additive term `2 ε / (1 - β)`. -/
theorem oracle_bound (μ : S → A) (ν : S → ℝ) {N : ℕ} (X : Fin N → S) (hN : 0 < N)
    (hμ : M.IsOptimal μ) (hν : IsDistribution ν) (J V : S → ℝ) (ε : ℝ)
    (hfit : sampleObjective M ν X V ≤ sampleObjective M ν X J)
    (hdev : discountedOccupancy M μ ν ⬝ᵥ policyResidual M μ J ≤
      sampleMean X (policyResidual M μ J) + ε) :
    weightedL1 ν (optimalCost M - J) ≤
      (3 + M.β) / (1 - M.β) * ‖optimalCost M - V‖ + 2 * ε / (1 - M.β) := by
  have hβ : 0 < 1 - M.β := sub_pos.mpr M.β_lt_one
  have hslack := sampleMean_le_const X hN (bellmanResidual_le M V)
  have hval : ν ⬝ᵥ optimalCost M - ν ⬝ᵥ V ≤ ‖optimalCost M - V‖ := by
    rw [← dotProduct_sub]
    calc ν ⬝ᵥ (optimalCost M - V) ≤ ν ⬝ᵥ (fun _ => ‖optimalCost M - V‖) := by
          apply dotProduct_le_dotProduct_of_nonneg_left _ hν.nonneg
          intro x
          have hx := norm_le_pi_norm (optimalCost M - V) x
          rw [Real.norm_eq_abs] at hx
          exact (le_abs_self _).trans hx
      _ = ‖optimalCost M - V‖ := by rw [dotProduct, ← Finset.sum_mul, hν.sum_eq_one, one_mul]
  refine (error_le_sample_comparator M μ ν X hμ hν J V ε hfit hdev).trans ?_
  rw [dotProduct_sub]
  calc
    _ ≤ ‖optimalCost M - V‖ + 2 / (1 - M.β) * ((1 + M.β) * ‖optimalCost M - V‖ + ε) :=
      add_le_add hval (mul_le_mul_of_nonneg_left (add_le_add hslack le_rfl) (by positivity))
    _ = _ := by field_simp [hβ.ne']; ring

end Kadp.Approximation
