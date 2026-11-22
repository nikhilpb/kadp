import Approximation

/-! The weighted max norm, its one-step drift, and the deterministic
comparator appearing in the weighted approximation guarantee (25). -/

namespace Kadp.Weighted

open Matrix SargentStachurski.MarkovDecisionProcesses Kadp.Occupancy Kadp.Approximation

/-- The manuscript's class Ψ of state weights. -/
def Weight (S : Type*) := {ψ : S → ℝ // ∀ x, 1 ≤ ψ x}

def unitWeight (S : Type*) : Weight S := ⟨fun _ => 1, fun _ => le_rfl⟩

variable {S A : Type*} [Fintype S] [Fintype A]

noncomputable def weightedSup (ψ : Weight S) (f : S → ℝ) : ℝ :=
  ‖fun x => f x / ψ.val x‖

/-- The ratios are nonnegative by stochasticity, so their ordinary sup norm
is precisely their maximum over all state-action pairs. -/
noncomputable def drift (M : MDP S A) (ψ : Weight S) : ℝ :=
  ‖fun xa : S × A => (∑ y, ψ.val y * M.P xa.1 xa.2 y) / ψ.val xa.1‖

theorem abs_le_weightedSup_mul (ψ : Weight S) (f : S → ℝ) (x : S) :
    |f x| ≤ weightedSup ψ f * ψ.val x := by
  have hψ : 0 < ψ.val x := lt_of_lt_of_le zero_lt_one (ψ.property x)
  apply (div_le_iff₀ hψ).mp
  have h := norm_le_pi_norm (fun y => f y / ψ.val y) x
  simpa only [Real.norm_eq_abs, abs_div, abs_of_pos hψ, weightedSup] using h

theorem transition_weight_le (M : MDP S A) (ψ : Weight S) (x : S) (a : A) :
    (∑ y, ψ.val y * M.P x a y) ≤ drift M ψ * ψ.val x := by
  apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one (ψ.property x))).mp
  exact (le_abs_self _).trans (norm_le_pi_norm
    (fun xa : S × A => (∑ y, ψ.val y * M.P xa.1 xa.2 y) / ψ.val xa.1) (x, a))

/-- A one-sided perturbation estimate for the reward-form Bellman maximum.
The multiplier may exceed one. -/
private theorem rewardBellman_le (M : MDP S A) (ψ : Weight S) (u v : S → ℝ)
    {d : ℝ} (hd : 0 ≤ d) (huv : ∀ y, u y ≤ v y + d * ψ.val y) (x : S) :
    M.T u x ≤ M.T v x + M.β * (d * (drift M ψ * ψ.val x)) := by
  apply Finset.sup'_le
  intro a ha
  have hsum : (∑ y, u y * M.P x a y) ≤
      (∑ y, v y * M.P x a y) + d * (drift M ψ * ψ.val x) := calc
    _ ≤ ∑ y, (v y + d * ψ.val y) * M.P x a y := Finset.sum_le_sum fun y _ =>
      mul_le_mul_of_nonneg_right (huv y) (M.P_nonneg x a y)
    _ = (∑ y, v y * M.P x a y) + d * (∑ y, ψ.val y * M.P x a y) := by
      simp only [add_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left (transition_weight_le M ψ x a) hd)
  refine le_trans ?_ (add_le_add_left (M.B_le_T v ha) _)
  unfold MDP.B
  linarith only [mul_le_mul_of_nonneg_left hsum M.β_pos.le]

variable (M : MDP S A) [DecidableEq S] [DecidableEq A]

/-- The full signed comparator residual, bounded in absolute value at each state. -/
theorem abs_bellman_error_le_weight (V : S → ℝ) (ψ : Weight S) (x : S) :
    |V x - optimalBellman M V x| ≤
      (weightedSup ψ (optimalCost M - V) * (1 + M.β * drift M ψ)) * ψ.val x := by
  let d := weightedSup ψ (optimalCost M - V)
  have hd : 0 ≤ d := norm_nonneg _
  have herr (y : S) : |optimalCost M y - V y| ≤ d * ψ.val y :=
    abs_le_weightedSup_mul ψ (optimalCost M - V) y
  have hup := rewardBellman_le M ψ (-V) M.vstar hd (fun y => by
    have hu := (abs_le.mp (herr y)).2
    change -M.vstar y - V y ≤ _ at hu
    change -V y ≤ _
    linarith only [hu]) x
  have hlo := rewardBellman_le M ψ M.vstar (-V) hd (fun y => by
    have hl := (abs_le.mp (herr y)).1
    change _ ≤ -M.vstar y - V y at hl
    change _ ≤ -V y + _
    linarith only [hl]) x
  rw [M.isFixedPt_T_vstar.eq] at hup hlo
  have hx := abs_le.mp (herr x)
  change _ ≤ -M.vstar x - V x ∧ -M.vstar x - V x ≤ _ at hx
  change |V x - -M.T (-V) x| ≤ (d * (1 + M.β * drift M ψ)) * ψ.val x
  exact abs_le.mpr ⟨by linarith only [hlo, hx.2], by linarith only [hup, hx.1]⟩

/-- Pointwise control of the least feasible comparator slack in (18). -/
theorem bellmanResidual_le_weight (V : S → ℝ) (ψ : Weight S) (x : S) :
    bellmanResidual M V x ≤
      (weightedSup ψ (optimalCost M - V) * (1 + M.β * drift M ψ)) * ψ.val x :=
  (max_le (le_abs_self _) (abs_nonneg _)).trans (abs_bellman_error_le_weight M V ψ x)

/-- The product under the infimum in (25). -/
noncomputable def comparatorBound (μ : S → A) (ν V : S → ℝ) (ψ : Weight S) : ℝ :=
  weightedSup ψ (optimalCost M - V) *
    (ν ⬝ᵥ ψ.val + 2 * (discountedOccupancy M μ ν ⬝ᵥ ψ.val) * (1 + M.β * drift M ψ) / (1 - M.β))

omit [DecidableEq S] in
private theorem dot_le_factor (ρ f ψ : S → ℝ) (k : ℝ)
    (hρ : ∀ x, 0 ≤ ρ x) (hf : ∀ x, f x ≤ k * ψ x) :
    ρ ⬝ᵥ f ≤ k * (ρ ⬝ᵥ ψ) := by
  calc
    _ ≤ ρ ⬝ᵥ (k • ψ) := dotProduct_le_dotProduct_of_nonneg_left hf hρ
    _ = _ := by rw [dotProduct_smul, smul_eq_mul]

theorem population_le_comparatorBound (μ : S → A) (ν V : S → ℝ) (ψ : Weight S)
    (hν : IsDistribution ν) :
    ν ⬝ᵥ (optimalCost M - V) + 2 / (1 - M.β) * (discountedOccupancy M μ ν ⬝ᵥ bellmanResidual M V) ≤
      comparatorBound M μ ν V ψ := by
  have initial := dot_le_factor ν (optimalCost M - V) ψ.val _ hν.nonneg
    (fun x => (le_abs_self _).trans (abs_le_weightedSup_mul ψ (optimalCost M - V) x))
  have residual := dot_le_factor (discountedOccupancy M μ ν) (bellmanResidual M V) ψ.val _
    (occupancy_isDistribution M μ hν).nonneg (bellmanResidual_le_weight M V ψ)
  refine (add_le_add initial (mul_le_mul_of_nonneg_left residual
    (div_nonneg (by norm_num) (sub_nonneg.mpr M.β_lt_one.le)))).trans_eq ?_
  unfold comparatorBound
  ring

/-- A constant weight recovers the unweighted approximation coefficient. -/
theorem comparatorBound_unitWeight [Nonempty S] [Nonempty A] (μ : S → A) (ν V : S → ℝ)
    (hν : IsDistribution ν) :
    comparatorBound M μ ν V (unitWeight S) =
      (3 + M.β) / (1 - M.β) * ‖optimalCost M - V‖ := by
  have hβ : drift M (unitWeight S) = 1 := by
    simp [drift, unitWeight, M.P_rowsum]
  have hπ := (occupancy_isDistribution M μ hν).sum_eq_one
  rw [comparatorBound, hβ]
  simp only [weightedSup, unitWeight, div_one, mul_one, dotProduct,
    hν.sum_eq_one, hπ]
  field_simp [sub_ne_zero.mpr M.β_lt_one.ne']
  ring

end Kadp.Weighted
