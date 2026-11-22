import MarkovDecisionProcesses.MDP
import Mathlib.LinearAlgebra.Matrix.Stochastic

/-! Discounted state occupancy (17) and the signed Bellman residual for any fixed policy.
Distributions multiply on the left, and costs on the right. -/

namespace Kadp.Occupancy

open Matrix SargentStachurski.MarkovDecisionProcesses

variable {S A : Type*} [Fintype S] [Fintype A]

/-- The paper allows all actions. The upstream MDP uses rewards, so put `r = -g`. -/
def ofCosts [Nonempty A] (α : ℝ) (hα : 0 < α) (hα' : α < 1)
    (g : S → A → ℝ) (p : S → A → S → ℝ)
    (hp : ∀ x a y, 0 ≤ p x a y) (hrow : ∀ x a, ∑ y, p x a y = 1) : MDP S A where
  Γ := fun _ => Finset.univ
  Γ_nonempty := fun _ => Finset.univ_nonempty
  β := α
  β_pos := hα
  β_lt_one := hα'
  r := fun x a => -g x a
  P := p
  P_nonneg := hp
  P_rowsum := hrow

variable (M : MDP S A) (μ : S → A)

noncomputable def costBellman (J : S → ℝ) : S → ℝ :=
  -M.rσ μ + M.β • (M.Pσ μ *ᵥ J)

noncomputable def policyCost : S → ℝ := -M.vσ μ

theorem costBellman_eq_neg_reward (J : S → ℝ) :
    costBellman M μ J = -M.Tσ μ (-J) := by
  simp [costBellman, M.Tσ_eq, mulVec_neg, neg_add_rev, add_comm]

theorem costBellman_policyCost : costBellman M μ (policyCost M μ) = policyCost M μ := by
  rw [costBellman_eq_neg_reward, policyCost, neg_neg, (M.isFixedPt_vσ μ).eq]

theorem policyCost_unique (J : S → ℝ) (hJ : costBellman M μ J = J) : J = policyCost M μ := by
  rw [costBellman_eq_neg_reward, neg_eq_iff_eq_neg] at hJ
  exact neg_eq_iff_eq_neg.mp (M.eq_vσ_of_isFixedPt μ hJ)

variable [DecidableEq S]

/-- Equation (17), written as a row vector. -/
noncomputable def discountedOccupancy (ν : S → ℝ) : S → ℝ :=
  (1 - M.β) • (ν ᵥ* (1 - M.β • M.Pσ μ)⁻¹)

/-- Evaluate a single-state indicator with the upstream policy evaluation theorems.
The resulting discounted visits give one entry of the inverse. -/
private theorem hasSum_entry (x y : S) :
    HasSum (fun t : ℕ => M.β ^ t * (M.Pσ μ ^ t) x y) ((1 - M.β • M.Pσ μ)⁻¹ x y) := by
  let visits := { M with r := fun z _ => (Pi.single y 1 : S → ℝ) z }
  have hs := (visits.summable_pow_smul_mulVec μ).hasSum
  rw [← visits.vσ_eq_tsum μ, visits.vσ_eq_inv μ] at hs
  change HasSum (fun t : ℕ => M.β ^ t • ((M.Pσ μ ^ t) *ᵥ Pi.single y 1))
    ((1 - M.β • M.Pσ μ)⁻¹ *ᵥ Pi.single y 1) at hs
  simp only [mulVec_single_one] at hs
  exact Pi.hasSum.mp hs x

/-- The discounted series converges to the inverse formula, including for signed initial rows. -/
theorem hasSum_occupancy (ν : S → ℝ) :
    HasSum (fun t : ℕ => ((1 - M.β) * M.β ^ t) • (ν ᵥ* M.Pσ μ ^ t))
      (discountedOccupancy M μ ν) := by
  apply Pi.hasSum.mpr
  intro y
  have hs := hasSum_sum (s := Finset.univ) fun x _ => (hasSum_entry M μ x y).mul_left (ν x)
  apply (hs.mul_left (1 - M.β)).congr_fun
  intro t
  simp only [Pi.smul_apply, smul_eq_mul, vecMul, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

private theorem balance_iff (ν w : S → ℝ) :
    w = (1 - M.β) • ν + M.β • (w ᵥ* M.Pσ μ) ↔
      w ᵥ* (1 - M.β • M.Pσ μ) = (1 - M.β) • ν := by
  rw [vecMul_sub, vecMul_one, vecMul_smul, sub_eq_iff_eq_add]

theorem occupancy_balance (ν : S → ℝ) :
    discountedOccupancy M μ ν =
      (1 - M.β) • ν + M.β • (discountedOccupancy M μ ν ᵥ* M.Pσ μ) := by
  apply (balance_iff M μ _ _).mpr
  rw [discountedOccupancy, smul_vecMul, vecMul_vecMul, nonsing_inv_mul, vecMul_one]
  exact (isUnit_iff_isUnit_det _).mp (M.isUnit_one_sub_smul_Pσ μ)

theorem occupancy_unique (ν w : S → ℝ)
    (hw : w = (1 - M.β) • ν + M.β • (w ᵥ* M.Pσ μ)) : w = discountedOccupancy M μ ν := by
  have h := congrArg (fun v => v ᵥ* (1 - M.β • M.Pσ μ)⁻¹) ((balance_iff M μ ν w).mp hw)
  simpa only [vecMul_vecMul, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp
    (M.isUnit_one_sub_smul_Pσ μ)), vecMul_one, smul_vecMul, discountedOccupancy] using h

theorem occupancy_isDistribution {ν : S → ℝ} (hν : IsDistribution ν) :
    IsDistribution (discountedOccupancy M μ ν) := by
  have hP : M.Pσ μ ∈ rowStochastic ℝ S :=
    mem_rowStochastic_iff_sum.mpr ⟨(M.isMarkov_Pσ μ).nonneg, (M.isMarkov_Pσ μ).rowsum⟩
  let π := discountedOccupancy M μ ν
  constructor
  · intro y
    apply HasSum.nonneg _ (Pi.hasSum.mp (hasSum_occupancy M μ ν) y)
    intro t
    exact mul_nonneg (mul_nonneg (sub_nonneg.mpr M.β_lt_one.le) (pow_nonneg M.β_pos.le _))
      (nonneg_vecMul_of_mem_rowStochastic ((rowStochastic ℝ S).pow_mem hP t) hν.nonneg y)
  · have h := congrArg (fun v : S → ℝ => v ⬝ᵥ 1) (occupancy_balance M μ ν)
    change π ⬝ᵥ 1 = ((1 - M.β) • ν + M.β • (π ᵥ* M.Pσ μ)) ⬝ᵥ 1 at h
    simp only [add_dotProduct, smul_dotProduct, smul_eq_mul, ← dotProduct_mulVec,
      one_vecMul_of_mem_rowStochastic hP] at h
    simp only [dotProduct, Pi.one_apply, mul_one, hν.sum_eq_one] at h
    change ∑ x, π x = 1
    apply mul_left_cancel₀ (sub_ne_zero.mpr M.β_lt_one.ne' : 1 - M.β ≠ 0)
    linarith only [h]

/-- The signed initial value error equals the occupancy-weighted one-step residual,
with the paper's cost convention and normalization. -/
theorem residual_identity (ν J : S → ℝ) :
    ν ⬝ᵥ (J - policyCost M μ) =
      (discountedOccupancy M μ ν ⬝ᵥ (J - costBellman M μ J)) / (1 - M.β) := by
  have hres : (1 - M.β • M.Pσ μ) *ᵥ (J - policyCost M μ) = J - costBellman M μ J := by
    have hfixed := costBellman_policyCost M μ
    unfold costBellman at hfixed ⊢
    rw [sub_mulVec, one_mulVec, smul_mulVec, mulVec_sub, smul_sub]
    rw [← sub_eq_iff_eq_add'.mpr hfixed.symm]
    abel
  have hbal := (balance_iff M μ _ _).mp (occupancy_balance M μ ν)
  apply (eq_div_iff (sub_ne_zero.mpr M.β_lt_one.ne')).mpr
  rw [← hres, dotProduct_mulVec, hbal, smul_dotProduct, smul_eq_mul, mul_comm]

end Kadp.Occupancy
