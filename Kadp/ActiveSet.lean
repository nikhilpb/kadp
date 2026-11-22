import Kadp.Duality
import Kadp.PairSelection

/-! Two-coordinate descent for the sampled dual quadratic program (9). -/

namespace Kadp.SampledRSALP

open Finset

variable {S A H : Type*} [Fintype S] [Fintype A] [DecidableEq S]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] {N : ℕ} (D : SampledRSALP S A H N)

/-- The gradient of the printed objective at a multiplier vector. -/
noncomputable def dualGradient (l : Fin N → A → ℝ) (i : Fin N) (a : A) : ℝ :=
  inner ℝ (D.featureDiff i a) (D.multiplierFeature l) + D.linearCoeff i a

theorem dualGradient_eq (l : Fin N → A → ℝ) (i : Fin N) (a : A) :
    D.dualGradient l i a = (∑ j, ∑ b, D.gramCoeff i a j b * l j b) + D.linearCoeff i a := by
  simp only [dualGradient, multiplierFeature, inner_sum, real_inner_smul_right, gramCoeff_inner, mul_comm]

/-- Exact restriction of (9) to a line, including its nonnegative quadratic remainder. -/
theorem dualObjective_along (l d : Fin N → A → ℝ) (t : ℝ) :
    D.dualObjective (fun i a => l i a + t * d i a) = D.dualObjective l +
      t * (∑ i, ∑ a, D.dualGradient l i a * d i a) + t ^ 2 * (‖D.multiplierFeature d‖ ^ 2 / 2) := by
  have hfeat : D.multiplierFeature (fun i a => l i a + t * d i a) =
      D.multiplierFeature l + t • D.multiplierFeature d := by
    simp only [multiplierFeature, add_smul, mul_smul, sum_add_distrib, smul_sum]
  have hlin : (∑ i, ∑ a, D.linearCoeff i a * (l i a + t * d i a)) =
      (∑ i, ∑ a, D.linearCoeff i a * l i a) + t * ∑ i, ∑ a, D.linearCoeff i a * d i a := by
    simp only [mul_add, mul_left_comm (D.linearCoeff _ _) t, sum_add_distrib, mul_sum]
  have hslope : (∑ i, ∑ a, D.dualGradient l i a * d i a) =
      inner ℝ (D.multiplierFeature l) (D.multiplierFeature d) + ∑ i, ∑ a, D.linearCoeff i a * d i a := by
    simp only [dualGradient, add_mul, sum_add_distrib, multiplierFeature, inner_sum, real_inner_smul_right]
    congr 1
    apply sum_congr rfl; intro i _
    apply sum_congr rfl; intro a _
    rw [← real_inner_comm (∑ j, ∑ b, l j b • D.featureDiff j b) (D.featureDiff i a)]
    simp only [inner_sum, real_inner_smul_right, mul_comm]
  rw [dualObjective, dualObjective, gram_quadratic_eq_norm_sq, gram_quadratic_eq_norm_sq, hfeat,
    norm_add_sq_real, norm_smul, Real.norm_eq_abs, real_inner_smul_right, mul_pow, sq_abs, hlin, hslope]
  ring

/-- The block objective in (9), up to its frozen constant. Set the frozen entries
to zero on the working set, and the free entries to zero outside it. -/
theorem dualObjective_block (frozen free : Fin N → A → ℝ) :
    D.dualObjective (fun i a => frozen i a + free i a) = D.dualObjective frozen +
      (∑ i, ∑ a, ((∑ j, ∑ b, D.gramCoeff i a j b * frozen j b) + D.linearCoeff i a) * free i a) +
      (∑ i, ∑ a, ∑ j, ∑ b, free i a * D.gramCoeff i a j b * free j b) / 2 := by
  simpa only [one_mul, one_pow, dualGradient_eq, gram_quadratic_eq_norm_sq]
    using D.dualObjective_along frozen free 1

/-- The unit exchange in (20), curried to match the sampled program's coordinates. -/
noncomputable def transfer {I A : Type*} (p q : I × A) (i : I) (a : A) : ℝ :=
  Kadp.unitExchange p q (i,a)

private theorem transfer_apply {I A : Type*} [DecidableEq I] [DecidableEq A]
    (p q : I × A) (i : I) (a : A) :
    transfer p q i a = (if i = p.1 then (if a = p.2 then 1 else 0) else 0) -
      (if i = q.1 then (if a = q.2 then 1 else 0) else 0) := by
  simp [transfer, Kadp.unitExchange, Prod.ext_iff, ite_and]

theorem transfer_support {I A : Type*} {p q : I × A} (hpq : p ≠ q) (i : I) (a : A) :
    transfer p q i a ≠ 0 ↔ (i,a) = p ∨ (i,a) = q := by
  classical
  by_cases h : (i,a) = p
  · simp [transfer, Kadp.unitExchange, h, hpq]
  · by_cases h' : (i,a) = q <;> simp [transfer, Kadp.unitExchange, h, h', Ne.symm hpq]

theorem transfer_slope {I A : Type*} [Fintype I] [Fintype A]
    (c : I → A → ℝ) (p q : I × A) :
    (∑ i, ∑ a, c i a * transfer p q i a) = c p.1 p.2 - c q.1 q.2 := by
  simpa only [Fintype.sum_prod_type, transfer, Kadp.exchangeSlope] using Kadp.unitExchange_slope c p q

theorem transfer_card {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A]
    {p q : I × A} (hpq : p ≠ q) :
    (univ.filter (fun k : I × A => transfer p q k.1 k.2 ≠ 0)).card = 2 := by
  have h : univ.filter (fun k : I × A => transfer p q k.1 k.2 ≠ 0) = {p,q} := by
    ext k
    simp [transfer_support hpq]
  simp [h, hpq]

omit [DecidableEq S] [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
/-- A positive donor and space in the receiving row suffice for all sufficiently
small transfers; within a row its total stays fixed even when that row is full. -/
theorem transfer_feasible {l : Fin N → A → ℝ} (hl : D.DualFeasible l)
    (p q : Fin N × A) (hpos : 0 < l q.1 q.2)
    (hrow : p.1 = q.1 ∨ (∑ a, l p.1 a) < D.κ / N) :
    ∃ η > 0, ∀ t : ℝ, 0 ≤ t → t ≤ η →
      D.DualFeasible (fun i a => l i a + t * transfer p q i a) := by
  classical
  let room := if p.1 = q.1 then l q.1 q.2 else D.κ / N - ∑ a, l p.1 a
  have hr : 0 < room := by
    dsimp [room]
    split_ifs with h
    · exact hpos
    · exact sub_pos.mpr (hrow.resolve_left h)
  refine ⟨min (l q.1 q.2) room, lt_min hpos hr, ?_⟩
  intro t ht hsmall
  have hdon := hsmall.trans (min_le_left _ _)
  have hrecv := hsmall.trans (min_le_right _ _)
  have hs (i : Fin N) : (∑ a, (l i a + t * transfer p q i a)) =
      (∑ a, l i a) + ((if i = p.1 then t else 0) - (if i = q.1 then t else 0)) := by
    simp [transfer_apply, mul_sub, sum_add_distrib, sum_sub_distrib, mul_ite,
      Finset.sum_ite_irrel]
  refine ⟨?_, ?_, ?_⟩
  · intro i a
    have hnon := hl.1 i a
    by_cases hi : i = q.1 <;> by_cases ha : a = q.2 <;>
      simp [transfer_apply, hi, ha] <;> split_ifs <;> simp_all <;> linarith
  · intro i
    rw [hs]
    by_cases heq : p.1 = q.1
    · simpa [heq] using hl.2.1 i
    · have hroom : t ≤ D.κ / N - ∑ a, l p.1 a := by simpa [room, heq] using hrecv
      by_cases hi : i = p.1
      · subst i; simp [heq]; linarith
      · by_cases hj : i = q.1
        · subst i; simp [Ne.symm heq]; linarith [hl.2.1 q.1]
        · simpa [hi, hj] using hl.2.1 i
  · simp only [hs, sum_add_distrib, sum_sub_distrib]
    simp [hl.2.2]

/-- Negative pair slope gives an interval of feasible, strictly improving steps. -/
theorem descent_of_improving_transfer {l : Fin N → A → ℝ} (hl : D.DualFeasible l)
    (p q : Fin N × A) (hpos : 0 < l q.1 q.2)
    (hrow : p.1 = q.1 ∨ (∑ a, l p.1 a) < D.κ / N)
    (hgrad : D.dualGradient l p.1 p.2 < D.dualGradient l q.1 q.2) :
    ∃ η > 0, ∀ t : ℝ, 0 < t → t ≤ η →
      D.DualFeasible (fun i a => l i a + t * transfer p q i a) ∧
      D.dualObjective (fun i a => l i a + t * transfer p q i a) < D.dualObjective l := by
  obtain ⟨room, hr, hfeas⟩ := D.transfer_feasible hl p q hpos hrow
  let curvature := ‖D.multiplierFeature (transfer p q)‖ ^ 2 / 2
  have hc : 0 ≤ curvature := by dsimp [curvature]; positivity
  obtain ⟨s, hs, hsmall⟩ := exists_pos_mul_lt (sub_pos.mpr hgrad) curvature
  refine ⟨min room s, lt_min hr hs, fun t ht htη => ⟨hfeas t ht.le (htη.trans (min_le_left _ _)), ?_⟩⟩
  have h := (mul_le_mul_of_nonneg_left (htη.trans (min_le_right _ _)) hc).trans_lt hsmall
  rw [dualObjective_along, transfer_slope]
  have hneg : t * ((D.dualGradient l p.1 p.2 - D.dualGradient l q.1 q.2) + curvature * t) < 0 :=
    mul_neg_of_pos_of_neg ht (by linarith)
  change _ + _ + t ^ 2 * curvature < _
  linarith only [hneg]

/-- A strictly cheaper feasible vector gives a feasible pair with smaller gradient
at the receiving coordinate. The certificate is expressed in the scale of (9). -/
theorem exists_improving_transfer [Nonempty A] {l k : Fin N → A → ℝ}
    (hl : D.DualFeasible l) (hk : D.DualFeasible k) (hlt : D.dualObjective k < D.dualObjective l) :
    ∃ p q : Fin N × A, p ≠ q ∧ 0 < l q.1 q.2 ∧
      (p.1 = q.1 ∨ (∑ a, l p.1 a) < D.κ / N) ∧
      D.dualGradient l p.1 p.2 < D.dualGradient l q.1 q.2 := by
  let d := fun i a => k i a - l i a
  have he := D.dualObjective_along l d 1
  have hline : (fun i a => l i a + 1 * d i a) = k := by
    funext i a; dsimp [d]; ring
  rw [hline, one_pow, one_mul, one_mul] at he
  have hslope : (∑ i, ∑ a, D.dualGradient l i a * (k i a - l i a)) < 0 := by
    linarith only [he, hlt, sq_nonneg (‖D.multiplierFeature d‖)]
  obtain ⟨i,a,j,b,hne,hpos,hgrad,hrow⟩ := Kadp.exists_capped_exchange
    (D.dualGradient l) l k hl.1 hk.1 hk.2.1 (hk.2.2.trans hl.2.2.symm) hslope
  exact ⟨(i,a),(j,b),hne,hpos,hrow,hgrad⟩

/-- Proposition 2. The direction has exactly two nonzero entries, +1 and −1
(see transfer_support), and every sufficiently small positive step improves (9). -/
theorem proposition2 [Nonempty A] {l : Fin N → A → ℝ} (hl : D.DualFeasible l)
    (hsub : ∃ k, D.DualFeasible k ∧ D.dualObjective k < D.dualObjective l) :
    ∃ p q : Fin N × A, p ≠ q ∧ ∃ η > 0, ∀ t : ℝ, 0 < t → t ≤ η →
      D.DualFeasible (fun i a => l i a + t * transfer p q i a) ∧
      D.dualObjective (fun i a => l i a + t * transfer p q i a) < D.dualObjective l := by
  obtain ⟨k,hk,hlt⟩ := hsub
  obtain ⟨p,q,hne,hpos,hrow,hgrad⟩ := D.exists_improving_transfer hl hk hlt
  exact ⟨p,q,hne,D.descent_of_improving_transfer hl p q hpos hrow hgrad⟩

/-- At a suboptimal feasible point, the extreme-score pair search of §4.1
selects a pair that strictly decreases the actual objective (9). -/
theorem exists_improving_search_candidate [Nonempty A] {l : Fin N → A → ℝ}
    (hl : D.DualFeasible l) (hsub : ∃ k, D.DualFeasible k ∧ D.dualObjective k < D.dualObjective l) :
    ∃ p q : Fin N × A, Kadp.IsPairSearchCandidate (D.dualGradient l) l (D.κ/N) p q ∧ p ≠ q ∧
      ∃ η > 0, ∀ t : ℝ, 0 < t → t ≤ η →
        D.DualFeasible (fun i a => l i a + t * transfer p q i a) ∧
        D.dualObjective (fun i a => l i a + t * transfer p q i a) < D.dualObjective l := by
  obtain ⟨k,hk,hlt⟩ := hsub
  obtain ⟨u,v,_,hd,hr,hg⟩ := D.exists_improving_transfer hl hk hlt
  obtain ⟨p,q,hc,hne,hneg,_⟩ := Kadp.exists_best_pair_search_candidate (D.dualGradient l) l hl.2.1
    ⟨u,v,⟨hd,hr⟩, sub_neg.mpr hg⟩
  exact ⟨p,q,hc,hne,D.descent_of_improving_transfer hl p q hc.legal.1 hc.legal.2 (sub_neg.mp hneg)⟩

/-- The absence of an improving legal transfer is a global optimality certificate. -/
theorem optimal_iff_no_improving_transfer [Nonempty A] {l : Fin N → A → ℝ} (hl : D.DualFeasible l) :
    (∀ k, D.DualFeasible k → D.dualObjective l ≤ D.dualObjective k) ↔
      ∀ p q : Fin N × A, 0 < l q.1 q.2 →
        (p.1 = q.1 ∨ (∑ a, l p.1 a) < D.κ / N) →
        D.dualGradient l q.1 q.2 ≤ D.dualGradient l p.1 p.2 := by
  constructor
  · intro hmin p q hpos hrow
    by_contra! hgrad
    obtain ⟨η,hη,h⟩ := D.descent_of_improving_transfer hl p q hpos hrow hgrad
    obtain ⟨hf,hd⟩ := h η hη le_rfl
    exact hd.not_ge (hmin _ hf)
  · intro hall k hk
    by_contra! hlt
    obtain ⟨p,q,_,hpos,hrow,hgrad⟩ := D.exists_improving_transfer hl hk hlt
    exact hgrad.not_ge (hall p q hpos hrow)

end Kadp.SampledRSALP
