import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith

/-! Improving exchanges for the capped simplex in Proposition 2. -/

namespace Kadp
open Finset

/-- Lemma 4. A mass-preserving change of negative cost moves some mass
    toward a strictly cheaper coordinate. -/
theorem exists_improving_pair_of_sum_zero {I : Type*} [Fintype I] (x y : I → ℝ)
    (hsum : ∑ i, x i = 0) (hcost : ∑ i, x i * y i < 0) :
    ∃ i j, 0 < x i ∧ x j < 0 ∧ y i < y j := by
  classical
  let gains := univ.filter fun i => 0 < x i
  have hgain : gains.Nonempty := by
    by_contra hempty
    have hnonpos (i : I) : x i ≤ 0 :=
      le_of_not_gt fun hi => hempty ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩
    have hzero := (sum_eq_zero_iff_of_nonpos (fun i _ => hnonpos i)).mp hsum
    simp [fun i => hzero i (mem_univ _)] at hcost
  obtain ⟨p, hp, hmin⟩ := gains.exists_min_image y hgain
  have hp_pos := (mem_filter.mp hp).2
  by_contra! hno
  have hlower (i : I) : x i * y p ≤ x i * y i := by
    rcases lt_trichotomy (x i) 0 with hi | hi | hi
    · exact mul_le_mul_of_nonpos_left (hno p i hp_pos hi) hi.le
    · simp [hi]
    · exact mul_le_mul_of_nonneg_left (hmin i (mem_filter.mpr ⟨mem_univ _, hi⟩)) hi.le
  have h := sum_le_sum fun i (_ : i ∈ univ) => hlower i
  rw [← sum_mul, hsum, zero_mul] at h
  exact hcost.not_ge h

/-- A cheaper feasible comparison allocation certifies an improving two-coordinate
    transfer. A transfer between rows needs spare capacity in the recipient row. -/
theorem exists_capped_exchange {I A : Type*} [Fintype I] [Fintype A] [Nonempty A]
    (c l k : I → A → ℝ) {cap : ℝ} (hl : ∀ i a, 0 ≤ l i a) (hk : ∀ i a, 0 ≤ k i a)
    (hkcap : ∀ i, ∑ a, k i a ≤ cap) (hmass : (∑ i, ∑ a, k i a) = ∑ i, ∑ a, l i a)
    (hcost : (∑ i, ∑ a, c i a * (k i a - l i a)) < 0) :
    ∃ i a j b, (i, a) ≠ (j, b) ∧ 0 < l j b ∧ c i a < c j b ∧
      (i = j ∨ ∑ a, l i a < cap) := by
  classical
  by_contra hno
  have noExchange (i : I) (a : A) (j : I) (b : A) (hb : 0 < l j b)
      (hrow : i = j ∨ ∑ t, l i t < cap) : c j b ≤ c i a := by
    by_contra! hlt
    have hne : (i, a) ≠ (j, b) := fun heq =>
      hlt.ne (congrArg (fun p : I × A => c p.1 p.2) heq)
    exact hno ⟨i, a, j, b, hne, hb, hlt, hrow⟩
  choose best _ hbest using fun i => univ.exists_min_image (c i) univ_nonempty
  let r := fun i => c i (best i)
  have hmin (i : I) (a : A) : r i ≤ c i a := hbest i a (mem_univ _)
  have hsupport (i : I) (a : A) (ha : 0 < l i a) : c i a = r i :=
    le_antisymm (noExchange i (best i) i a ha (Or.inl rfl)) (hmin i a)
  let d := fun i => (∑ a, k i a) - ∑ a, l i a
  have hsum : ∑ i, d i = 0 := by simp [d, sum_sub_distrib, hmass]
  have hlower (i : I) : d i * r i ≤ ∑ a, c i a * (k i a - l i a) := by
    rw [show d i * r i = ∑ a, r i * (k i a - l i a) by
      rw [← mul_sum, sum_sub_distrib, mul_comm]]
    apply sum_le_sum
    intro a _
    rcases (hl i a).eq_or_lt with ha | ha
    · simpa [← ha] using mul_le_mul_of_nonneg_right (hmin i a) (hk i a)
    · rw [hsupport i a ha]
  obtain ⟨i, j, hi, hj, hlt⟩ := exists_improving_pair_of_sum_zero d r hsum
    (lt_of_le_of_lt (sum_le_sum fun i _ => hlower i) hcost)
  have hroom : (∑ a, l i a) < cap := (sub_pos.mp hi).trans_le (hkcap i)
  obtain ⟨b, _, hb⟩ := exists_lt_of_sum_lt (sub_neg.mp hj)
  have hb_pos := (hk j b).trans_lt hb
  exact hlt.not_ge ((hsupport j b hb_pos) ▸ noExchange i (best i) j b hb_pos (Or.inr hroom))

end Kadp
