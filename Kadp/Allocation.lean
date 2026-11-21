import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith

/-! Fill rows up to a common cap in increasing order of their costs.
    Rows tied at the cutoff share the remaining mass. -/

namespace Kadp
open Finset

private theorem exists_capacity_cutoff {I : Type*} [Fintype I] [Nonempty I]
    (r : I → ℝ) {q M : ℝ} (hM : 0 < M) (hcap : M ≤ Fintype.card I * q) :
    ∃ u : ℝ, (∑ i, if r i < u then q else 0) < M ∧
      M ≤ ∑ i, if r i ≤ u then q else 0 := by
  classical
  let good := univ.filter fun i => M ≤ ∑ j, if r j ≤ r i then q else 0
  obtain ⟨last, _, hlast⟩ := univ.exists_max_image r univ_nonempty
  have hg : last ∈ good := by
    simp [good, hlast, nsmul_eq_mul, hcap]
  obtain ⟨cut, hcut, hmin⟩ := good.exists_min_image r ⟨last, hg⟩
  refine ⟨r cut, ?_, (mem_filter.mp hcut).2⟩
  let cheaper := univ.filter fun i => r i < r cut
  by_cases h : cheaper.Nonempty
  · obtain ⟨prev, hprev, hmax⟩ := cheaper.exists_max_image r h
    have hlt := (mem_filter.mp hprev).2
    have hbad : prev ∉ good := fun hp => (not_le_of_gt hlt) (hmin prev hp)
    have hequiv (i : I) : r i < r cut ↔ r i ≤ r prev :=
      ⟨fun hi => hmax i (mem_filter.mpr ⟨mem_univ _, hi⟩), fun hi => hi.trans_lt hlt⟩
    simpa [good, hequiv] using hbad
  · have hnone (i : I) : ¬ r i < r cut :=
      fun hi => h ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩
    simpa [hnone] using hM

/-- An allocation attaining the cutoff cost, together with the nonnegative
    slacks certifying that cost. The statement allows ties and full capacity. -/
theorem exists_cutoff_allocation {I A : Type*} [Fintype I] [Nonempty I]
    [Fintype A] [Nonempty A] (c : I → A → ℝ) {q M : ℝ}
    (hq : 0 ≤ q) (hM : 0 < M) (hcap : M ≤ Fintype.card I * q) :
    ∃ (u : ℝ) (s : I → ℝ) (t : I → A → ℝ),
      (∀ i, 0 ≤ s i) ∧ (∀ i a, u ≤ c i a + s i) ∧
      (∀ i a, 0 ≤ t i a) ∧ (∀ i, ∑ a, t i a ≤ q) ∧
      (∑ i, ∑ a, t i a) = M ∧
      (∑ i, ∑ a, t i a * c i a) = u * M - q * ∑ i, s i := by
  classical
  choose best _ hbest using fun i => univ.exists_min_image (c i) univ_nonempty
  let r := fun i => c i (best i)
  obtain ⟨u, hlo, hhi⟩ := exists_capacity_cutoff r hM hcap
  let lo := fun i => if r i < u then q else 0
  let hi := fun i => if r i ≤ u then q else 0
  let L := ∑ i, lo i
  let U := ∑ i, hi i
  have hL : L < M := hlo
  have hU : M ≤ U := hhi
  let θ := (M - L) / (U - L)
  have hUL : 0 < U - L := sub_pos.mpr (hL.trans_le hU)
  have hθ : 0 ≤ θ := div_nonneg (sub_nonneg.mpr hL.le) hUL.le
  have hθ₁ : θ ≤ 1 := (div_le_one hUL).mpr (by linarith)
  let w := fun i => lo i + θ * (hi i - lo i)
  have hsum : (∑ i, w i) = M := by
    change (∑ i, (lo i + θ * (hi i - lo i))) = M
    rw [sum_add_distrib, ← mul_sum, sum_sub_distrib]
    change L + θ * (U - L) = M
    rw [show θ * (U - L) = M - L from div_mul_cancel₀ _ hUL.ne']
    ring
  let s := fun i => max (u - r i) 0
  have hrow (i : I) : 0 ≤ w i ∧ w i ≤ q ∧ w i * r i = u * w i - q * s i := by
    rcases lt_trichotomy (r i) u with h | h | h
    · simp [w, lo, hi, h, h.le, s, hq]
      ring
    · simp [w, lo, hi, h, s, mul_comm]
      exact ⟨mul_nonneg hq hθ, mul_le_of_le_one_right hq hθ₁⟩
    · simp [w, lo, hi, h.not_gt, h.not_ge, s, max_eq_right (sub_nonpos.mpr h.le), hq]
  let t := fun i a => if best i = a then w i else 0
  have hmass (i : I) : ∑ a, t i a = w i := by simp [t]
  refine ⟨u, s, t, fun i => le_max_right _ _, ?_, ?_, ?_, ?_, ?_⟩
  · intro i a
    have hmin : r i ≤ c i a := hbest i a (mem_univ _)
    have hs : u - r i ≤ s i := le_max_left _ _
    linarith
  · intro i a
    dsimp [t]
    split
    · exact (hrow i).1
    · exact le_rfl
  · intro i
    rw [hmass]
    exact (hrow i).2.1
  · simpa only [hmass] using hsum
  · calc
      (∑ i, ∑ a, t i a * c i a) = ∑ i, w i * r i := by simp [t, r, ite_mul]
      _ = ∑ i, (u * w i - q * s i) := sum_congr rfl fun i _ => (hrow i).2.2
      _ = _ := by rw [sum_sub_distrib, ← mul_sum, ← mul_sum, hsum]

end Kadp
