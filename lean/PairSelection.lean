import Exchange

/-! The two searches in §4.1 suffice to minimize the two-coordinate slope in (21).
    In each pair, p receives mass and q donates it. -/

namespace Kadp
open Finset

variable {I A : Type*} [Fintype I] [Fintype A]

def IsLegalExchange (l : I → A → ℝ) (cap : ℝ) (p q : I × A) : Prop :=
  0 < l q.1 q.2 ∧ (p.1 = q.1 ∨ ∑ a, l p.1 a < cap)

def exchangeSlope (c : I → A → ℝ) (p q : I × A) : ℝ :=
  c p.1 p.2 - c q.1 q.2

/-- Step 2 uses the cheapest coordinate in any unfilled row and the costliest
    positive donor overall. Step 3 uses the corresponding extrema in one full row. -/
def IsPairSearchCandidate (c l : I → A → ℝ) (cap : ℝ) (p q : I × A) : Prop :=
  0 < l q.1 q.2 ∧
    (((∑ a, l p.1 a) < cap ∧
      (∀ i a, (∑ b, l i b) < cap → c p.1 p.2 ≤ c i a) ∧
      (∀ j b, 0 < l j b → c j b ≤ c q.1 q.2)) ∨
    (p.1 = q.1 ∧ (∑ a, l p.1 a) = cap ∧
      (∀ a, c p.1 p.2 ≤ c p.1 a) ∧
      (∀ b, 0 < l q.1 b → c q.1 b ≤ c q.1 q.2)))

omit [Fintype I] in
theorem IsPairSearchCandidate.legal {c l : I → A → ℝ} {cap : ℝ} {p q : I × A}
    (h : IsPairSearchCandidate c l cap p q) : IsLegalExchange l cap p q := by
  rcases h with ⟨hq, hu | hf⟩
  · exact ⟨hq, Or.inr hu.1⟩
  · exact ⟨hq, Or.inl hf.1⟩

/-- Every legal pair is dominated by the extrema from one of the two searches,
    including when all rows are full or when extrema are tied. -/
theorem exists_pair_search_candidate_le (c l : I → A → ℝ) {cap : ℝ}
    (hcap : ∀ i, ∑ a, l i a ≤ cap) {p q : I × A} (h : IsLegalExchange l cap p q) :
    ∃ r s, IsPairSearchCandidate c l cap r s ∧ exchangeSlope c r s ≤ exchangeSlope c p q := by
  classical
  rcases p with ⟨i, a⟩
  rcases q with ⟨j, b⟩
  obtain ⟨hb, hrow⟩ := h
  let score := fun x : I × A => c x.1 x.2
  by_cases hroom : (∑ t, l i t) < cap
  · let receivers := univ.filter fun x : I × A => (∑ t, l x.1 t) < cap
    let donors := univ.filter fun x : I × A => 0 < l x.1 x.2
    have hrecv : (i, a) ∈ receivers := mem_filter.mpr ⟨mem_univ _, hroom⟩
    have hdon : (j, b) ∈ donors := mem_filter.mpr ⟨mem_univ _, hb⟩
    obtain ⟨r, hr, hmin⟩ := receivers.exists_min_image score ⟨_, hrecv⟩
    obtain ⟨s, hs, hmax⟩ := donors.exists_max_image score ⟨_, hdon⟩
    refine ⟨r, s, ⟨(mem_filter.mp hs).2, Or.inl ⟨(mem_filter.mp hr).2, ?_, ?_⟩⟩,
      sub_le_sub (hmin _ hrecv) (hmax _ hdon)⟩
    · exact fun k t hk => hmin (k, t) (mem_filter.mpr ⟨mem_univ _, hk⟩)
    · exact fun k t hk => hmax (k, t) (mem_filter.mpr ⟨mem_univ _, hk⟩)
  · have hij : i = j := hrow.resolve_right hroom
    subst j
    let donors := univ.filter fun t => 0 < l i t
    have hdon : b ∈ donors := mem_filter.mpr ⟨mem_univ _, hb⟩
    obtain ⟨r, _, hmin⟩ := univ.exists_min_image (c i) ⟨a, mem_univ _⟩
    obtain ⟨s, hs, hmax⟩ := donors.exists_max_image (c i) ⟨_, hdon⟩
    refine ⟨(i, r), (i, s), ⟨(mem_filter.mp hs).2, Or.inr ⟨rfl,
      le_antisymm (hcap i) (le_of_not_gt hroom), fun t => hmin t (mem_univ _), ?_⟩⟩,
      sub_le_sub (hmin a (mem_univ _)) (hmax b hdon)⟩
    exact fun t ht => hmax t (mem_filter.mpr ⟨mem_univ _, ht⟩)

/-- Whenever a legal improving exchange exists, a minimum-score candidate in
    (21) has distinct coordinates and negative slope. Its unit step minimizes
    the slope over all legal exchanges with amplitude in [0,1]. -/
theorem exists_best_pair_search_candidate (c l : I → A → ℝ) {cap : ℝ}
    (hcap : ∀ i, ∑ a, l i a ≤ cap)
    (himprove : ∃ p q, IsLegalExchange l cap p q ∧ exchangeSlope c p q < 0) :
    ∃ r s, IsPairSearchCandidate c l cap r s ∧ r ≠ s ∧ exchangeSlope c r s < 0 ∧
      ∀ p q, IsLegalExchange l cap p q → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        exchangeSlope c r s ≤ t * exchangeSlope c p q := by
  classical
  let legal := univ.filter fun x : (I × A) × (I × A) => IsLegalExchange l cap x.1 x.2
  let slope := fun x : (I × A) × (I × A) => exchangeSlope c x.1 x.2
  obtain ⟨p, q, hpq, hneg⟩ := himprove
  have hpq' : (p, q) ∈ legal := mem_filter.mpr ⟨mem_univ _, hpq⟩
  obtain ⟨x, hx, hmin⟩ := legal.exists_min_image slope ⟨_, hpq'⟩
  obtain ⟨r, s, hrs, hle⟩ := exists_pair_search_candidate_le c l hcap (mem_filter.mp hx).2
  have hrs_neg : exchangeSlope c r s < 0 := (hle.trans (hmin _ hpq')).trans_lt hneg
  have hrs_ne : r ≠ s := by
    rintro rfl
    simp [exchangeSlope] at hrs_neg
  refine ⟨r, s, hrs, hrs_ne, hrs_neg, ?_⟩
  intro u v huv t ht ht'
  rcases le_total (exchangeSlope c u v) 0 with hle' | hge
  · have hmin' := hmin (u, v) (mem_filter.mpr ⟨mem_univ _, huv⟩)
    exact (hle.trans hmin').trans (by simpa using mul_le_mul_of_nonpos_right ht' hle')
  · exact hrs_neg.le.trans (mul_nonneg ht hge)

/-- The five constraints of (20) for q = 2, with directions indexed by coordinate pairs. -/
structure TwoCoordinateDirection (l : I → A → ℝ) (cap : ℝ) (d : I × A → ℝ) : Prop where
  full_row : ∀ i, (∑ a, l i a) = cap → (∑ a, d (i, a)) ≤ 0
  zero_entry : ∀ x, l x.1 x.2 = 0 → 0 ≤ d x
  balance : ∑ x, d x = 0
  sparse : (Function.support d).ncard ≤ 2
  bound : ∀ x, |d x| ≤ 1

/-- Every negative-slope feasible direction of (20) is a scaled legal exchange. -/
theorem TwoCoordinateDirection.exists_scaled_exchange {c l : I → A → ℝ} {cap : ℝ}
    (hl : ∀ i a, 0 ≤ l i a) (hcap : ∀ i, ∑ a, l i a ≤ cap)
    {d : I × A → ℝ} (hd : TwoCoordinateDirection l cap d)
    (hneg : (∑ x : I × A, c x.1 x.2 * d x) < 0) :
    ∃ p q, IsLegalExchange l cap p q ∧ exchangeSlope c p q < 0 ∧
      0 < d p ∧ d p ≤ 1 ∧ (∑ x : I × A, c x.1 x.2 * d x) = d p * exchangeSlope c p q := by
  classical
  obtain ⟨p, q, hp, hq, hscores⟩ := exists_improving_pair_of_sum_zero d
    (fun x => c x.1 x.2) hd.balance (by simpa [mul_comm] using hneg)
  have hne : p ≠ q := fun heq => hp.not_gt (heq ▸ hq)
  have hsupp : Function.support d = {p, q} := by
    apply Set.eq_of_subset_of_ncard_le _ _ (Set.toFinite _) |>.symm
    · exact Set.insert_subset (Function.mem_support.mpr hp.ne')
        (Set.singleton_subset_iff.mpr (Function.mem_support.mpr hq.ne))
    · simpa [Set.ncard_pair hne] using hd.sparse
  have hzero (x : I × A) (hx : x ∉ ({p, q} : Finset (I × A))) : d x = 0 := by
    by_contra hn
    have hm : x ∈ Function.support d := hn
    exact hx (by simpa [hsupp] using hm)
  have hsum (f : I × A → ℝ) : (∑ x, f x * d x) = f p * d p + f q * d q := by
    calc
      _ = ∑ x ∈ {p, q}, f x * d x := (sum_subset (subset_univ _) fun x _ hx =>
        by rw [hzero x hx, mul_zero]).symm
      _ = _ := by simp [hne]
  have hbalance : d p + d q = 0 := by simpa [hd.balance] using (hsum fun _ => 1).symm
  have hdonor : 0 < l q.1 q.2 := (hl _ _).lt_of_ne fun hz => hq.not_ge (hd.zero_entry q hz.symm)
  have hrow : p.1 = q.1 ∨ (∑ a, l p.1 a) < cap := by
    by_cases heq : p.1 = q.1
    · exact Or.inl heq
    · right
      apply (hcap _).lt_of_ne
      intro hfull
      have h := hd.full_row p.1 hfull
      rw [sum_eq_single_of_mem p.2 (mem_univ _) (fun a _ ha => hzero (p.1, a)
        (by simp [ha, heq, Prod.ext_iff]))] at h
      exact hp.not_ge h
  refine ⟨p, q, ⟨hdonor, hrow⟩, sub_neg.mpr hscores, hp, (le_abs_self _).trans (hd.bound _), ?_⟩
  rw [hsum, exchangeSlope, show d q = -d p by linarith]
  ring

noncomputable def unitExchange (p q x : I × A) : ℝ := by
  classical exact (if x = p then 1 else 0) - (if x = q then 1 else 0)

theorem unitExchange_slope (c : I → A → ℝ) (p q : I × A) :
    (∑ x : I × A, c x.1 x.2 * unitExchange p q x) = exchangeSlope c p q := by
  classical
  simp [unitExchange, exchangeSlope, mul_sub, mul_ite, sum_sub_distrib]

theorem IsLegalExchange.unit_direction {l : I → A → ℝ} {cap : ℝ} {p q : I × A}
    (h : IsLegalExchange l cap p q) (hne : p ≠ q) :
    TwoCoordinateDirection l cap (unitExchange p q) := by
  classical
  obtain ⟨hpos, hrow⟩ := h
  have hsum (i : I) (z : I × A) :
      (∑ a, (if (i, a) = z then (1 : ℝ) else 0)) = if i = z.1 then 1 else 0 := by
    rcases z with ⟨j, b⟩
    by_cases hij : i = j <;> simp [Prod.ext_iff, hij]
  constructor
  · intro i hfull
    simp only [unitExchange, sum_sub_distrib, hsum]
    by_cases hi : i = p.1
    · have hj : i = q.1 := hi.trans (hrow.resolve_right (by rw [← hi, hfull]; exact lt_irrefl _))
      simp only [if_pos hi, if_pos hj, sub_self, le_refl]
    · simp only [if_neg hi]
      split_ifs <;> norm_num
  · intro x hx
    have hxq : x ≠ q := fun heq => hpos.ne' (heq ▸ hx)
    simp only [unitExchange, if_neg hxq, sub_zero]
    split_ifs <;> norm_num
  · simp [unitExchange, sum_sub_distrib]
  · have hsub : Function.support (unitExchange p q) ⊆ ({p, q} : Set (I × A)) := by
      intro x hx
      by_contra! hn
      obtain ⟨hp, hq⟩ : x ≠ p ∧ x ≠ q := by simpa using hn
      exact hx (by simp [unitExchange, hp, hq])
    exact (Set.ncard_le_ncard hsub).trans_eq (Set.ncard_pair hne)
  · intro x
    unfold unitExchange
    split_ifs <;> norm_num

/-- When (20) admits descent, the best candidate in (21) attains a slope no
    greater than the objective at any feasible direction of sparsity at most two. -/
theorem pair_search_optimal_for_two_coordinate_directions (c l : I → A → ℝ) {cap : ℝ}
    (hl : ∀ i a, 0 ≤ l i a) (hcap : ∀ i, ∑ a, l i a ≤ cap)
    (himprove : ∃ d, TwoCoordinateDirection l cap d ∧ (∑ x : I × A, c x.1 x.2 * d x) < 0) :
    ∃ p q, IsPairSearchCandidate c l cap p q ∧ p ≠ q ∧ exchangeSlope c p q < 0 ∧
      TwoCoordinateDirection l cap (unitExchange p q) ∧
      ∀ d, TwoCoordinateDirection l cap d → exchangeSlope c p q ≤ ∑ x : I × A, c x.1 x.2 * d x := by
  obtain ⟨d, hd, hneg⟩ := himprove
  obtain ⟨p, q, hleg, himp, _⟩ := hd.exists_scaled_exchange hl hcap hneg
  obtain ⟨r, s, hrs, hrs', hnegative, hbest⟩ :=
    exists_best_pair_search_candidate c l hcap ⟨p, q, hleg, himp⟩
  refine ⟨r, s, hrs, hrs', hnegative, hrs.legal.unit_direction hrs', fun e he => ?_⟩
  by_cases h : (∑ x : I × A, c x.1 x.2 * e x) < 0
  · obtain ⟨u, v, huv, _, ht, ht', hslope⟩ := he.exists_scaled_exchange hl hcap h
    exact (hbest u v huv (e u) ht.le ht').trans_eq hslope.symm
  · exact hnegative.le.trans (le_of_not_gt h)

/-- The stopping test also applies if one or both searches have no candidates. -/
theorem pair_search_descent_iff (c l : I → A → ℝ) {cap : ℝ}
    (hl : ∀ i a, 0 ≤ l i a) (hcap : ∀ i, ∑ a, l i a ≤ cap) :
    (∃ p q, IsPairSearchCandidate c l cap p q ∧ exchangeSlope c p q < 0) ↔
      ∃ d, TwoCoordinateDirection l cap d ∧ (∑ x : I × A, c x.1 x.2 * d x) < 0 := by
  constructor
  · rintro ⟨p, q, hc, hneg⟩
    have hne : p ≠ q := by rintro rfl; simp [exchangeSlope] at hneg
    exact ⟨unitExchange p q, hc.legal.unit_direction hne, (unitExchange_slope c p q).trans_lt hneg⟩
  · intro h
    obtain ⟨p, q, hc, _, hneg, _⟩ := pair_search_optimal_for_two_coordinate_directions c l hl hcap h
    exact ⟨p, q, hc, hneg⟩

end Kadp
