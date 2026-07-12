/-
Copyright (c) 2026 Walid K. Elkersh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Walid K. Elkersh
-/
import Mathlib
import Ringel.Primitives

/-!
# Cyclic intervals and colour classes in the ND-colouring (MPS §7)

Arithmetic infrastructure for the Case C embedding (`Lemma_small_tree` of `arXiv:2001.02665`):

* `cyclicShift n a j` — the vertex `a + j` in the cyclic order on `Fin (2n+1)`;
* `cyclicInterval n a len` — the cyclic interval `{a, a+1, …, a+len-1}`;
* `colourClass n k r` — colours `c` whose *value* `c+1` is even and `≡ r (mod 2k+1)`;
* `exists_even_residue_in_window` — every window of `2(2k+1)` consecutive integers contains an
  even integer `≡ r (mod 2k+1)`;
* `ndColouring_sweep` — the colour value of `s(v, v+d)` is `min d (2n+1-d)`;
* `card_pred_nbrs_in_cyclicInterval` — a vertex `v` outside a cyclic interval `I` has at least
  `|I|/D - 2` neighbours inside `I` whose colour value satisfies a predicate `Pcol`, provided
  every window of `D` consecutive integers contains a `Pcol`-value.  The point: since `v ∉ I`,
  the forward distance from `v` sweeps through `|I|` consecutive values in `[1, 2n]` without
  wrapping, so the colour value is piecewise a run of consecutive integers with at most one
  "fold" at `n`; every full window of `D` consecutive values inside a run contains a witness.
* `card_class_nbrs_in_cyclicInterval`, `card_odd_nbrs_in_cyclicInterval` — the two
  instantiations used in `Lemma_small_tree`: colour classes `C^r` (window `2(2k+1)`) and
  odd colours (window `2`).
-/

namespace Ringel

/-- The `j`-th cyclic successor of `a` in `Fin (2 * n + 1)`. -/
def cyclicShift (n : ℕ) (a : Fin (2 * n + 1)) (j : ℕ) : Fin (2 * n + 1) :=
  a + ⟨j % (2 * n + 1), Nat.mod_lt _ (by omega)⟩

@[simp] lemma cyclicShift_val (n : ℕ) (a : Fin (2 * n + 1)) (j : ℕ) :
    (cyclicShift n a j).val = (a.val + j) % (2 * n + 1) := by
  change (a.val + j % (2 * n + 1)) % (2 * n + 1) = (a.val + j) % (2 * n + 1)
  exact Nat.add_mod_mod _ _ _

@[simp] lemma cyclicShift_zero (n : ℕ) (a : Fin (2 * n + 1)) : cyclicShift n a 0 = a := by
  apply Fin.ext
  rw [cyclicShift_val, Nat.add_zero, Nat.mod_eq_of_lt a.isLt]

lemma cyclicShift_cyclicShift (n : ℕ) (a : Fin (2 * n + 1)) (i j : ℕ) :
    cyclicShift n (cyclicShift n a i) j = cyclicShift n a (i + j) := by
  apply Fin.ext
  rw [cyclicShift_val, cyclicShift_val, cyclicShift_val, Nat.mod_add_mod, Nat.add_assoc]

/-- Any vertex `u` is the shift of `v` by the cyclic distance from `v` to `u`. -/
lemma cyclicShift_dist (n : ℕ) (v a : Fin (2 * n + 1)) :
    cyclicShift n v ((a.val + (2 * n + 1) - v.val) % (2 * n + 1)) = a := by
  apply Fin.ext
  have hv := v.isLt
  rw [cyclicShift_val, Nat.add_mod_mod,
    show v.val + (a.val + (2 * n + 1) - v.val) = a.val + (2 * n + 1) by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt a.isLt]

lemma cyclicShift_injOn (n : ℕ) (a : Fin (2 * n + 1)) {j₁ j₂ : ℕ}
    (h1 : j₁ < 2 * n + 1) (h2 : j₂ < 2 * n + 1)
    (h : cyclicShift n a j₁ = cyclicShift n a j₂) : j₁ = j₂ := by
  have hv : (a.val + j₁) % (2 * n + 1) = (a.val + j₂) % (2 * n + 1) := by
    rw [← cyclicShift_val, ← cyclicShift_val, h]
  exact Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.add_left_cancel' a.val hv) h1 h2

/-- The cyclic interval `{a, a+1, …, a+(len-1)}` in `Fin (2 * n + 1)`. -/
def cyclicInterval (n : ℕ) (a : Fin (2 * n + 1)) (len : ℕ) : Finset (Fin (2 * n + 1)) :=
  (Finset.range len).image (cyclicShift n a)

lemma mem_cyclicInterval {n : ℕ} {a : Fin (2 * n + 1)} {len : ℕ} {u : Fin (2 * n + 1)} :
    u ∈ cyclicInterval n a len ↔ ∃ j < len, cyclicShift n a j = u := by
  simp [cyclicInterval]

lemma card_cyclicInterval (n : ℕ) (a : Fin (2 * n + 1)) {len : ℕ} (hlen : len ≤ 2 * n + 1) :
    (cyclicInterval n a len).card = len := by
  rw [cyclicInterval, Finset.card_image_of_injOn, Finset.card_range]
  intro j₁ h1 j₂ h2 h
  simp only [Finset.coe_range, Set.mem_Iio] at h1 h2
  exact cyclicShift_injOn n a (lt_of_lt_of_le h1 hlen) (lt_of_lt_of_le h2 hlen) h

/-- Colour class `C^r`: colours `c : Fin n` whose value `c+1` is even and `≡ r (mod 2k+1)`. -/
def colourClass (n k r : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun c => (c.val + 1) % 2 = 0 ∧ (c.val + 1) % (2 * k + 1) = r

/-- The odd colours: value `c+1` odd. -/
def oddColourClass (n : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun c => (c.val + 1) % 2 = 1

lemma mem_colourClass {n k r : ℕ} {c : Fin n} :
    c ∈ colourClass n k r ↔ (c.val + 1) % 2 = 0 ∧ (c.val + 1) % (2 * k + 1) = r := by
  simp [colourClass]

lemma mem_oddColourClass {n : ℕ} {c : Fin n} :
    c ∈ oddColourClass n ↔ (c.val + 1) % 2 = 1 := by
  simp [oddColourClass]

/-- Every window of `2(2k+1)` consecutive integers contains an even integer that is
`≡ r (mod 2k+1)`. (CRT for the coprime moduli `2` and `2k+1`.) -/
lemma exists_even_residue_in_window (x k r : ℕ) (hr : r < 2 * k + 1) :
    ∃ m, x ≤ m ∧ m < x + 2 * (2 * k + 1) ∧ m % 2 = 0 ∧ m % (2 * k + 1) = r := by
  set P := 2 * (2 * k + 1) with hP
  have hP0 : 0 < P := by omega
  set m₀ := r * (2 * k + 2) with hm₀
  have hxP : x % P < P := Nat.mod_lt _ hP0
  set t := (m₀ + P - x % P) % P with ht
  have htP : t < P := Nat.mod_lt _ hP0
  have hle : x % P ≤ x := Nat.mod_le x P
  have hdm : P * (x / P) + x % P = x := Nat.div_add_mod x P
  have key : (x + t) % P = m₀ % P := by
    rw [ht, Nat.add_mod_mod,
      show x + (m₀ + P - x % P) = P * (x / P) + (m₀ + P) by omega,
      Nat.mul_add_mod, Nat.add_mod_right]
  have h2 : (x + t) % 2 = m₀ % 2 := by
    have d2 : (2 : ℕ) ∣ P := ⟨2 * k + 1, by ring⟩
    rw [← Nat.mod_mod_of_dvd (x + t) d2, key, Nat.mod_mod_of_dvd m₀ d2]
  have h3 : (x + t) % (2 * k + 1) = m₀ % (2 * k + 1) := by
    have dk : (2 * k + 1) ∣ P := ⟨2, by ring⟩
    rw [← Nat.mod_mod_of_dvd (x + t) dk, key, Nat.mod_mod_of_dvd m₀ dk]
  have hm₀2 : m₀ % 2 = 0 := by
    rw [hm₀, show r * (2 * k + 2) = r * (k + 1) * 2 by ring]
    exact Nat.mul_mod_left _ 2
  have hm₀k : m₀ % (2 * k + 1) = r := by
    rw [hm₀, show r * (2 * k + 2) = r + r * (2 * k + 1) by ring,
      Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt hr
  exact ⟨x + t, Nat.le_add_right _ _, by omega, by rw [h2]; exact hm₀2,
    by rw [h3]; exact hm₀k⟩

/-- The colour value of the edge from `v` to its `d`-th cyclic successor is
`min d (2n+1-d)`, for `1 ≤ d ≤ 2n`. -/
lemma ndColouring_sweep (n : ℕ) (hn : 0 < n) (v : Fin (2 * n + 1)) {d : ℕ}
    (hd1 : 1 ≤ d) (hd2 : d ≤ 2 * n) :
    (ndColouring n hn s(v, cyclicShift n v d)).val + 1 = min d (2 * n + 1 - d) := by
  have hdlt : d < 2 * n + 1 := by omega
  have hδ : cyclicShift n v d = v + ⟨d, hdlt⟩ := by
    apply Fin.ext
    rw [cyclicShift_val, Fin.add_def]
  rw [hδ]
  rcases Nat.lt_or_ge d (n + 1) with hdn | hdn
  · rw [ndColouring_step n hn v ⟨d, hdlt⟩ ⟨d - 1, by omega⟩ (Or.inl (by simp; omega))]
    change d - 1 + 1 = _
    omega
  · rw [ndColouring_step n hn v ⟨d, hdlt⟩ ⟨2 * n - d, by omega⟩ (Or.inr (by simp; omega))]
    change 2 * n - d + 1 = _
    omega

/-- **Generic interval counting** (MPS §7, counting fact inside `Lemma_small_tree`).
Let `Pcol` be a predicate on colour *values* such that every window of `D` consecutive
integers contains a `Pcol`-value.  A vertex `v` outside a cyclic interval `I` of length
`len` has at least `len/D - 2` neighbours `u ∈ I` whose colour value satisfies `Pcol`. -/
lemma card_pred_nbrs_in_cyclicInterval (n : ℕ) (hn : 0 < n)
    (Pcol : ℕ → Prop) [DecidablePred Pcol] (D : ℕ) (hD : 0 < D)
    (hwin : ∀ x, ∃ m, x ≤ m ∧ m < x + D ∧ Pcol m)
    (a : Fin (2 * n + 1)) (len : ℕ) (hlen : len ≤ 2 * n + 1)
    (v : Fin (2 * n + 1)) (hv : v ∉ cyclicInterval n a len) :
    len / D ≤
      ((cyclicInterval n a len).filter
        (fun u => Pcol ((ndColouring n hn s(v, u)).val + 1))).card + 2 := by
  classical
  set B := len / D with hB
  rcases Nat.lt_or_ge B 3 with hB2 | hB2
  · omega
  have hBle : B ≤ len := hB ▸ Nat.div_le_self len D
  have hlen1 : 1 ≤ len := by omega
  have hBP : B * D ≤ len := by
    rw [hB]
    exact Nat.div_mul_le_self len D
  -- distance from `v` to the base point of the interval
  set d₀ := (a.val + (2 * n + 1) - v.val) % (2 * n + 1) with hd₀
  have hshift : ∀ j, cyclicShift n a j = cyclicShift n v (d₀ + j) := by
    intro j
    conv_lhs => rw [← cyclicShift_dist n v a]
    rw [cyclicShift_cyclicShift]
  have hd₀lt : d₀ < 2 * n + 1 := Nat.mod_lt _ (by omega)
  have hd₀pos : 1 ≤ d₀ := by
    rcases Nat.eq_zero_or_pos d₀ with h0 | h
    · exfalso
      apply hv
      rw [mem_cyclicInterval]
      exact ⟨0, hlen1, by rw [hshift 0, h0, cyclicShift_zero]⟩
    · exact h
  -- since `v ∉ I` the distance sweep never wraps
  have hnowrap : ∀ j < len, d₀ + j ≤ 2 * n := by
    intro j hj
    by_contra hgt
    apply hv
    rw [mem_cyclicInterval]
    refine ⟨2 * n + 1 - d₀, by omega, ?_⟩
    rw [hshift]
    apply Fin.ext
    rw [cyclicShift_val, show d₀ + (2 * n + 1 - d₀) = 2 * n + 1 by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt v.isLt]
  -- the colour value along the sweep
  have hcol : ∀ j < len, (ndColouring n hn s(v, cyclicShift n a j)).val + 1
      = min (d₀ + j) (2 * n + 1 - (d₀ + j)) := by
    intro j hj
    rw [hshift]
    exact ndColouring_sweep n hn v (by omega) (hnowrap j hj)
  set F := (cyclicInterval n a len).filter
      (fun u => Pcol ((ndColouring n hn s(v, u)).val + 1)) with hF
  -- every block avoiding the fold at `n` produces a witness
  have hwitness : ∀ b < B, (d₀ + b * D + (D - 1) ≤ n ∨ n + 1 ≤ d₀ + b * D) →
      ∃ j, (b * D ≤ j ∧ j < b * D + D) ∧ cyclicShift n a j ∈ F := by
    intro b hb hclean
    have hblock : b * D + D ≤ len := by
      have h2 : (b + 1) * D ≤ B * D := Nat.mul_le_mul_right _ hb
      rw [add_mul, one_mul] at h2
      omega
    have hup2n : d₀ + b * D + (D - 1) ≤ 2 * n := by
      have := hnowrap (b * D + (D - 1)) (by omega)
      omega
    rcases hclean with hup | hdown
    · -- increasing branch: colour value is `d₀ + j`
      obtain ⟨m, hm1, hm2, hmP⟩ := hwin (d₀ + b * D)
      refine ⟨m - d₀, ⟨by omega, by omega⟩, ?_⟩
      have hjlen : m - d₀ < len := by omega
      rw [hF, Finset.mem_filter]
      refine ⟨mem_cyclicInterval.mpr ⟨m - d₀, hjlen, rfl⟩, ?_⟩
      rw [hcol _ hjlen,
        show min (d₀ + (m - d₀)) (2 * n + 1 - (d₀ + (m - d₀))) = m by omega]
      exact hmP
    · -- decreasing branch: colour value is `2n+1 - (d₀ + j)`
      obtain ⟨m, hm1, hm2, hmP⟩ := hwin (2 * n + 2 - (d₀ + b * D + D))
      refine ⟨2 * n + 1 - d₀ - m, ⟨by omega, by omega⟩, ?_⟩
      have hjlen : 2 * n + 1 - d₀ - m < len := by omega
      rw [hF, Finset.mem_filter]
      refine ⟨mem_cyclicInterval.mpr ⟨2 * n + 1 - d₀ - m, hjlen, rfl⟩, ?_⟩
      rw [hcol _ hjlen, show min (d₀ + (2 * n + 1 - d₀ - m))
          (2 * n + 1 - (d₀ + (2 * n + 1 - d₀ - m))) = m by omega]
      exact hmP
  -- at most one block contains the fold
  set clean : ℕ → Prop :=
    fun b => d₀ + b * D + (D - 1) ≤ n ∨ n + 1 ≤ d₀ + b * D with hclean
  have hBadcard : ((Finset.range B).filter (fun b => ¬ clean b)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro b1 hb1 b2 hb2
    simp only [Finset.mem_filter, Finset.mem_range, hclean, not_or, not_le] at hb1 hb2
    obtain ⟨-, hb1a, hb1b⟩ := hb1
    obtain ⟨-, hb2a, hb2b⟩ := hb2
    have h12 : b1 * D < b2 * D + D := by omega
    have h21 : b2 * D < b1 * D + D := by omega
    have hb12 : b1 < b2 + 1 := by
      have : b1 * D < (b2 + 1) * D := by rw [add_mul, one_mul]; exact h12
      exact lt_of_mul_lt_mul_right this (Nat.zero_le D)
    have hb21 : b2 < b1 + 1 := by
      have : b2 * D < (b1 + 1) * D := by rw [add_mul, one_mul]; exact h21
      exact lt_of_mul_lt_mul_right this (Nat.zero_le D)
    omega
  have hGoodcard : B - 1 ≤ ((Finset.range B).filter clean).card := by
    have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.range B) (p := clean)
    rw [Finset.card_range] at hsplit
    omega
  -- choose a witness vertex for each clean block; the map is injective
  have hchoice : ∀ b : ℕ, ∃ j, b ∈ (Finset.range B).filter clean →
      ((b * D ≤ j ∧ j < b * D + D) ∧ cyclicShift n a j ∈ F) := by
    intro b
    by_cases hb : b ∈ (Finset.range B).filter clean
    · simp only [Finset.mem_filter, Finset.mem_range, hclean] at hb
      obtain ⟨j, hj⟩ := hwitness b hb.1 hb.2
      exact ⟨j, fun _ => hj⟩
    · exact ⟨0, fun h => absurd h hb⟩
  choose g hg using hchoice
  have hgle : ∀ b ∈ (Finset.range B).filter clean, g b < len := by
    intro b hb
    obtain ⟨⟨-, h2⟩, -⟩ := hg b hb
    have hbB : b < B := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
    have hmul : (b + 1) * D ≤ B * D := Nat.mul_le_mul_right _ hbB
    rw [add_mul, one_mul] at hmul
    omega
  have hmaps : ∀ b ∈ (Finset.range B).filter clean, cyclicShift n a (g b) ∈ F :=
    fun b hb => (hg b hb).2
  have hinj : Set.InjOn (fun b => cyclicShift n a (g b))
      ((Finset.range B).filter clean : Finset ℕ) := by
    intro b1 hb1 b2 hb2 heq
    rw [Finset.mem_coe] at hb1 hb2
    have hj1 := (hg b1 hb1).1
    have hj2 := (hg b2 hb2).1
    have hgeq : g b1 = g b2 :=
      cyclicShift_injOn n a (lt_of_lt_of_le (hgle b1 hb1) hlen)
        (lt_of_lt_of_le (hgle b2 hb2) hlen) heq
    have h12 : b1 * D < b2 * D + D := by omega
    have h21 : b2 * D < b1 * D + D := by omega
    have hb12 : b1 < b2 + 1 := by
      have : b1 * D < (b2 + 1) * D := by rw [add_mul, one_mul]; exact h12
      exact lt_of_mul_lt_mul_right this (Nat.zero_le D)
    have hb21 : b2 < b1 + 1 := by
      have : b2 * D < (b1 + 1) * D := by rw [add_mul, one_mul]; exact h21
      exact lt_of_mul_lt_mul_right this (Nat.zero_le D)
    omega
  have hcard := Finset.card_le_card_of_injOn _
    (fun b hb => Finset.mem_coe.mpr (hmaps b (Finset.mem_coe.mp hb))) hinj
  omega

/-- A shifted cyclic subinterval is contained in the ambient cyclic interval. -/
lemma cyclicInterval_shift_subset (n : ℕ) (a : Fin (2 * n + 1)) {i m len : ℕ}
    (h : i + m ≤ len) :
    cyclicInterval n (cyclicShift n a i) m ⊆ cyclicInterval n a len := by
  intro u hu
  obtain ⟨j, hj, hju⟩ := mem_cyclicInterval.mp hu
  rw [cyclicShift_cyclicShift] at hju
  exact mem_cyclicInterval.mpr ⟨i + j, by omega, hju⟩

/-- Two shifted cyclic subintervals with non-overlapping index ranges are disjoint. -/
lemma cyclicInterval_shift_disjoint (n : ℕ) (a : Fin (2 * n + 1)) {i₁ m₁ i₂ m₂ : ℕ}
    (h12 : i₁ + m₁ ≤ i₂) (h2 : i₂ + m₂ ≤ 2 * n + 1) :
    Disjoint (cyclicInterval n (cyclicShift n a i₁) m₁)
      (cyclicInterval n (cyclicShift n a i₂) m₂) := by
  rw [Finset.disjoint_left]
  intro u hu1 hu2
  obtain ⟨j1, hj1, hju1⟩ := mem_cyclicInterval.mp hu1
  obtain ⟨j2, hj2, hju2⟩ := mem_cyclicInterval.mp hu2
  rw [cyclicShift_cyclicShift] at hju1 hju2
  have := cyclicShift_injOn n a (by omega : i₁ + j1 < 2 * n + 1)
    (by omega : i₂ + j2 < 2 * n + 1) (hju1.trans hju2.symm)
  omega

/-- Distinct residues give disjoint colour classes. -/
lemma colourClass_disjoint (n k : ℕ) {r r' : ℕ} (hne : r ≠ r') :
    Disjoint (colourClass n k r) (colourClass n k r') := by
  rw [Finset.disjoint_left]
  intro c hc hc'
  rw [mem_colourClass] at hc hc'
  exact hne (hc.2.symm.trans hc'.2)

/-- The odd colours are disjoint from every (even) colour class. -/
lemma oddColourClass_disjoint_colourClass (n k r : ℕ) :
    Disjoint (oddColourClass n) (colourClass n k r) := by
  rw [Finset.disjoint_left]
  intro c hc hc'
  rw [mem_oddColourClass] at hc
  rw [mem_colourClass] at hc'
  omega

/-- **Unconditional generic interval counting**: like `card_pred_nbrs_in_cyclicInterval`
but with no hypothesis on the location of `v`, at the cost of slack `6` instead of `2`.
When `v ∈ I` the interval splits at `v` into two cyclic intervals avoiding `v`. -/
lemma card_pred_nbrs_in_cyclicInterval' (n : ℕ) (hn : 0 < n)
    (Pcol : ℕ → Prop) [DecidablePred Pcol] (D : ℕ) (hD : 0 < D)
    (hwin : ∀ x, ∃ m, x ≤ m ∧ m < x + D ∧ Pcol m)
    (a : Fin (2 * n + 1)) (len : ℕ) (hlen : len ≤ 2 * n + 1)
    (v : Fin (2 * n + 1)) :
    len / D ≤
      ((cyclicInterval n a len).filter
        (fun u => Pcol ((ndColouring n hn s(v, u)).val + 1))).card + 6 := by
  classical
  by_cases hv : v ∈ cyclicInterval n a len
  · obtain ⟨j₀, hj₀len, hj₀⟩ := mem_cyclicInterval.mp hv
    have hvA : v ∉ cyclicInterval n a j₀ := by
      rw [mem_cyclicInterval]
      rintro ⟨j, hj, hjv⟩
      have := cyclicShift_injOn n a (by omega) (by omega) (hjv.trans hj₀.symm)
      omega
    have hvB : v ∉ cyclicInterval n (cyclicShift n a (j₀ + 1)) (len - j₀ - 1) := by
      rw [mem_cyclicInterval]
      rintro ⟨j, hj, hjv⟩
      rw [cyclicShift_cyclicShift] at hjv
      have := cyclicShift_injOn n a (by omega) (by omega) (hjv.trans hj₀.symm)
      omega
    have hcA := card_pred_nbrs_in_cyclicInterval n hn Pcol D hD hwin a j₀
      (by omega) v hvA
    have hcB := card_pred_nbrs_in_cyclicInterval n hn Pcol D hD hwin
      (cyclicShift n a (j₀ + 1)) (len - j₀ - 1) (by omega) v hvB
    have hAsub : cyclicInterval n a j₀ ⊆ cyclicInterval n a len := by
      have := cyclicInterval_shift_subset n a (i := 0) (m := j₀) (len := len) (by omega)
      rwa [cyclicShift_zero] at this
    have hBsub : cyclicInterval n (cyclicShift n a (j₀ + 1)) (len - j₀ - 1)
        ⊆ cyclicInterval n a len :=
      cyclicInterval_shift_subset n a (by omega)
    have hAB : Disjoint (cyclicInterval n a j₀)
        (cyclicInterval n (cyclicShift n a (j₀ + 1)) (len - j₀ - 1)) := by
      have := cyclicInterval_shift_disjoint n a (i₁ := 0) (m₁ := j₀)
        (i₂ := j₀ + 1) (m₂ := len - j₀ - 1) (by omega) (by omega)
      rwa [cyclicShift_zero] at this
    have hunion : ((cyclicInterval n a j₀).filter
          (fun u => Pcol ((ndColouring n hn s(v, u)).val + 1))).card +
        ((cyclicInterval n (cyclicShift n a (j₀ + 1)) (len - j₀ - 1)).filter
          (fun u => Pcol ((ndColouring n hn s(v, u)).val + 1))).card ≤
        ((cyclicInterval n a len).filter
          (fun u => Pcol ((ndColouring n hn s(v, u)).val + 1))).card := by
      rw [← Finset.card_union_of_disjoint
        (Finset.disjoint_filter_filter hAB)]
      exact Finset.card_le_card (Finset.union_subset
        (Finset.filter_subset_filter _ hAsub) (Finset.filter_subset_filter _ hBsub))
    have hdiv : len / D < j₀ / D + (len - j₀ - 1) / D + 2 := by
      rw [Nat.div_lt_iff_lt_mul hD]
      have h1 := Nat.div_add_mod j₀ D
      have h2 := Nat.div_add_mod (len - j₀ - 1) D
      have hm1 : j₀ % D < D := Nat.mod_lt _ hD
      have hm2 : (len - j₀ - 1) % D < D := Nat.mod_lt _ hD
      have hexp : (j₀ / D + (len - j₀ - 1) / D + 2) * D
          = D * (j₀ / D) + D * ((len - j₀ - 1) / D) + 2 * D := by ring
      rw [hexp]
      omega
    omega
  · have := card_pred_nbrs_in_cyclicInterval n hn Pcol D hD hwin a len hlen v hv
    omega

/-- **Interval colour-class counting**: a vertex `v` outside a cyclic interval `I` of
length `len` has at least `len/(2(2k+1)) - 2` neighbours `u ∈ I` with
`ndColouring s(v, u) ∈ colourClass n k r`. -/
lemma card_class_nbrs_in_cyclicInterval (n : ℕ) (hn : 0 < n) (k r : ℕ)
    (hr : r < 2 * k + 1) (a : Fin (2 * n + 1)) (len : ℕ) (hlen : len ≤ 2 * n + 1)
    (v : Fin (2 * n + 1)) (hv : v ∉ cyclicInterval n a len) :
    len / (2 * (2 * k + 1)) ≤
      ((cyclicInterval n a len).filter
        (fun u => ndColouring n hn s(v, u) ∈ colourClass n k r)).card + 2 := by
  have h := card_pred_nbrs_in_cyclicInterval n hn
    (fun m => m % 2 = 0 ∧ m % (2 * k + 1) = r) (2 * (2 * k + 1)) (by omega)
    (fun x => exists_even_residue_in_window x k r hr) a len hlen v hv
  simpa only [mem_colourClass] using h

/-- **Interval odd-colour counting**: a vertex `v` outside a cyclic interval `I` of
length `len` has at least `len/2 - 2` neighbours `u ∈ I` with
`ndColouring s(v, u) ∈ oddColourClass n`. -/
lemma card_odd_nbrs_in_cyclicInterval (n : ℕ) (hn : 0 < n)
    (a : Fin (2 * n + 1)) (len : ℕ) (hlen : len ≤ 2 * n + 1)
    (v : Fin (2 * n + 1)) (hv : v ∉ cyclicInterval n a len) :
    len / 2 ≤
      ((cyclicInterval n a len).filter
        (fun u => ndColouring n hn s(v, u) ∈ oddColourClass n)).card + 2 := by
  have h := card_pred_nbrs_in_cyclicInterval n hn
    (fun m => m % 2 = 1) 2 (by omega)
    (fun x => ⟨x + (x + 1) % 2, by omega, by omega, by omega⟩) a len hlen v hv
  simpa only [mem_oddColourClass] using h

/-- Unconditional colour-class counting: no hypothesis on `v`, slack `6`. -/
lemma card_class_nbrs_in_cyclicInterval' (n : ℕ) (hn : 0 < n) (k r : ℕ)
    (hr : r < 2 * k + 1) (a : Fin (2 * n + 1)) (len : ℕ) (hlen : len ≤ 2 * n + 1)
    (v : Fin (2 * n + 1)) :
    len / (2 * (2 * k + 1)) ≤
      ((cyclicInterval n a len).filter
        (fun u => ndColouring n hn s(v, u) ∈ colourClass n k r)).card + 6 := by
  have h := card_pred_nbrs_in_cyclicInterval' n hn
    (fun m => m % 2 = 0 ∧ m % (2 * k + 1) = r) (2 * (2 * k + 1)) (by omega)
    (fun x => exists_even_residue_in_window x k r hr) a len hlen v
  simpa only [mem_colourClass] using h

/-- Unconditional odd-colour counting: no hypothesis on `v`, slack `6`. -/
lemma card_odd_nbrs_in_cyclicInterval' (n : ℕ) (hn : 0 < n)
    (a : Fin (2 * n + 1)) (len : ℕ) (hlen : len ≤ 2 * n + 1)
    (v : Fin (2 * n + 1)) :
    len / 2 ≤
      ((cyclicInterval n a len).filter
        (fun u => ndColouring n hn s(v, u) ∈ oddColourClass n)).card + 6 := by
  have h := card_pred_nbrs_in_cyclicInterval' n hn
    (fun m => m % 2 = 1) 2 (by omega)
    (fun x => ⟨x + (x + 1) % 2, by omega, by omega, by omega⟩) a len hlen v
  simpa only [mem_oddColourClass] using h

end Ringel
