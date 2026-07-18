/-
Copyright (c) 2026 Walid Elkersh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Walid Elkersh
-/
import Mathlib

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-!
# Generic engines for the Case C leaf-packing (MPS §7)

This file collects reusable, project-independent combinatorial engines that drive the
explicit leaf-packing construction of the many-high-degree-vertex case:

* `up_pos_gap_injOn` — up-fan injectivity when colour gaps dominate a *decreasing*
  position (the mirror of `down_pos_gap_injOn`, used for the reversed type-2 fan);
* `rank_injOn` / `rank_lt_card` / `rank_lt_of_key_lt` — the "rank under an injective
  key" gadget: `x ↦ #{y ∈ S : key y < key x}` is an injection `S → {0,…,|S|-1}`, and
  is strictly monotone in the key.  This assigns each leaf a distinct colour index in
  block order without having to build explicit prefix-sum offsets.
-/

namespace Ringel

/-- **Up-fan injectivity, gap form.** If the colour value grows strictly faster than the
anchor position *decreases* (colour gaps dominate position gaps), the up-position
`p j + col j` is injective even when the anchor position decreases along the enumeration.
This is the engine of the reversed type-2 leaf packing: the vertex carrying the smallest
even colour block sits at the *rightmost* position, so as the colour value increases the
anchor position decreases, and the up-positions still increase because each intervening
fan contributes `≥ 100·L` colours against a `≤ 3·L` position drop. -/
lemma up_pos_gap_injOn (N : ℕ) (col p : ℕ → ℕ)
    (hcolmono : ∀ i j, i < j → j < N → col i ≤ col j)
    (hpanti : ∀ i j, i < j → j < N → p j ≤ p i)
    (hgap : ∀ i j, i < j → j < N → p i - p j < col j - col i) :
    Set.InjOn (fun j => p j + col j) (Set.Iio N) := by
  intro i hi j hj hij
  rw [Set.mem_Iio] at hi hj
  simp only at hij
  rcases lt_trichotomy i j with h | h | h
  · have := hcolmono i j h hj; have := hpanti i j h hj; have := hgap i j h hj; omega
  · exact h
  · have := hcolmono j i h hi; have := hpanti j i h hi; have := hgap j i h hi; omega

/-- **Rank under an injective key is injective.** For a finite set `S` and a key `key`
that is injective on `S`, the map `x ↦ #{y ∈ S : key y < key x}` is injective on `S`. -/
lemma rank_injOn {V : Type*} [DecidableEq V] (S : Finset V) (key : V → ℕ)
    (hkey : Set.InjOn key ↑S) :
    Set.InjOn (fun x => (S.filter (fun y => key y < key x)).card) ↑S := by
  intro a ha b hb hab
  rw [Finset.mem_coe] at ha hb
  simp only at hab
  rcases lt_trichotomy (key a) (key b) with h | h | h
  · -- {y : key y < key a} ⊊ {y : key y < key b}
    exfalso
    have hsub : S.filter (fun y => key y < key a) ⊆ S.filter (fun y => key y < key b) := by
      intro y hy
      rw [Finset.mem_filter] at hy ⊢
      exact ⟨hy.1, lt_trans hy.2 h⟩
    have hlt : (S.filter (fun y => key y < key a)).card <
        (S.filter (fun y => key y < key b)).card := by
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset hsub]
      exact ⟨a, Finset.mem_filter.mpr ⟨ha, h⟩, fun hcon => by
        rw [Finset.mem_filter] at hcon; exact absurd hcon.2 (lt_irrefl _)⟩
    omega
  · exact hkey (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) h
  · exfalso
    have hsub : S.filter (fun y => key y < key b) ⊆ S.filter (fun y => key y < key a) := by
      intro y hy
      rw [Finset.mem_filter] at hy ⊢
      exact ⟨hy.1, lt_trans hy.2 h⟩
    have hlt : (S.filter (fun y => key y < key b)).card <
        (S.filter (fun y => key y < key a)).card := by
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset hsub]
      exact ⟨b, Finset.mem_filter.mpr ⟨hb, h⟩, fun hcon => by
        rw [Finset.mem_filter] at hcon; exact absurd hcon.2 (lt_irrefl _)⟩
    omega

/-- The rank of any element is `< |S|`. -/
lemma rank_lt_card {V : Type*} [DecidableEq V] (S : Finset V) (key : V → ℕ) {x : V} :
    (S.filter (fun y => key y < key x)).card ≤ S.card :=
  Finset.card_filter_le _ _

/-- Rank is strictly monotone in the key, for elements of `S`. -/
lemma rank_lt_of_key_lt {V : Type*} [DecidableEq V] (S : Finset V) (key : V → ℕ)
    {a b : V} (ha : a ∈ S) (h : key a < key b) :
    (S.filter (fun y => key y < key a)).card < (S.filter (fun y => key y < key b)).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨a, Finset.mem_filter.mpr ⟨ha, h⟩, fun hcon => by
        rw [Finset.mem_filter] at hcon; exact absurd hcon.2 (lt_irrefl _)⟩
  · intro y hy
    rw [Finset.mem_filter] at hy ⊢
    exact ⟨hy.1, lt_trans hy.2 h⟩

/-- **Rank gap lower bound.** If `key a ≤ key b` and `MID ⊆ S` consists of elements whose
key lies strictly between `key a` and `key b`, then `|MID|` is at most the difference of
the ranks of `b` and `a`.  This is how an intervening block of leaves (a whole fan of the
other type) forces a large colour-index gap between two consecutive same-type fans. -/
lemma rank_diff_ge {V : Type*} [DecidableEq V] (S : Finset V) (key : V → ℕ)
    {a b : V} (hab : key a ≤ key b) (MID : Finset V) (hMIDS : MID ⊆ S)
    (hMID : ∀ z ∈ MID, key a < key z ∧ key z < key b) :
    MID.card + (S.filter (fun y => key y < key a)).card
      ≤ (S.filter (fun y => key y < key b)).card := by
  have hsuba : S.filter (fun y => key y < key a) ⊆ S.filter (fun y => key y < key b) := by
    intro y hy
    rw [Finset.mem_filter] at hy ⊢
    exact ⟨hy.1, lt_of_lt_of_le hy.2 hab⟩
  have hdisj : Disjoint MID (S.filter (fun y => key y < key a)) := by
    rw [Finset.disjoint_left]
    intro z hzM hzA
    rw [Finset.mem_filter] at hzA
    exact absurd hzA.2 (not_lt.mpr (le_of_lt (hMID z hzM).1))
  have hunion : MID ∪ S.filter (fun y => key y < key a)
      ⊆ S.filter (fun y => key y < key b) := by
    intro z hz
    rw [Finset.mem_union] at hz
    rcases hz with hz | hz
    · rw [Finset.mem_filter]
      exact ⟨hMIDS hz, (hMID z hz).2⟩
    · exact hsuba hz
  calc MID.card + (S.filter (fun y => key y < key a)).card
      = (MID ∪ S.filter (fun y => key y < key a)).card := (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ (S.filter (fun y => key y < key b)).card := Finset.card_le_card hunion

/-! ## The explicit colour-rank / colour-index / position construction (MPS §7) -/

/-- **Colour-rank permutation.** Within the low-colour side `V₁` (of size `m`), the
vertices are relabelled so that, in *position* order `0,1,…,m-1`, the type-1 (down) fans
come first (colour ranks `0,2,4,…`) and the type-2 (up) fans come last, in *reversed*
position order (colour ranks `1,3,5,…`).  This is the paper's interleaving
`u₁,u₃,…,u_m,u_{m-1},…,u₂`: it guarantees that two consecutive same-type fans are
separated in colour by a whole intervening fan of the other type. -/
def cPerm (m r : ℕ) : ℕ := if r < (m + 1) / 2 then 2 * r else 2 * (m - 1 - r) + 1

/-- **Colour rank** of a leaf-bearing vertex: `V₁` occupies `[0, |V₁|)` (interleaved by
`cPerm`), `V₂` occupies `[|V₁|, |V₁|+|V₂|)` in position order.  (Junk on other inputs.) -/
def cRank {V : Type*} [DecidableEq V] (V₁ V₂ : Finset V) (idx : V → ℕ) (L : ℕ) (u : V) : ℕ :=
  if u ∈ V₁ then cPerm V₁.card (idx u / L) else V₁.card + idx u / L

/-- **Lex key**: order leaves first by the colour rank of their anchor, then by an
arbitrary injective tie-breaker; the multiplier `Fintype.card V + 1` dominates the tie. -/
noncomputable def cKey {V : Type*} [Fintype V] [DecidableEq V] (V₁ V₂ : Finset V) (idx : V → ℕ) (L : ℕ)
    (anchor : V → V) (x : V) : ℕ :=
  cRank V₁ V₂ idx L (anchor x) * (Fintype.card V + 1) + (Fintype.equivFin V x).1

/-- **Colour index** of a leaf: its rank among all leaves under `cKey`.  Ranges over
`[0, #leaves)` bijectively; leaves of one fan occupy a contiguous block. -/
noncomputable def cCiv {V : Type*} [Fintype V] [DecidableEq V] (leaves V₁ V₂ : Finset V)
    (idx : V → ℕ) (L : ℕ) (anchor : V → V) (x : V) : ℕ :=
  (leaves.filter (fun y => cKey V₁ V₂ idx L anchor y < cKey V₁ V₂ idx L anchor x)).card

/-- The number of leaves attached to a core vertex `u`. -/
def cDeg {V : Type*} [Fintype V] [DecidableEq V] (leaves : Finset V) (anchor : V → V)
    (u : V) : ℕ := (leaves.filter (fun x => anchor x = u)).card

/-- **Raw leaf position value.** Type-1 fans (`u ∈ V₁`, low position rank) attach
*downwards* (`g u − (c+1)`); type-2 (`u ∈ V₁`, high position rank) and type-3 (`u ∈ V₂`)
attach *upwards* (`g u + (c+1)`), where `c` is the realized colour value. -/
def cPosVal {n : ℕ} {V : Type*} [DecidableEq V] (V₁ V₂ : Finset V) (idx : V → ℕ) (L : ℕ)
    (g : V → Fin (2 * n + 1)) (anchor : V → V) (colval : V → ℕ) (x : V) : ℕ :=
  if anchor x ∈ V₁ ∧ idx (anchor x) / L < (V₁.card + 1) / 2 then
    (g (anchor x)).val - (colval x + 1)
  else (g (anchor x)).val + (colval x + 1)

/-- The leaf position as an element of `Fin (2n+1)` (reduced mod `2n+1`; in range the
reduction is trivial and the value equals `cPosVal`). -/
def cPos {n : ℕ} {V : Type*} [DecidableEq V] (V₁ V₂ : Finset V) (idx : V → ℕ) (L : ℕ)
    (g : V → Fin (2 * n + 1)) (anchor : V → V) (colval : V → ℕ) (x : V) : Fin (2 * n + 1) :=
  ⟨cPosVal V₁ V₂ idx L g anchor colval x % (2 * n + 1), Nat.mod_lt _ (by positivity)⟩

/-- `cPerm m r < m` for `r < m`. -/
lemma cPerm_lt {m r : ℕ} (hr : r < m) : cPerm m r < m := by
  unfold cPerm
  split_ifs with h <;> omega

/-- `cPerm` is injective on `[0, m)`. -/
lemma cPerm_injOn {m : ℕ} : Set.InjOn (cPerm m) (Set.Iio m) := by
  intro a ha b hb hab
  rw [Set.mem_Iio] at ha hb
  unfold cPerm at hab
  split_ifs at hab <;> omega

/-
**Generic initial-segment count.** If `f` is injective on `S` and maps `S` onto
`range |S|`, then exactly `c` elements of `S` have `f`-value `< c`, for any `c ≤ |S|`.
-/
lemma card_filter_lt_image_eq {V : Type*} [DecidableEq V] (f : V → ℕ) (S : Finset V)
    (hinj : Set.InjOn f ↑S) (himg : S.image f = Finset.range S.card) {c : ℕ} (hc : c ≤ S.card) :
    (S.filter (fun w => f w < c)).card = c := by
  have h_image : Finset.image f (Finset.filter (fun w => f w < c) S) = Finset.range c := by
    ext x; simp [Finset.mem_image] at *; (
    exact ⟨ fun ⟨ a, ha, hx ⟩ => hx ▸ ha.2, fun hx => by have := Finset.mem_image.mp ( himg.symm ▸ Finset.mem_range.mpr ( by linarith : x < S.card ) ) ; aesop ⟩ ;);
  rw [ ← Finset.card_image_of_injOn ( hinj.mono <| Finset.filter_subset _ _ ), h_image, Finset.card_range ]

/-
`cRank` is injective on `V₁ ∪ V₂`.
-/
lemma cRank_injOn {V : Type*} [DecidableEq V] (V₁ V₂ : Finset V) (idx : V → ℕ) (L : ℕ)
    (hV₁V₂ : Disjoint V₁ V₂)
    (hrank1 : ∀ u ∈ V₁, idx u / L < V₁.card) (hrank2 : ∀ u ∈ V₂, idx u / L < V₂.card)
    (hblk1 : ∀ u ∈ V₁, ∀ v ∈ V₁, u ≠ v → idx u / L ≠ idx v / L)
    (hblk2 : ∀ u ∈ V₂, ∀ v ∈ V₂, u ≠ v → idx u / L ≠ idx v / L) :
    Set.InjOn (cRank V₁ V₂ idx L) ↑(V₁ ∪ V₂) := by
  intros v hv; simp [cRank] at hv; cases' hv with hv₁ hv₂;
  · intro w hw h;
    simp_all +decide [ cRank ];
    split_ifs at h;
    · exact Classical.not_not.1 fun h' => hblk1 v hv₁ w ‹_› h' <| by have := cPerm_injOn ( show idx v / L < V₁.card from hrank1 v hv₁ ) ( show idx w / L < V₁.card from hrank1 w ‹_› ) h; aesop;
    · unfold cPerm at h;
      grind (instances := 20000) (splits := 500) (gen := 500) +splitImp;
  · unfold cRank at *; simp_all +decide [ Finset.disjoint_left ] ;
    intro w hw; split_ifs at * <;> simp_all +decide [ cPerm ] ;
    · grind (instances := 20000) (splits := 500) (gen := 500);
    · exact fun h => Classical.not_not.1 fun hne => hblk2 v hv₂ w hw hne h

/-
The image of `V₁` under `cRank` is `range |V₁|`.
-/
lemma cRank_image_V1 {V : Type*} [DecidableEq V] (V₁ V₂ : Finset V) (idx : V → ℕ) (L : ℕ)
    (hrank1 : ∀ u ∈ V₁, idx u / L < V₁.card)
    (hblk1 : ∀ u ∈ V₁, ∀ v ∈ V₁, u ≠ v → idx u / L ≠ idx v / L) :
    V₁.image (cRank V₁ V₂ idx L) = Finset.range V₁.card := by
  refine' Finset.eq_of_subset_of_card_le _ _;
  · grind (instances := 20000) (splits := 500) (gen := 500) +locals;
  · rw [ Finset.card_image_of_injOn ];
    · simp +decide;
    · intro u hu v hv huv; simp_all +decide [ cRank ] ;
      exact Classical.not_not.1 fun h => hblk1 u hu v hv h <| by have := cPerm_injOn ( show idx u / L < V₁.card from hrank1 u hu ) ( show idx v / L < V₁.card from hrank1 v hv ) huv; aesop;

/-
**Lex key is injective on the leaves.**
-/
lemma cKey_injOn_leaves {V : Type*} [Fintype V] [DecidableEq V] (leaves V₁ V₂ : Finset V)
    (idx : V → ℕ) (L : ℕ) (anchor : V → V)
    (hanchor_big : ∀ x ∈ leaves, anchor x ∈ V₁ ∪ V₂)
    (hcrank : Set.InjOn (cRank V₁ V₂ idx L) ↑(V₁ ∪ V₂)) :
    Set.InjOn (cKey V₁ V₂ idx L anchor) ↑leaves := by
  intro x hx y hy hxy;
  unfold cKey at hxy;
  have := congr_arg ( · % ( Fintype.card V + 1 ) ) hxy; norm_num [ Nat.add_mod, Nat.mod_eq_of_lt ] at this;
  exact Fintype.equivFin V |>.injective ( Fin.ext this )

/-- **Colour index is injective on the leaves.** -/
lemma cCiv_injOn_leaves {V : Type*} [Fintype V] [DecidableEq V] (leaves V₁ V₂ : Finset V)
    (idx : V → ℕ) (L : ℕ) (anchor : V → V)
    (hkey : Set.InjOn (cKey V₁ V₂ idx L anchor) ↑leaves) :
    Set.InjOn (cCiv leaves V₁ V₂ idx L anchor) ↑leaves :=
  rank_injOn leaves (cKey V₁ V₂ idx L anchor) hkey

/-
The colour index of a leaf is `< #leaves`.
-/
lemma cCiv_lt_card {V : Type*} [Fintype V] [DecidableEq V] (leaves V₁ V₂ : Finset V)
    (idx : V → ℕ) (L : ℕ) (anchor : V → V) {x : V} (hx : x ∈ leaves) :
    cCiv leaves V₁ V₂ idx L anchor x < leaves.card := by
  convert Finset.card_lt_card ( Finset.filter_ssubset.mpr _ ) using 1;
  exact ⟨ x, hx, by simp +decide ⟩

/-
**Generic strictly-between count.** With `f` injective on `S` mapping onto
`range |S|`, exactly `c2 - c1 - 1` elements have `f`-value strictly between `c1` and `c2`
(for `c1 < c2 ≤ |S|`).
-/
lemma card_filter_between_image {V : Type*} [DecidableEq V] (f : V → ℕ) (S : Finset V)
    (hinj : Set.InjOn f ↑S) (himg : S.image f = Finset.range S.card) {c1 c2 : ℕ}
    (h12 : c1 < c2) (hc2 : c2 ≤ S.card) :
    (S.filter (fun w => c1 < f w ∧ f w < c2)).card = c2 - c1 - 1 := by
  rw [ show { w ∈ S | c1 < f w ∧ f w < c2 } = S.filter ( fun w => f w < c2 ) \ S.filter ( fun w => f w < c1 + 1 ) from ?_ ];
  · rw [ Finset.card_sdiff ];
    rw [ show ( { w ∈ S | f w < c1 + 1 } ∩ { w ∈ S | f w < c2 } ) = { w ∈ S | f w < c1 + 1 } from ?_ ];
    · rw [ card_filter_lt_image_eq f S hinj himg ( by linarith : c2 ≤ S.card ), card_filter_lt_image_eq f S hinj himg ( by linarith : c1 + 1 ≤ S.card ) ] ; omega;
    · grind (instances := 20000) (splits := 500) (gen := 500);
  · grind (instances := 20000) (splits := 500) (gen := 500)

/-
**Colour-index lower bound via smaller-rank fans.** The colour index of a leaf `x`
is at least the total number of leaves attached to fans of strictly smaller colour rank.
-/
lemma cCiv_ge_below {V : Type*} [Fintype V] [DecidableEq V] (leaves V₁ V₂ : Finset V)
    (idx : V → ℕ) (L : ℕ) (anchor : V → V)
    (hanchor_big : ∀ x ∈ leaves, anchor x ∈ V₁ ∪ V₂) {x : V} (hx : x ∈ leaves) :
    ∑ w ∈ (V₁ ∪ V₂).filter
        (fun w => cRank V₁ V₂ idx L w < cRank V₁ V₂ idx L (anchor x)),
      cDeg leaves anchor w ≤ cCiv leaves V₁ V₂ idx L anchor x := by
  refine' le_trans _ ( Finset.card_mono <| show Finset.filter ( fun y => cKey V₁ V₂ idx L anchor y < cKey V₁ V₂ idx L anchor x ) leaves ⊇ Finset.filter ( fun y => cRank V₁ V₂ idx L ( anchor y ) < cRank V₁ V₂ idx L ( anchor x ) ) leaves from _ );
  · rw [ Finset.card_filter ];
    rw [ Finset.sum_congr rfl fun w hw => show cDeg leaves anchor w = ∑ y ∈ leaves, if anchor y = w then 1 else 0 from ?_ ];
    · rw [ Finset.sum_comm ];
      gcongr ; aesop;
    · simp +decide [ cDeg ];
  · intro y hy; simp_all +decide [ cKey ] ;
    nlinarith [ Fin.is_lt ( Fintype.equivFin V y ), Fin.is_lt ( Fintype.equivFin V x ) ]

/-
**Colour-index gap via intervening fans.** If `anchor x` has strictly smaller colour
rank than `anchor y`, the colour indices differ by at least the total number of leaves in
the fans whose colour rank lies strictly between them.
-/
lemma cCiv_diff_ge_between {V : Type*} [Fintype V] [DecidableEq V] (leaves V₁ V₂ : Finset V)
    (idx : V → ℕ) (L : ℕ) (anchor : V → V)
    (hanchor_big : ∀ x ∈ leaves, anchor x ∈ V₁ ∪ V₂)
    (hkey : Set.InjOn (cKey V₁ V₂ idx L anchor) ↑leaves)
    {x y : V} (hx : x ∈ leaves) (hy : y ∈ leaves)
    (hlt : cRank V₁ V₂ idx L (anchor x) < cRank V₁ V₂ idx L (anchor y)) :
    cCiv leaves V₁ V₂ idx L anchor x
      + ∑ w ∈ (V₁ ∪ V₂).filter
          (fun w => cRank V₁ V₂ idx L (anchor x) < cRank V₁ V₂ idx L w
            ∧ cRank V₁ V₂ idx L w < cRank V₁ V₂ idx L (anchor y)),
        cDeg leaves anchor w
      ≤ cCiv leaves V₁ V₂ idx L anchor y := by
  refine' le_trans _ ( Finset.card_mono <| show Finset.filter ( fun z => cKey V₁ V₂ idx L anchor z < cKey V₁ V₂ idx L anchor y ) leaves ⊇ Finset.filter ( fun z => cKey V₁ V₂ idx L anchor z < cKey V₁ V₂ idx L anchor x ) leaves ∪ Finset.biUnion ( ( V₁ ∪ V₂ ).filter ( fun w => cRank V₁ V₂ idx L ( anchor x ) < cRank V₁ V₂ idx L w ∧ cRank V₁ V₂ idx L w < cRank V₁ V₂ idx L ( anchor y ) ) ) ( fun w => leaves.filter ( fun z => anchor z = w ) ) from _ );
  · rw [ Finset.card_union_of_disjoint ];
    · rw [ Finset.card_biUnion ];
      · exact add_le_add ( by rfl ) ( Finset.sum_le_sum fun _ _ => by rfl );
      · exact fun a ha b hb hab => Finset.disjoint_left.mpr fun x hx₁ hx₂ => hab <| by aesop;
    · simp +contextual [ Finset.disjoint_left ];
      intro z hz hz' hz'' hz'''; contrapose! hz';
      unfold cKey; nlinarith [ Fin.is_lt ( Fintype.equivFin V x ), Fin.is_lt ( Fintype.equivFin V z ) ] ;
  · simp +decide [ Finset.subset_iff ];
    rintro z ( hz | hz ) <;> simp_all +decide [ cKey ];
    · exact lt_of_lt_of_le hz.2 ( by nlinarith [ Fin.is_lt ( Fintype.equivFin V x ), Fin.is_lt ( Fintype.equivFin V y ) ] );
    · nlinarith [ Fin.is_lt ( Fintype.equivFin V z ), Fin.is_lt ( Fintype.equivFin V y ) ]

/-- Colour rank of a type-1 vertex (`u ∈ V₁`, low position rank). -/
lemma cRank_type1 {V : Type*} [DecidableEq V] (V₁ V₂ : Finset V) (idx : V → ℕ) (L : ℕ)
    {u : V} (hu : u ∈ V₁) (hr : idx u / L < (V₁.card + 1) / 2) :
    cRank V₁ V₂ idx L u = 2 * (idx u / L) := by
  unfold cRank cPerm; rw [if_pos hu, if_pos hr]

/-- Colour rank of a type-2 vertex (`u ∈ V₁`, high position rank). -/
lemma cRank_type2 {V : Type*} [DecidableEq V] (V₁ V₂ : Finset V) (idx : V → ℕ) (L : ℕ)
    {u : V} (hu : u ∈ V₁) (hr : ¬ idx u / L < (V₁.card + 1) / 2) :
    cRank V₁ V₂ idx L u = 2 * (V₁.card - 1 - idx u / L) + 1 := by
  unfold cRank cPerm; rw [if_pos hu, if_neg hr]

/-- Colour rank of a type-3 vertex (`u ∈ V₂`). -/
lemma cRank_V2 {V : Type*} [DecidableEq V] (V₁ V₂ : Finset V) (idx : V → ℕ) (L : ℕ)
    {u : V} (hu : u ∉ V₁) : cRank V₁ V₂ idx L u = V₁.card + idx u / L := by
  unfold cRank; rw [if_neg hu]

/-- A `V₁` vertex has colour rank `< |V₁|`. -/
lemma cRank_lt_card_V1 {V : Type*} [DecidableEq V] (V₁ V₂ : Finset V) (idx : V → ℕ) (L : ℕ)
    (hrank1 : ∀ u ∈ V₁, idx u / L < V₁.card) {u : V} (hu : u ∈ V₁) :
    cRank V₁ V₂ idx L u < V₁.card := by
  unfold cRank; rw [if_pos hu]; exact cPerm_lt (hrank1 u hu)

/-- A non-`V₁` vertex has colour rank `≥ |V₁|`. -/
lemma cRank_ge_card_V2 {V : Type*} [DecidableEq V] (V₁ V₂ : Finset V) (idx : V → ℕ) (L : ℕ)
    {u : V} (hu : u ∉ V₁) : V₁.card ≤ cRank V₁ V₂ idx L u := by
  unfold cRank; rw [if_neg hu]; exact Nat.le_add_right _ _

/-- Strict monotonicity of the colour index in the colour rank of the anchor. -/
lemma cCiv_lt_of_crank_lt {V : Type*} [Fintype V] [DecidableEq V] (leaves V₁ V₂ : Finset V)
    (idx : V → ℕ) (L : ℕ) (anchor : V → V) {x y : V} (hx : x ∈ leaves)
    (hlt : cRank V₁ V₂ idx L (anchor x) < cRank V₁ V₂ idx L (anchor y)) :
    cCiv leaves V₁ V₂ idx L anchor x < cCiv leaves V₁ V₂ idx L anchor y := by
  have hkey : cKey V₁ V₂ idx L anchor x < cKey V₁ V₂ idx L anchor y := by
    unfold cKey
    have := (Fintype.equivFin V x).2
    nlinarith [(Fintype.equivFin V x).2, (Fintype.equivFin V y).2]
  exact rank_lt_of_key_lt leaves (cKey V₁ V₂ idx L anchor) hx hkey

/-- A lower bound for a sum of fan sizes over a subset of `V₁ ∪ V₂`. -/
lemma sum_cDeg_ge {V : Type*} [Fintype V] [DecidableEq V] (leaves V₁ V₂ : Finset V)
    (anchor : V → V) (L : ℕ) (s : Finset V) (hs : s ⊆ V₁ ∪ V₂)
    (hdeg : ∀ w ∈ V₁ ∪ V₂, 100 * L ≤ cDeg leaves anchor w) :
    s.card * (100 * L) ≤ ∑ w ∈ s, cDeg leaves anchor w := by
  calc s.card * (100 * L) = ∑ _w ∈ s, 100 * L := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ w ∈ s, cDeg leaves anchor w := Finset.sum_le_sum (fun w hw => hdeg w (hs hw))

/-
**Type-1 colour-index gap.** For two type-1 leaves whose anchors have position ranks
`r_x < r_y`, the colour index of `y` exceeds that of `x` by more than the position gap
`idx(anchor y) − idx(anchor x)` (an intervening type-2 fan of `≥ 100·L` colours dominates
the `< 3·L` position gap).
-/
lemma civ_gap_type1 {V : Type*} [Fintype V] [DecidableEq V] (leaves V₁ V₂ : Finset V)
    (idx : V → ℕ) (L : ℕ) (anchor : V → V) (hL : 1 ≤ L)
    (hanchor_big : ∀ x ∈ leaves, anchor x ∈ V₁ ∪ V₂)
    (hkey : Set.InjOn (cKey V₁ V₂ idx L anchor) ↑leaves)
    (hcrank : Set.InjOn (cRank V₁ V₂ idx L) ↑(V₁ ∪ V₂))
    (hrank1 : ∀ u ∈ V₁, idx u / L < V₁.card)
    (hblk1 : ∀ u ∈ V₁, ∀ v ∈ V₁, u ≠ v → idx u / L ≠ idx v / L)
    (hdeg : ∀ w ∈ V₁ ∪ V₂, 100 * L ≤ cDeg leaves anchor w)
    {x y : V} (hx : x ∈ leaves) (hy : y ∈ leaves)
    (hux : anchor x ∈ V₁) (huy : anchor y ∈ V₁)
    (h1x : idx (anchor x) / L < (V₁.card + 1) / 2)
    (h1y : idx (anchor y) / L < (V₁.card + 1) / 2)
    (hrxy : idx (anchor x) / L < idx (anchor y) / L) :
    cCiv leaves V₁ V₂ idx L anchor x + (idx (anchor y) - idx (anchor x)) + 1
      ≤ cCiv leaves V₁ V₂ idx L anchor y := by
  -- Apply `cCiv_diff_ge_between leaves V₁ V₂ idx L anchor hanchor_big hkey hx hy` with the crank inequality.
  have h_sum : cCiv leaves V₁ V₂ idx L anchor x
            + ∑ w ∈ (V₁.filter (fun w => cRank V₁ V₂ idx L (anchor x) < cRank V₁ V₂ idx L w ∧ cRank V₁ V₂ idx L w < cRank V₁ V₂ idx L (anchor y))),
              cDeg leaves anchor w
            ≤ cCiv leaves V₁ V₂ idx L anchor y := by
              refine' le_trans _ ( cCiv_diff_ge_between leaves V₁ V₂ idx L anchor hanchor_big hkey hx hy _ );
              · gcongr;
                exact Finset.subset_union_left;
              · unfold cRank; simp +decide [ *, cPerm ] ;
  -- Apply `sum_cDeg_ge` to bound the sum of fan sizes.
  have h_sum_bound : ∑ w ∈ (V₁.filter (fun w => cRank V₁ V₂ idx L (anchor x) < cRank V₁ V₂ idx L w ∧ cRank V₁ V₂ idx L w < cRank V₁ V₂ idx L (anchor y))), cDeg leaves anchor w ≥ (2 * ((idx (anchor y) / L) - (idx (anchor x) / L)) - 1) * (100 * L) := by
    have h_card : (V₁.filter (fun w => cRank V₁ V₂ idx L (anchor x) < cRank V₁ V₂ idx L w ∧ cRank V₁ V₂ idx L w < cRank V₁ V₂ idx L (anchor y))).card = 2 * ((idx (anchor y) / L) - (idx (anchor x) / L)) - 1 := by
      convert card_filter_between_image ( fun w => cRank V₁ V₂ idx L w ) V₁ _ _ _ _ using 1;
      · rw [ cRank_type1, cRank_type1 ] <;> omega;
      · exact hcrank.mono ( Finset.subset_union_left );
      · convert cRank_image_V1 V₁ V₂ idx L hrank1 hblk1 using 1;
      · grind (instances := 20000) (splits := 500) (gen := 500) +locals;
      · grind (instances := 20000) (splits := 500) (gen := 500) +suggestions;
    exact h_card ▸ le_trans ( by simp +decide [ mul_comm ] ) ( Finset.sum_le_sum fun w hw => hdeg w <| Finset.mem_union_left _ <| Finset.mem_filter.mp hw |>.1 );
  rw [ tsub_mul ] at h_sum_bound;
  rw [ ge_iff_le, tsub_le_iff_right ] at h_sum_bound;
  nlinarith [ Nat.div_add_mod ( idx ( anchor y ) ) L, Nat.mod_lt ( idx ( anchor y ) ) ( by linarith : 0 < L ), Nat.div_mul_le_self ( idx ( anchor x ) ) L, Nat.sub_add_cancel ( show idx ( anchor x ) ≤ idx ( anchor y ) from le_of_not_gt fun h => by { exact hrxy.not_ge ( Nat.div_le_div_right h.le ) } ), Nat.sub_add_cancel ( show idx ( anchor x ) / L ≤ idx ( anchor y ) / L from Nat.div_le_div_right ( le_of_not_gt fun h => by { exact hrxy.not_ge ( Nat.div_le_div_right h.le ) } ) ) ]

/-
**Type-2 colour-index gap.** For two type-2 leaves whose anchors have position ranks
`r_x < r_y`, the colour index of `x` exceeds that of `y` by more than the position gap
(type-2 fans are placed in *reversed* colour order, so higher position rank means lower
colour index; an intervening fan of `≥ 100·L` colours still dominates).
-/
lemma civ_gap_type2 {V : Type*} [Fintype V] [DecidableEq V] (leaves V₁ V₂ : Finset V)
    (idx : V → ℕ) (L : ℕ) (anchor : V → V) (hL : 1 ≤ L)
    (hanchor_big : ∀ x ∈ leaves, anchor x ∈ V₁ ∪ V₂)
    (hkey : Set.InjOn (cKey V₁ V₂ idx L anchor) ↑leaves)
    (hcrank : Set.InjOn (cRank V₁ V₂ idx L) ↑(V₁ ∪ V₂))
    (hrank1 : ∀ u ∈ V₁, idx u / L < V₁.card)
    (hblk1 : ∀ u ∈ V₁, ∀ v ∈ V₁, u ≠ v → idx u / L ≠ idx v / L)
    (hdeg : ∀ w ∈ V₁ ∪ V₂, 100 * L ≤ cDeg leaves anchor w)
    {x y : V} (hx : x ∈ leaves) (hy : y ∈ leaves)
    (hux : anchor x ∈ V₁) (huy : anchor y ∈ V₁)
    (h2x : ¬ idx (anchor x) / L < (V₁.card + 1) / 2)
    (h2y : ¬ idx (anchor y) / L < (V₁.card + 1) / 2)
    (hrxy : idx (anchor x) / L < idx (anchor y) / L) :
    cCiv leaves V₁ V₂ idx L anchor y + (idx (anchor y) - idx (anchor x)) + 1
      ≤ cCiv leaves V₁ V₂ idx L anchor x := by
  refine' le_trans _ ( cCiv_diff_ge_between leaves V₁ V₂ idx L anchor hanchor_big hkey hy hx _ );
  · -- Let's simplify the goal using the fact that multiplication by a constant out of the sum can be taken outside.
    suffices h_suff : (idx (anchor y) - idx (anchor x)) + 1 ≤ (∑ w ∈ V₁.filter (fun w => cRank V₁ V₂ idx L (anchor y) < cRank V₁ V₂ idx L w ∧ cRank V₁ V₂ idx L w < cRank V₁ V₂ idx L (anchor x)), cDeg leaves anchor w) by
      convert Nat.add_le_add_left h_suff ( cCiv leaves V₁ V₂ idx L anchor y ) using 1;
      refine' congr rfl ( Finset.sum_subset _ _ ) <;> simp +contextual [ Finset.subset_iff ];
      grind (instances := 20000) (splits := 500) (gen := 500) +suggestions;
    refine' le_trans _ ( Finset.sum_le_sum fun w hw => hdeg w <| Finset.mem_union_left _ <| Finset.mem_filter.mp hw |>.1 );
    simp +zetaDelta at *;
    rw [ card_filter_between_image ];
    · unfold cRank; simp +decide [ *, cPerm ] ;
      split_ifs <;> try omega;
      rw [ tsub_tsub, tsub_mul ];
      rw [ lt_tsub_iff_left ];
      nlinarith [ Nat.div_add_mod ( idx ( anchor y ) ) L, Nat.mod_lt ( idx ( anchor y ) ) hL, Nat.div_mul_le_self ( idx ( anchor x ) ) L, Nat.sub_add_cancel ( show idx ( anchor x ) ≤ idx ( anchor y ) from le_of_not_gt fun h => by { exact hrxy.not_ge ( Nat.div_le_div_right h.le ) } ), Nat.sub_add_cancel ( show idx ( anchor x ) / L ≤ V₁.card - 1 from Nat.le_sub_one_of_lt ( hrank1 _ hux ) ), Nat.sub_add_cancel ( show idx ( anchor y ) / L ≤ V₁.card - 1 from Nat.le_sub_one_of_lt ( hrank1 _ huy ) ) ];
    · exact hcrank.mono ( by aesop_cat );
    · convert cRank_image_V1 V₁ V₂ idx L hrank1 hblk1 using 1;
    · grind (instances := 20000) (splits := 500) (gen := 500) +suggestions;
    · grind (instances := 20000) (splits := 500) (gen := 500) +locals;
  · grind (instances := 20000) (splits := 500) (gen := 500) +suggestions

/-
**Type-1 clearance.** The colour index of a type-1 leaf is at least `100·L` times its
anchor's position rank (there are that many smaller-rank fans below it in colour).
-/
lemma cCiv_ge_type1 {V : Type*} [Fintype V] [DecidableEq V] (leaves V₁ V₂ : Finset V)
    (idx : V → ℕ) (L : ℕ) (anchor : V → V)
    (hanchor_big : ∀ x ∈ leaves, anchor x ∈ V₁ ∪ V₂)
    (hcrank : Set.InjOn (cRank V₁ V₂ idx L) ↑(V₁ ∪ V₂))
    (hrank1 : ∀ u ∈ V₁, idx u / L < V₁.card)
    (hblk1 : ∀ u ∈ V₁, ∀ v ∈ V₁, u ≠ v → idx u / L ≠ idx v / L)
    (hdeg : ∀ w ∈ V₁ ∪ V₂, 100 * L ≤ cDeg leaves anchor w)
    {x : V} (hx : x ∈ leaves) (hux : anchor x ∈ V₁)
    (h1x : idx (anchor x) / L < (V₁.card + 1) / 2) :
    100 * L * (idx (anchor x) / L) ≤ cCiv leaves V₁ V₂ idx L anchor x := by
  refine' le_trans _ ( cCiv_ge_below leaves V₁ V₂ idx L anchor hanchor_big hx );
  refine' le_trans _ ( Finset.sum_le_sum fun w hw => hdeg w <| Finset.mem_filter.mp hw |>.1 );
  rw [ Finset.sum_const, smul_eq_mul, mul_comm ];
  have h_card : (V₁.filter (fun w => cRank V₁ V₂ idx L w < cRank V₁ V₂ idx L (anchor x))).card = 2 * (idx (anchor x) / L) := by
    convert card_filter_lt_image_eq ( fun w => cRank V₁ V₂ idx L w ) V₁ _ _ _ using 1;
    · exact Eq.symm ( cRank_type1 V₁ V₂ idx L hux h1x );
    · exact hcrank.mono ( Finset.subset_union_left );
    · exact cRank_image_V1 V₁ V₂ idx L hrank1 hblk1;
    · unfold cRank cPerm; simp +decide [ *, cPerm ] ; omega;
  rw [ show { w ∈ V₁ ∪ V₂ | cRank V₁ V₂ idx L w < cRank V₁ V₂ idx L ( anchor x ) } = { w ∈ V₁ | cRank V₁ V₂ idx L w < cRank V₁ V₂ idx L ( anchor x ) } from ?_ ] ; nlinarith [ Nat.zero_le ( idx ( anchor x ) / L ), Nat.zero_le L ] ;
  ext w; simp [Finset.inter_filter, Finset.mem_union];
  unfold cRank; simp +decide [ *, cPerm ] ;
  lia

/-
**Type-2 clearance.** The colour index of a type-2 leaf is at least `100·L` times
`|V₁| − r` (its reversed colour rank has that many smaller-rank fans below it).
-/
lemma cCiv_ge_type2 {V : Type*} [Fintype V] [DecidableEq V] (leaves V₁ V₂ : Finset V)
    (idx : V → ℕ) (L : ℕ) (anchor : V → V)
    (hanchor_big : ∀ x ∈ leaves, anchor x ∈ V₁ ∪ V₂)
    (hcrank : Set.InjOn (cRank V₁ V₂ idx L) ↑(V₁ ∪ V₂))
    (hrank1 : ∀ u ∈ V₁, idx u / L < V₁.card)
    (hblk1 : ∀ u ∈ V₁, ∀ v ∈ V₁, u ≠ v → idx u / L ≠ idx v / L)
    (hdeg : ∀ w ∈ V₁ ∪ V₂, 100 * L ≤ cDeg leaves anchor w)
    {x : V} (hx : x ∈ leaves) (hux : anchor x ∈ V₁)
    (h2x : ¬ idx (anchor x) / L < (V₁.card + 1) / 2) :
    100 * L * (V₁.card - idx (anchor x) / L) ≤ cCiv leaves V₁ V₂ idx L anchor x := by
  -- By `cCiv_ge_below`, we need to show that the sum of degrees for V₁ elements is at least `100 * L * (V₁.card - idx(anchor x)/L)`.
  have hsum_ge : ∑ w ∈ (V₁.filter (fun w => cRank V₁ V₂ idx L w < cRank V₁ V₂ idx L (anchor x))), cDeg leaves anchor w ≥ 100 * L * (V₁.card - idx (anchor x) / L) := by
    refine' le_trans _ ( Finset.sum_le_sum fun w hw => hdeg w <| Finset.mem_union_left _ <| Finset.mem_filter.mp hw |>.1 );
    have h_card : (V₁.filter (fun w => cRank V₁ V₂ idx L w < cRank V₁ V₂ idx L (anchor x))).card = 2 * (V₁.card - 1 - idx (anchor x) / L) + 1 := by
      convert card_filter_lt_image_eq ( fun w => cRank V₁ V₂ idx L w ) V₁ _ _ _ using 1;
      · exact Eq.symm ( cRank_type2 V₁ V₂ idx L hux h2x );
      · exact hcrank.mono ( Finset.subset_union_left );
      · exact cRank_image_V1 V₁ V₂ idx L hrank1 hblk1;
      · grind (instances := 20000) (splits := 500) (gen := 500) +locals;
    simp_all +decide [ mul_comm ];
    exact Nat.mul_le_mul_right _ ( by omega );
  refine' le_trans hsum_ge ( cCiv_ge_below leaves V₁ V₂ idx L anchor hanchor_big hx |> le_trans _ );
  refine' Finset.sum_le_sum_of_subset _;
  grind (instances := 20000) (splits := 500) (gen := 500) +suggestions

/-
The colour index of a leaf with anchor in `V₁` is below the whole `V₁` colour block.
-/
lemma cCiv_lt_sumV1 {V : Type*} [Fintype V] [DecidableEq V] (leaves V₁ V₂ : Finset V)
    (idx : V → ℕ) (L : ℕ) (anchor : V → V)
    (hrank1 : ∀ u ∈ V₁, idx u / L < V₁.card)
    {x : V} (hx : x ∈ leaves) (hux : anchor x ∈ V₁) :
    cCiv leaves V₁ V₂ idx L anchor x < ∑ u ∈ V₁, cDeg leaves anchor u := by
  by_contra h_contra
  exact (by
  contrapose! h_contra;
  refine' lt_of_lt_of_le ( Finset.card_lt_card _ ) _;
  exact leaves.filter ( fun y => anchor y ∈ V₁ );
  · constructor <;> simp_all +decide [ Finset.ssubset_def, Finset.subset_iff ];
    · intro y hy hxy
      have hcrk : cRank V₁ V₂ idx L (anchor y) ≤ cRank V₁ V₂ idx L (anchor x) := by
        unfold cKey at hxy; nlinarith [ Fin.is_lt ( Fintype.equivFin V y ), Fin.is_lt ( Fintype.equivFin V x ) ] ;
      have hcrk_lt : cRank V₁ V₂ idx L (anchor y) < V₁.card := by
        exact lt_of_le_of_lt hcrk ( cRank_lt_card_V1 V₁ V₂ idx L hrank1 hux )
      have hanchor_y : anchor y ∈ V₁ := by
        unfold cRank at hcrk_lt; aesop;
      exact hanchor_y;
    · exact ⟨ x, hx, hux, le_rfl ⟩;
  · simp +decide only [cDeg];
    rw [ ← Finset.card_biUnion ] ; exact Finset.card_mono <| by aesop_cat;
    exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z hz₁ hz₂ => hxy <| by aesop;)

/-
The colour index of a leaf with anchor in `V₂` is at least the whole `V₁` colour
block (all `V₁` leaves precede it in colour).
-/
lemma cCiv_ge_sumV1_of_V2 {V : Type*} [Fintype V] [DecidableEq V] (leaves V₁ V₂ : Finset V)
    (idx : V → ℕ) (L : ℕ) (anchor : V → V) (hV₁V₂ : Disjoint V₁ V₂)
    (hrank1 : ∀ u ∈ V₁, idx u / L < V₁.card)
    (hanchor_big : ∀ x ∈ leaves, anchor x ∈ V₁ ∪ V₂)
    {x : V} (hx : x ∈ leaves) (hux : anchor x ∈ V₂) :
    ∑ u ∈ V₁, cDeg leaves anchor u ≤ cCiv leaves V₁ V₂ idx L anchor x := by
  refine' le_trans _ ( cCiv_ge_below leaves V₁ V₂ idx L anchor hanchor_big hx );
  refine' Finset.sum_le_sum_of_subset _;
  intro u hu; simp only [Finset.mem_filter] at *;
  have hax : anchor x ∉ V₁ := fun h => Finset.disjoint_left.mp hV₁V₂ h hux;
  exact ⟨Finset.mem_union_left V₂ hu, lt_of_lt_of_le (cRank_lt_card_V1 V₁ V₂ idx L hrank1 hu) (cRank_ge_card_V2 V₁ V₂ idx L hax)⟩

/-! ## Geometry of the leaf positions -/

section Geometry

variable {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
  (leaves V₁ V₂ : Finset V) (idx : V → ℕ) (L : ℕ) (anchor : V → V)
  (g : V → Fin (2 * n + 1)) (col : V → Fin n) (ap₁ ap₂ a₀ : Fin (2 * n + 1)) (slack : ℕ)

/-
**Type-1 position (down fan).** No underflow, positive, and below the anchor.
-/
lemma cPosVal_type1
    (hn : 1000000 ≤ n) (hap₁ : ap₁.val = 70 * n / 100)
    (hrank1 : ∀ u ∈ V₁, idx u / L < V₁.card)
    (hgV₁ : ∀ v ∈ V₁, (g v).val = ap₁.val + idx v ∧ idx v < V₁.card * L)
    (hV₁L : V₁.card * L ≤ n / 100)
    (hV₁le : ∑ u ∈ V₁, cDeg leaves anchor u ≤ 2 * n / 3)
    (hub : ∀ z ∈ leaves, (col z).val ≤ cCiv leaves V₁ V₂ idx L anchor z + slack)
    (hslack : slack ≤ n / 100)
    {x : V} (hx : x ∈ leaves) (hux : anchor x ∈ V₁)
    (h1x : idx (anchor x) / L < (V₁.card + 1) / 2) :
    cPosVal V₁ V₂ idx L g anchor (fun z => (col z).val) x + ((col x).val + 1)
        = (g (anchor x)).val
      ∧ 1 ≤ cPosVal V₁ V₂ idx L g anchor (fun z => (col z).val) x
      ∧ cPosVal V₁ V₂ idx L g anchor (fun z => (col z).val) x < (g (anchor x)).val := by
  unfold cPosVal; simp +decide [ * ] ;
  have := hub x hx;
  have := cCiv_lt_sumV1 leaves V₁ V₂ idx L anchor hrank1 hx hux; omega;

/-
**Type-1 vs. `V₁` core.** A type-1 leaf position never coincides with a `V₁` vertex.
-/
lemma cPosVal_type1_ne_V1
    (hn : 1000000 ≤ n) (hap₁ : ap₁.val = 70 * n / 100)
    (hanchor_big : ∀ x ∈ leaves, anchor x ∈ V₁ ∪ V₂)
    (hcrank : Set.InjOn (cRank V₁ V₂ idx L) ↑(V₁ ∪ V₂))
    (hrank1 : ∀ u ∈ V₁, idx u / L < V₁.card)
    (hblk1 : ∀ u ∈ V₁, ∀ v ∈ V₁, u ≠ v → idx u / L ≠ idx v / L)
    (hdeg : ∀ w ∈ V₁ ∪ V₂, 100 * L ≤ cDeg leaves anchor w)
    (hgV₁ : ∀ v ∈ V₁, (g v).val = ap₁.val + idx v ∧ idx v < V₁.card * L)
    (hV₁L : V₁.card * L ≤ n / 100)
    (hV₁le : ∑ u ∈ V₁, cDeg leaves anchor u ≤ 2 * n / 3)
    (hlb : ∀ z ∈ leaves, cCiv leaves V₁ V₂ idx L anchor z ≤ (col z).val)
    (hub : ∀ z ∈ leaves, (col z).val ≤ cCiv leaves V₁ V₂ idx L anchor z + slack)
    (hslack : slack ≤ n / 100)
    {x : V} (hx : x ∈ leaves) (hux : anchor x ∈ V₁)
    (h1x : idx (anchor x) / L < (V₁.card + 1) / 2) {w : V} (hw : w ∈ V₁) :
    cPosVal V₁ V₂ idx L g anchor (fun z => (col z).val) x ≠ (g w).val := by
  by_contra h_contra;
  -- By definition of `cPosVal`, we know that `cPosVal V₁ V₂ idx L g anchor (fun z => (col z).val) x < (g (anchor x)).val`.
  have h_cPosVal_lt_gAnchor : cPosVal V₁ V₂ idx L g anchor (fun z => (col z).val) x < (g (anchor x)).val := by
    apply (cPosVal_type1 leaves V₁ V₂ idx L anchor g col ap₁ slack hn hap₁ hrank1 (fun v hv => ⟨(hgV₁ v hv).left, (hgV₁ v hv).right⟩) hV₁L hV₁le hub hslack hx hux h1x).right.right;
  by_cases hL : L = 0;
  · grind (instances := 20000) (splits := 500) (gen := 500);
  · by_cases hcase : idx (anchor x) / L = 0;
    · simp_all +decide [ Nat.div_eq_zero_iff ];
      exact hblk1 ( anchor x ) hux w hw ( by aesop ) ( by rw [ Nat.div_eq_of_lt, Nat.div_eq_of_lt ] <;> linarith [ Nat.pos_of_ne_zero hL ] );
    · have h_contra : idx (anchor x) - idx w ≥ 100 * L * (idx (anchor x) / L) + 1 := by
        have h_contra : (col x).val ≥ 100 * L * (idx (anchor x) / L) := by
          exact le_trans ( cCiv_ge_type1 leaves V₁ V₂ idx L anchor hanchor_big hcrank hrank1 hblk1 hdeg hx hux h1x ) ( hlb x hx );
        grind (instances := 20000) (splits := 500) (gen := 500) +locals;
      have h_contra : idx (anchor x) < (idx (anchor x) / L + 1) * L := by
        linarith [ Nat.div_add_mod ( idx ( anchor x ) ) L, Nat.mod_lt ( idx ( anchor x ) ) ( Nat.pos_of_ne_zero hL ) ];
      nlinarith only [ h_contra, ‹idx ( anchor x ) - idx w ≥ 100 * L * ( idx ( anchor x ) / L ) + 1›, Nat.sub_le ( idx ( anchor x ) ) ( idx w ), Nat.pos_of_ne_zero hcase, Nat.pos_of_ne_zero hL ]

/-
**Type-2 position (up fan).** No overflow, and strictly below `I₀` (`< 0.83n`).
-/
lemma cPosVal_type2
    (hn : 1000000 ≤ n) (hap₁ : ap₁.val = 70 * n / 100) (ha₀ : a₀.val = 83 * n / 100)
    (hrank1 : ∀ u ∈ V₁, idx u / L < V₁.card)
    (hgV₁ : ∀ v ∈ V₁, (g v).val = ap₁.val + idx v ∧ idx v < V₁.card * L)
    (hV₁L : V₁.card * L ≤ n / 100)
    (hV₁small : 2 ≤ V₁.card → ∑ u ∈ V₁, cDeg leaves anchor u ≤ n / 10)
    (hub : ∀ z ∈ leaves, (col z).val ≤ cCiv leaves V₁ V₂ idx L anchor z + slack)
    (hslack : slack ≤ n / 100)
    {x : V} (hx : x ∈ leaves) (hux : anchor x ∈ V₁)
    (h2x : ¬ idx (anchor x) / L < (V₁.card + 1) / 2) :
    cPosVal V₁ V₂ idx L g anchor (fun z => (col z).val) x
        = (g (anchor x)).val + ((col x).val + 1)
      ∧ cPosVal V₁ V₂ idx L g anchor (fun z => (col z).val) x < a₀.val := by
  -- By definition of $cPosVal$, we have $cPosVal V₁ V₂ idx L g anchor (fun z => (col z).val) x = (g (anchor x)).val + ((col x).val + 1)$.
  simp [cPosVal, h2x];
  -- Bound the colour value: `(col x).val ≤ cCiv ... x + slack` (`hub x hx`), `cCiv ... x < ∑ ... ≤ n/10` (`cCiv_lt_sumV1` + the `hV₁small` bound), `slack ≤ n/100` (`hslack`). So `(col x).val < n/10 + n/100`.
  have h_col_bound : (col x).val < n / 10 + n / 100 := by
    by_cases hV₁card : 2 ≤ V₁.card;
    · linarith [ hub x hx, hV₁small hV₁card, cCiv_lt_sumV1 leaves V₁ V₂ idx L anchor hrank1 hx hux, Nat.div_mul_le_self n 10, Nat.div_mul_le_self n 100 ];
    · grind (instances := 20000) (splits := 500) (gen := 500);
  grind (instances := 20000) (splits := 500) (gen := 500)

/-
**Type-2 vs. `V₁` core.** A type-2 leaf sits strictly above every `V₁` vertex.
-/
lemma cPosVal_type2_gt_V1
    (hn : 1000000 ≤ n) (hap₁ : ap₁.val = 70 * n / 100)
    (hanchor_big : ∀ x ∈ leaves, anchor x ∈ V₁ ∪ V₂)
    (hcrank : Set.InjOn (cRank V₁ V₂ idx L) ↑(V₁ ∪ V₂))
    (hrank1 : ∀ u ∈ V₁, idx u / L < V₁.card)
    (hblk1 : ∀ u ∈ V₁, ∀ v ∈ V₁, u ≠ v → idx u / L ≠ idx v / L)
    (hdeg : ∀ w ∈ V₁ ∪ V₂, 100 * L ≤ cDeg leaves anchor w)
    (hgV₁ : ∀ v ∈ V₁, (g v).val = ap₁.val + idx v ∧ idx v < V₁.card * L)
    (hV₁L : V₁.card * L ≤ n / 100)
    (hV₁small : 2 ≤ V₁.card → ∑ u ∈ V₁, cDeg leaves anchor u ≤ n / 10)
    (hlb : ∀ z ∈ leaves, cCiv leaves V₁ V₂ idx L anchor z ≤ (col z).val)
    (hub : ∀ z ∈ leaves, (col z).val ≤ cCiv leaves V₁ V₂ idx L anchor z + slack)
    (hslack : slack ≤ n / 100)
    {x : V} (hx : x ∈ leaves) (hux : anchor x ∈ V₁)
    (h2x : ¬ idx (anchor x) / L < (V₁.card + 1) / 2) {w : V} (hw : w ∈ V₁) :
    (g w).val < cPosVal V₁ V₂ idx L g anchor (fun z => (col z).val) x := by
  by_cases hL : L = 0;
  · grind (instances := 20000) (splits := 500) (gen := 500);
  · unfold cPosVal; simp +decide [ * ] ;
    have := cCiv_ge_type2 leaves V₁ V₂ idx L anchor hanchor_big hcrank hrank1 hblk1 hdeg hx hux h2x;
    nlinarith [ Nat.div_mul_le_self ( idx ( anchor x ) ) L, Nat.sub_add_cancel ( show idx ( anchor x ) / L ≤ V₁.card from le_of_lt ( hrank1 _ hux ) ), hlb x hx, Nat.pos_of_ne_zero hL, hgV₁ _ hw, hgV₁ _ hux, Nat.sub_add_cancel ( show 1 ≤ V₁.card from Finset.card_pos.mpr ⟨ _, hux ⟩ ) ]

/-
**Type-3 position (up fan into `[0.96n, 1.92n]`).**
-/
lemma cPosVal_type3
    (hn : 1000000 ≤ n) (hap₂ : ap₂.val = 91 * n / 100) (hV₁V₂ : Disjoint V₁ V₂)
    (hanchor_big : ∀ x ∈ leaves, anchor x ∈ V₁ ∪ V₂)
    (hrank1 : ∀ u ∈ V₁, idx u / L < V₁.card)
    (hgV₂ : ∀ v ∈ V₂, (g v).val = ap₂.val + idx v ∧ idx v < V₂.card * L)
    (hV₂L : V₂.card * L ≤ n / 100)
    (hV₁gt : n / 20 < ∑ u ∈ V₁, cDeg leaves anchor u)
    (hlb : ∀ z ∈ leaves, cCiv leaves V₁ V₂ idx L anchor z ≤ (col z).val)
    {x : V} (hx : x ∈ leaves) (hux : anchor x ∈ V₂) :
    cPosVal V₁ V₂ idx L g anchor (fun z => (col z).val) x
        = (g (anchor x)).val + ((col x).val + 1)
      ∧ 96 * n / 100 ≤ cPosVal V₁ V₂ idx L g anchor (fun z => (col z).val) x
      ∧ cPosVal V₁ V₂ idx L g anchor (fun z => (col z).val) x < 2 * n + 1 := by
  unfold cPosVal; simp +decide [ * ] ;
  split_ifs;
  · exact False.elim ( Finset.disjoint_left.mp hV₁V₂ ( by tauto ) hux );
  · refine' ⟨ _, _, _ ⟩;
    · grind (instances := 20000) (splits := 500) (gen := 500);
    · have := hlb x hx;
      have := cCiv_ge_sumV1_of_V2 leaves V₁ V₂ idx L anchor hV₁V₂ hrank1 hanchor_big hx hux; omega;
    · grind (instances := 20000) (splits := 500) (gen := 500)

/-
Every leaf position value is in range `[0, 2n+1)`.
-/
lemma cPosVal_lt
    (hn : 1000000 ≤ n) (hap₁ : ap₁.val = 70 * n / 100) (hap₂ : ap₂.val = 91 * n / 100)
    (ha₀ : a₀.val = 83 * n / 100) (hV₁V₂ : Disjoint V₁ V₂)
    (hanchor_big : ∀ x ∈ leaves, anchor x ∈ V₁ ∪ V₂)
    (hrank1 : ∀ u ∈ V₁, idx u / L < V₁.card)
    (hgV₁ : ∀ v ∈ V₁, (g v).val = ap₁.val + idx v ∧ idx v < V₁.card * L)
    (hgV₂ : ∀ v ∈ V₂, (g v).val = ap₂.val + idx v ∧ idx v < V₂.card * L)
    (hV₁L : V₁.card * L ≤ n / 100) (hV₂L : V₂.card * L ≤ n / 100)
    (hV₁le : ∑ u ∈ V₁, cDeg leaves anchor u ≤ 2 * n / 3)
    (hV₁small : 2 ≤ V₁.card → ∑ u ∈ V₁, cDeg leaves anchor u ≤ n / 10)
    (hV₁gt : n / 20 < ∑ u ∈ V₁, cDeg leaves anchor u)
    (hlb : ∀ z ∈ leaves, cCiv leaves V₁ V₂ idx L anchor z ≤ (col z).val)
    (hub : ∀ z ∈ leaves, (col z).val ≤ cCiv leaves V₁ V₂ idx L anchor z + slack)
    (hslack : slack ≤ n / 100)
    {x : V} (hx : x ∈ leaves) :
    cPosVal V₁ V₂ idx L g anchor (fun z => (col z).val) x < 2 * n + 1 := by
  by_cases h1x : idx ( anchor x ) / L < ( V₁.card + 1 ) / 2 <;> simp_all +decide only [cPosVal]; all_goals grind (instances := 20000) (splits := 500) (gen := 500)

/-- Injectivity of `idx` from injectivity of the block index `idx / L`. -/
lemma idx_lt_of_div_lt {a b L : ℕ} (hL : 1 ≤ L) (h : a / L < b / L) : a < b := by
  have h1 : a < (a / L + 1) * L := by
    have := Nat.div_add_mod a L; have := Nat.mod_lt a (show 0 < L by omega); nlinarith
  have h2 : (a / L + 1) * L ≤ (b / L) * L := Nat.mul_le_mul_right L (by omega)
  have h3 : (b / L) * L ≤ b := Nat.div_mul_le_self b L
  omega

/-- Strict monotonicity of the colour index in the `V₂` position rank. -/
lemma cCiv_lt_of_rank2_lt {V : Type*} [Fintype V] [DecidableEq V] (leaves V₁ V₂ : Finset V)
    (idx : V → ℕ) (L : ℕ) (anchor : V → V) {x y : V} (hx : x ∈ leaves)
    (hux : anchor x ∉ V₁) (huy : anchor y ∉ V₁)
    (h : idx (anchor x) / L < idx (anchor y) / L) :
    cCiv leaves V₁ V₂ idx L anchor x < cCiv leaves V₁ V₂ idx L anchor y := by
  apply cCiv_lt_of_crank_lt leaves V₁ V₂ idx L anchor hx
  rw [cRank_V2 V₁ V₂ idx L hux, cRank_V2 V₁ V₂ idx L huy]; omega

/-
Same-side injectivity for two `V₁`-anchored leaves.
-/
lemma cPosVal_injOn_V1V1
    (hn : 1000000 ≤ n) (hap₁ : ap₁.val = 70 * n / 100) (ha₀ : a₀.val = 83 * n / 100)
    (hL : 1 ≤ L)
    (hanchor_big : ∀ x ∈ leaves, anchor x ∈ V₁ ∪ V₂)
    (hkey : Set.InjOn (cKey V₁ V₂ idx L anchor) ↑leaves)
    (hcrank : Set.InjOn (cRank V₁ V₂ idx L) ↑(V₁ ∪ V₂))
    (hrank1 : ∀ u ∈ V₁, idx u / L < V₁.card)
    (hblk1 : ∀ u ∈ V₁, ∀ v ∈ V₁, u ≠ v → idx u / L ≠ idx v / L)
    (hdeg : ∀ w ∈ V₁ ∪ V₂, 100 * L ≤ cDeg leaves anchor w)
    (hgV₁ : ∀ v ∈ V₁, (g v).val = ap₁.val + idx v ∧ idx v < V₁.card * L)
    (hV₁L : V₁.card * L ≤ n / 100)
    (hV₁le : ∑ u ∈ V₁, cDeg leaves anchor u ≤ 2 * n / 3)
    (hV₁small : 2 ≤ V₁.card → ∑ u ∈ V₁, cDeg leaves anchor u ≤ n / 10)
    (hlb : ∀ z ∈ leaves, cCiv leaves V₁ V₂ idx L anchor z ≤ (col z).val)
    (hgap : ∀ z ∈ leaves, ∀ z' ∈ leaves, cCiv leaves V₁ V₂ idx L anchor z
      ≤ cCiv leaves V₁ V₂ idx L anchor z' →
      (col z).val + (cCiv leaves V₁ V₂ idx L anchor z' - cCiv leaves V₁ V₂ idx L anchor z)
        ≤ (col z').val)
    (hub : ∀ z ∈ leaves, (col z).val ≤ cCiv leaves V₁ V₂ idx L anchor z + slack)
    (hslack : slack ≤ n / 100) (hcolinj : Set.InjOn col ↑leaves)
    {x y : V} (hx : x ∈ leaves) (hy : y ∈ leaves) (hux : anchor x ∈ V₁) (huy : anchor y ∈ V₁)
    (hxy : cPosVal V₁ V₂ idx L g anchor (fun z => (col z).val) x
      = cPosVal V₁ V₂ idx L g anchor (fun z => (col z).val) y) : x = y := by
  by_cases h1x : idx ( anchor x ) / L < ( V₁.card + 1 ) / 2 <;> by_cases h1y : idx ( anchor y ) / L < ( V₁.card + 1 ) / 2;
  · by_cases h : idx ( anchor x ) / L = idx ( anchor y ) / L;
    · have h_anchor_eq : anchor x = anchor y := by
        exact Classical.not_not.1 fun hxy => hblk1 _ hux _ huy hxy h;
      have := cPosVal_type1 leaves V₁ V₂ idx L anchor g col ap₁ slack hn hap₁ hrank1 ( fun v hv => ⟨ hgV₁ v hv |>.1, hgV₁ v hv |>.2 ⟩ ) hV₁L hV₁le hub hslack hx hux h1x; have := cPosVal_type1 leaves V₁ V₂ idx L anchor g col ap₁ slack hn hap₁ hrank1 ( fun v hv => ⟨ hgV₁ v hv |>.1, hgV₁ v hv |>.2 ⟩ ) hV₁L hV₁le hub hslack hy huy h1y; simp_all +decide ;
      exact hcolinj hx hy ( Fin.ext <| by linarith );
    · cases lt_or_gt_of_ne h;
      · have := civ_gap_type1 leaves V₁ V₂ idx L anchor hL hanchor_big hkey hcrank hrank1 hblk1 hdeg hx hy hux huy h1x h1y ‹_›;
        have := cPosVal_type1 leaves V₁ V₂ idx L anchor g col ap₁ slack hn hap₁ hrank1 ( fun v hv => ⟨ hgV₁ v hv |>.1, hgV₁ v hv |>.2 ⟩ ) hV₁L hV₁le hub hslack hx hux h1x;
        have := cPosVal_type1 leaves V₁ V₂ idx L anchor g col ap₁ slack hn hap₁ hrank1 ( fun v hv => ⟨ hgV₁ v hv |>.1, hgV₁ v hv |>.2 ⟩ ) hV₁L hV₁le hub hslack hy huy h1y;
        grind (instances := 20000) (splits := 500) (gen := 500);
      · have := civ_gap_type1 leaves V₁ V₂ idx L anchor hL hanchor_big hkey hcrank hrank1 hblk1 hdeg hy hx huy hux h1y h1x ‹_›;
        have := cPosVal_type1 leaves V₁ V₂ idx L anchor g col ap₁ slack hn hap₁ hrank1 ( fun v hv => ⟨ hgV₁ v hv |>.1, hgV₁ v hv |>.2 ⟩ ) hV₁L hV₁le hub hslack hx hux h1x;
        have := cPosVal_type1 leaves V₁ V₂ idx L anchor g col ap₁ slack hn hap₁ hrank1 ( fun v hv => ⟨ hgV₁ v hv |>.1, hgV₁ v hv |>.2 ⟩ ) hV₁L hV₁le hub hslack hy huy h1y;
        grind (instances := 20000) (splits := 500) (gen := 500) +splitImp;
  · have h_contra : (g (anchor x)).val < cPosVal V₁ V₂ idx L g anchor (fun z => (col z).val) y := by
      apply cPosVal_type2_gt_V1 leaves V₁ V₂ idx L anchor g col ap₁ slack hn hap₁ hanchor_big hcrank hrank1 hblk1 hdeg hgV₁ hV₁L hV₁small hlb hub hslack hy huy h1y hux;
    unfold cPosVal at *; simp_all +decide ;
    grind (instances := 20000) (splits := 500) (gen := 500);
  · have h_contra : cPosVal V₁ V₂ idx L g anchor (fun z => (col z).val) x > (g (anchor y)).val := by
      apply cPosVal_type2_gt_V1;
      all_goals try assumption;
    grind (instances := 20000) (splits := 500) (gen := 500) +locals;
  · by_cases h : idx ( anchor x ) / L < idx ( anchor y ) / L <;> simp_all +decide only [cPosVal];
    · have := civ_gap_type2 leaves V₁ V₂ idx L anchor hL hanchor_big hkey hcrank hrank1 hblk1 hdeg hx hy hux huy h1x h1y h;
      grind (instances := 20000) (splits := 500) (gen := 500);
    · by_cases h : idx ( anchor x ) / L = idx ( anchor y ) / L;
      · have := hblk1 ( anchor x ) hux ( anchor y ) huy; simp_all +decide ;
        exact hcolinj hx hy ( Fin.ext hxy );
      · have := civ_gap_type2 leaves V₁ V₂ idx L anchor hL hanchor_big hkey hcrank hrank1 hblk1 hdeg hy hx huy hux ( by omega ) ( by omega ) ( by omega );
        grind (instances := 20000) (splits := 500) (gen := 500)

/-
Same-side injectivity for two `V₂`-anchored leaves.
-/
lemma cPosVal_injOn_V2V2
    (hn : 1000000 ≤ n) (hap₂ : ap₂.val = 91 * n / 100) (hL : 1 ≤ L) (hV₁V₂ : Disjoint V₁ V₂)
    (hanchor_big : ∀ x ∈ leaves, anchor x ∈ V₁ ∪ V₂)
    (hblk2 : ∀ u ∈ V₂, ∀ v ∈ V₂, u ≠ v → idx u / L ≠ idx v / L)
    (hgV₂ : ∀ v ∈ V₂, (g v).val = ap₂.val + idx v ∧ idx v < V₂.card * L)
    (hlb : ∀ z ∈ leaves, cCiv leaves V₁ V₂ idx L anchor z ≤ (col z).val)
    (hgap : ∀ z ∈ leaves, ∀ z' ∈ leaves, cCiv leaves V₁ V₂ idx L anchor z
      ≤ cCiv leaves V₁ V₂ idx L anchor z' →
      (col z).val + (cCiv leaves V₁ V₂ idx L anchor z' - cCiv leaves V₁ V₂ idx L anchor z)
        ≤ (col z').val)
    (hcolinj : Set.InjOn col ↑leaves)
    {x y : V} (hx : x ∈ leaves) (hy : y ∈ leaves) (hux : anchor x ∉ V₁) (huy : anchor y ∉ V₁)
    (hxy : cPosVal V₁ V₂ idx L g anchor (fun z => (col z).val) x
      = cPosVal V₁ V₂ idx L g anchor (fun z => (col z).val) y) : x = y := by
  by_cases hcase : idx (anchor x) / L = idx (anchor y) / L;
  · have h anchors : anchors = anchor x → anchors = anchor y := by
      grind (instances := 20000) (splits := 500) (gen := 500);
    contrapose! hxy; simp_all +decide [ cPosVal ] ;
    exact fun h => hxy <| hcolinj hx hy <| Fin.ext h;
  · cases lt_or_gt_of_ne hcase <;> simp_all +decide [ cPosVal ];
    · have h_contra : idx (anchor x) < idx (anchor y) := by
        exact idx_lt_of_div_lt hL ‹_›;
      have h_contra : cCiv leaves V₁ V₂ idx L anchor x < cCiv leaves V₁ V₂ idx L anchor y := by
        apply cCiv_lt_of_rank2_lt leaves V₁ V₂ idx L anchor hx hux huy ‹_›;
      grind (instances := 20000) (splits := 500) (gen := 500);
    · have := hgap y hy x hx ( cCiv_lt_of_rank2_lt leaves V₁ V₂ idx L anchor hy huy hux ‹_› |> le_of_lt );
      have := idx_lt_of_div_lt hL ‹_›;
      grind (instances := 20000) (splits := 500) (gen := 500)

/-
A `V₁`-anchored leaf sits strictly below any `V₂`-anchored (type-3) leaf.
-/
lemma cPosVal_lt_V1_V2
    (hn : 1000000 ≤ n) (hap₁ : ap₁.val = 70 * n / 100) (hap₂ : ap₂.val = 91 * n / 100)
    (ha₀ : a₀.val = 83 * n / 100) (hV₁V₂ : Disjoint V₁ V₂)
    (hanchor_big : ∀ x ∈ leaves, anchor x ∈ V₁ ∪ V₂)
    (hrank1 : ∀ u ∈ V₁, idx u / L < V₁.card)
    (hgV₁ : ∀ v ∈ V₁, (g v).val = ap₁.val + idx v ∧ idx v < V₁.card * L)
    (hgV₂ : ∀ v ∈ V₂, (g v).val = ap₂.val + idx v ∧ idx v < V₂.card * L)
    (hV₁L : V₁.card * L ≤ n / 100) (hV₂L : V₂.card * L ≤ n / 100)
    (hV₁le : ∑ u ∈ V₁, cDeg leaves anchor u ≤ 2 * n / 3)
    (hV₁small : 2 ≤ V₁.card → ∑ u ∈ V₁, cDeg leaves anchor u ≤ n / 10)
    (hV₁gt : n / 20 < ∑ u ∈ V₁, cDeg leaves anchor u)
    (hlb : ∀ z ∈ leaves, cCiv leaves V₁ V₂ idx L anchor z ≤ (col z).val)
    (hub : ∀ z ∈ leaves, (col z).val ≤ cCiv leaves V₁ V₂ idx L anchor z + slack)
    (hslack : slack ≤ n / 100)
    {x y : V} (hx : x ∈ leaves) (hy : y ∈ leaves) (hux : anchor x ∈ V₁) (huy : anchor y ∉ V₁) :
    cPosVal V₁ V₂ idx L g anchor (fun z => (col z).val) x
      < cPosVal V₁ V₂ idx L g anchor (fun z => (col z).val) y := by
  have h_cPosVal_y : 96 * n / 100 ≤ cPosVal V₁ V₂ idx L g anchor (fun z => (col z).val) y := by
    apply (cPosVal_type3 leaves V₁ V₂ idx L anchor g col ap₂ hn hap₂ hV₁V₂ hanchor_big hrank1 hgV₂ hV₂L hV₁gt hlb hy (by
    exact Or.resolve_left ( Finset.mem_union.mp ( hanchor_big y hy ) ) huy)).right.left;
  by_cases h1x : idx (anchor x) / L < (V₁.card + 1) / 2;
  · have := cPosVal_type1 leaves V₁ V₂ idx L anchor g col ap₁ slack hn hap₁ hrank1 ( fun v hv => ⟨ hgV₁ v hv |>.1, hgV₁ v hv |>.2 ⟩ ) hV₁L hV₁le hub hslack hx hux h1x;
    grind (instances := 20000) (splits := 500) (gen := 500);
  · have h_cPosVal_x : cPosVal V₁ V₂ idx L g anchor (fun z => (col z).val) x < a₀.val := by
      apply (cPosVal_type2 leaves V₁ V₂ idx L anchor g col ap₁ a₀ slack hn hap₁ ha₀ hrank1 hgV₁ hV₁L hV₁small hub hslack hx hux h1x).right;
    omega

/-- **Leaf position values are injective on the leaves.** -/
lemma cPosVal_injOn
    (hn : 1000000 ≤ n) (hap₁ : ap₁.val = 70 * n / 100) (hap₂ : ap₂.val = 91 * n / 100)
    (ha₀ : a₀.val = 83 * n / 100) (hL : 1 ≤ L) (hV₁V₂ : Disjoint V₁ V₂)
    (hanchor_big : ∀ x ∈ leaves, anchor x ∈ V₁ ∪ V₂)
    (hkey : Set.InjOn (cKey V₁ V₂ idx L anchor) ↑leaves)
    (hcrank : Set.InjOn (cRank V₁ V₂ idx L) ↑(V₁ ∪ V₂))
    (hrank1 : ∀ u ∈ V₁, idx u / L < V₁.card) (hrank2 : ∀ u ∈ V₂, idx u / L < V₂.card)
    (hblk1 : ∀ u ∈ V₁, ∀ v ∈ V₁, u ≠ v → idx u / L ≠ idx v / L)
    (hblk2 : ∀ u ∈ V₂, ∀ v ∈ V₂, u ≠ v → idx u / L ≠ idx v / L)
    (hdeg : ∀ w ∈ V₁ ∪ V₂, 100 * L ≤ cDeg leaves anchor w)
    (hgV₁ : ∀ v ∈ V₁, (g v).val = ap₁.val + idx v ∧ idx v < V₁.card * L)
    (hgV₂ : ∀ v ∈ V₂, (g v).val = ap₂.val + idx v ∧ idx v < V₂.card * L)
    (hV₁L : V₁.card * L ≤ n / 100) (hV₂L : V₂.card * L ≤ n / 100)
    (hV₁le : ∑ u ∈ V₁, cDeg leaves anchor u ≤ 2 * n / 3)
    (hV₁small : 2 ≤ V₁.card → ∑ u ∈ V₁, cDeg leaves anchor u ≤ n / 10)
    (hV₁gt : n / 20 < ∑ u ∈ V₁, cDeg leaves anchor u)
    (hlb : ∀ z ∈ leaves, cCiv leaves V₁ V₂ idx L anchor z ≤ (col z).val)
    (hgap : ∀ z ∈ leaves, ∀ z' ∈ leaves, cCiv leaves V₁ V₂ idx L anchor z
      ≤ cCiv leaves V₁ V₂ idx L anchor z' →
      (col z).val + (cCiv leaves V₁ V₂ idx L anchor z' - cCiv leaves V₁ V₂ idx L anchor z)
        ≤ (col z').val)
    (hub : ∀ z ∈ leaves, (col z).val ≤ cCiv leaves V₁ V₂ idx L anchor z + slack)
    (hslack : slack ≤ n / 100)
    (hcolinj : Set.InjOn col ↑leaves) :
    Set.InjOn (fun z => cPosVal V₁ V₂ idx L g anchor (fun w => (col w).val) z) ↑leaves := by
  intro x hx y hy hxy
  simp only at hxy
  rw [Finset.mem_coe] at hx hy
  by_cases hux : anchor x ∈ V₁ <;> by_cases huy : anchor y ∈ V₁
  · exact cPosVal_injOn_V1V1 leaves V₁ V₂ idx L anchor g col ap₁ a₀ slack hn hap₁ ha₀ hL
      hanchor_big hkey hcrank hrank1 hblk1 hdeg hgV₁ hV₁L hV₁le hV₁small hlb hgap hub hslack
      hcolinj hx hy hux huy hxy
  · exact absurd hxy (ne_of_lt (cPosVal_lt_V1_V2 leaves V₁ V₂ idx L anchor g col ap₁ ap₂ a₀
      slack hn hap₁ hap₂ ha₀ hV₁V₂ hanchor_big hrank1 hgV₁ hgV₂ hV₁L hV₂L hV₁le hV₁small hV₁gt
      hlb hub hslack hx hy hux huy))
  · exact (absurd hxy.symm (ne_of_lt (cPosVal_lt_V1_V2 leaves V₁ V₂ idx L anchor g col ap₁ ap₂ a₀
      slack hn hap₁ hap₂ ha₀ hV₁V₂ hanchor_big hrank1 hgV₁ hgV₂ hV₁L hV₂L hV₁le hV₁small hV₁gt
      hlb hub hslack hy hx huy hux)))
  · exact cPosVal_injOn_V2V2 leaves V₁ V₂ idx L anchor g col ap₂ hn hap₂ hL hV₁V₂
      hanchor_big hblk2 hgV₂ hlb hgap hcolinj hx hy hux huy hxy

/-- **Leaf positions are injective.** -/
lemma cPos_injOn
    (hn : 1000000 ≤ n) (hap₁ : ap₁.val = 70 * n / 100) (hap₂ : ap₂.val = 91 * n / 100)
    (ha₀ : a₀.val = 83 * n / 100) (hL : 1 ≤ L) (hV₁V₂ : Disjoint V₁ V₂)
    (hanchor_big : ∀ x ∈ leaves, anchor x ∈ V₁ ∪ V₂)
    (hkey : Set.InjOn (cKey V₁ V₂ idx L anchor) ↑leaves)
    (hcrank : Set.InjOn (cRank V₁ V₂ idx L) ↑(V₁ ∪ V₂))
    (hrank1 : ∀ u ∈ V₁, idx u / L < V₁.card) (hrank2 : ∀ u ∈ V₂, idx u / L < V₂.card)
    (hblk1 : ∀ u ∈ V₁, ∀ v ∈ V₁, u ≠ v → idx u / L ≠ idx v / L)
    (hblk2 : ∀ u ∈ V₂, ∀ v ∈ V₂, u ≠ v → idx u / L ≠ idx v / L)
    (hdeg : ∀ w ∈ V₁ ∪ V₂, 100 * L ≤ cDeg leaves anchor w)
    (hgV₁ : ∀ v ∈ V₁, (g v).val = ap₁.val + idx v ∧ idx v < V₁.card * L)
    (hgV₂ : ∀ v ∈ V₂, (g v).val = ap₂.val + idx v ∧ idx v < V₂.card * L)
    (hV₁L : V₁.card * L ≤ n / 100) (hV₂L : V₂.card * L ≤ n / 100)
    (hV₁le : ∑ u ∈ V₁, cDeg leaves anchor u ≤ 2 * n / 3)
    (hV₁small : 2 ≤ V₁.card → ∑ u ∈ V₁, cDeg leaves anchor u ≤ n / 10)
    (hV₁gt : n / 20 < ∑ u ∈ V₁, cDeg leaves anchor u)
    (hlb : ∀ z ∈ leaves, cCiv leaves V₁ V₂ idx L anchor z ≤ (col z).val)
    (hgap : ∀ z ∈ leaves, ∀ z' ∈ leaves, cCiv leaves V₁ V₂ idx L anchor z
      ≤ cCiv leaves V₁ V₂ idx L anchor z' →
      (col z).val + (cCiv leaves V₁ V₂ idx L anchor z' - cCiv leaves V₁ V₂ idx L anchor z)
        ≤ (col z').val)
    (hub : ∀ z ∈ leaves, (col z).val ≤ cCiv leaves V₁ V₂ idx L anchor z + slack)
    (hslack : slack ≤ n / 100)
    (hcolinj : Set.InjOn col ↑leaves) :
    Set.InjOn (cPos V₁ V₂ idx L g anchor (fun z => (col z).val)) ↑leaves := by
  have hvinj := cPosVal_injOn leaves V₁ V₂ idx L anchor g col ap₁ ap₂ a₀ slack hn hap₁ hap₂ ha₀
    hL hV₁V₂ hanchor_big hkey hcrank hrank1 hrank2 hblk1 hblk2 hdeg hgV₁ hgV₂ hV₁L hV₂L hV₁le
    hV₁small hV₁gt hlb hgap hub hslack hcolinj
  intro x hx y hy hxy
  apply hvinj hx hy
  have hlx := cPosVal_lt leaves V₁ V₂ idx L anchor g col ap₁ ap₂ a₀ slack hn hap₁ hap₂ ha₀
    hV₁V₂ hanchor_big hrank1 hgV₁ hgV₂ hV₁L hV₂L hV₁le hV₁small hV₁gt hlb hub hslack hx
  have hly := cPosVal_lt leaves V₁ V₂ idx L anchor g col ap₁ ap₂ a₀ slack hn hap₁ hap₂ ha₀
    hV₁V₂ hanchor_big hrank1 hgV₁ hgV₂ hV₁L hV₂L hV₁le hV₁small hV₁gt hlb hub hslack hy
  have := congrArg Fin.val hxy
  simpa [cPos, Nat.mod_eq_of_lt hlx, Nat.mod_eq_of_lt hly] using this

/-
Every core vertex is embedded strictly below `0.92n`.
-/
lemma g_core_lt (core : Finset V)
    (hn : 1000000 ≤ n) (hap₁ : ap₁.val = 70 * n / 100) (hap₂ : ap₂.val = 91 * n / 100)
    (ha₀ : a₀.val = 83 * n / 100) (len₀ : ℕ) (hlen₀ : len₀ = 7 * n / 100)
    (hV₁core : V₁ ⊆ core) (hV₂core : V₂ ⊆ core)
    (hgV₁ : ∀ v ∈ V₁, (g v).val = ap₁.val + idx v ∧ idx v < V₁.card * L)
    (hgV₂ : ∀ v ∈ V₂, (g v).val = ap₂.val + idx v ∧ idx v < V₂.card * L)
    (hgI₀ : ∀ v ∈ core, v ∉ V₁ → v ∉ V₂ → a₀.val ≤ (g v).val ∧ (g v).val < a₀.val + len₀)
    (hV₁L : V₁.card * L ≤ n / 100) (hV₂L : V₂.card * L ≤ n / 100)
    {v : V} (hv : v ∈ core) : (g v).val < 92 * n / 100 := by
  by_cases hv₁ : v ∈ V₁ <;> by_cases hv₂ : v ∈ V₂ <;> simp_all +decide only; all_goals grind (instances := 20000) (splits := 500) (gen := 500)

/-
**Leaf positions avoid the core image (value version).**
-/
lemma cPosVal_off_core (core : Finset V)
    (hn : 1000000 ≤ n) (hap₁ : ap₁.val = 70 * n / 100) (hap₂ : ap₂.val = 91 * n / 100)
    (ha₀ : a₀.val = 83 * n / 100) (len₀ : ℕ) (hlen₀ : len₀ = 7 * n / 100)
    (hV₁V₂ : Disjoint V₁ V₂) (hV₁core : V₁ ⊆ core) (hV₂core : V₂ ⊆ core)
    (hanchor_big : ∀ x ∈ leaves, anchor x ∈ V₁ ∪ V₂)
    (hcrank : Set.InjOn (cRank V₁ V₂ idx L) ↑(V₁ ∪ V₂))
    (hrank1 : ∀ u ∈ V₁, idx u / L < V₁.card)
    (hblk1 : ∀ u ∈ V₁, ∀ v ∈ V₁, u ≠ v → idx u / L ≠ idx v / L)
    (hdeg : ∀ w ∈ V₁ ∪ V₂, 100 * L ≤ cDeg leaves anchor w)
    (hgV₁ : ∀ v ∈ V₁, (g v).val = ap₁.val + idx v ∧ idx v < V₁.card * L)
    (hgV₂ : ∀ v ∈ V₂, (g v).val = ap₂.val + idx v ∧ idx v < V₂.card * L)
    (hgI₀ : ∀ v ∈ core, v ∉ V₁ → v ∉ V₂ → a₀.val ≤ (g v).val ∧ (g v).val < a₀.val + len₀)
    (hV₁L : V₁.card * L ≤ n / 100) (hV₂L : V₂.card * L ≤ n / 100)
    (hV₁le : ∑ u ∈ V₁, cDeg leaves anchor u ≤ 2 * n / 3)
    (hV₁small : 2 ≤ V₁.card → ∑ u ∈ V₁, cDeg leaves anchor u ≤ n / 10)
    (hV₁gt : n / 20 < ∑ u ∈ V₁, cDeg leaves anchor u)
    (hlb : ∀ z ∈ leaves, cCiv leaves V₁ V₂ idx L anchor z ≤ (col z).val)
    (hub : ∀ z ∈ leaves, (col z).val ≤ cCiv leaves V₁ V₂ idx L anchor z + slack)
    (hslack : slack ≤ n / 100)
    {x : V} (hx : x ∈ leaves) {v : V} (hv : v ∈ core) :
    cPosVal V₁ V₂ idx L g anchor (fun z => (col z).val) x ≠ (g v).val := by
  by_cases hux : anchor x ∈ V₁;
  · by_cases h1x : idx (anchor x) / L < (V₁.card + 1) / 2;
    · by_cases hv₁ : v ∈ V₁;
      · apply cPosVal_type1_ne_V1 leaves V₁ V₂ idx L anchor g col ap₁ slack hn hap₁ hanchor_big hcrank hrank1 hblk1 hdeg hgV₁ hV₁L hV₁le hlb hub hslack hx hux h1x hv₁;
      · by_cases hv₂ : v ∈ V₂ <;> simp_all +decide only [cPosVal];
        · grind (instances := 20000) (splits := 500) (gen := 500);
        · grind (instances := 20000) (splits := 500) (gen := 500) +locals;
    · have := cPosVal_type2 leaves V₁ V₂ idx L anchor g col ap₁ a₀ slack hn hap₁ ha₀ hrank1 hgV₁ hV₁L hV₁small hub hslack hx hux h1x;
      by_cases hv₁ : v ∈ V₁;
      · have := cPosVal_type2_gt_V1 leaves V₁ V₂ idx L anchor g col ap₁ slack hn hap₁ hanchor_big hcrank hrank1 hblk1 hdeg hgV₁ hV₁L hV₁small hlb hub hslack hx hux h1x ( hw := hv₁ ) ; omega;
      · by_cases hv₂ : v ∈ V₂ <;> simp_all +decide only [cPosVal]; all_goals grind (instances := 20000) (splits := 500) (gen := 500);
  · have := cPosVal_type3 leaves V₁ V₂ idx L anchor g col ap₂ hn hap₂ hV₁V₂ hanchor_big hrank1 hgV₂ hV₂L hV₁gt hlb hx ( by specialize hanchor_big x hx; aesop );
    grind (instances := 20000) (splits := 500) (gen := 500) +splitImp

/-- **Leaf positions avoid the core image.** -/
lemma cPos_off_core (core : Finset V)
    (hn : 1000000 ≤ n) (hap₁ : ap₁.val = 70 * n / 100) (hap₂ : ap₂.val = 91 * n / 100)
    (ha₀ : a₀.val = 83 * n / 100) (len₀ : ℕ) (hlen₀ : len₀ = 7 * n / 100)
    (hV₁V₂ : Disjoint V₁ V₂) (hV₁core : V₁ ⊆ core) (hV₂core : V₂ ⊆ core)
    (hanchor_big : ∀ x ∈ leaves, anchor x ∈ V₁ ∪ V₂)
    (hcrank : Set.InjOn (cRank V₁ V₂ idx L) ↑(V₁ ∪ V₂))
    (hrank1 : ∀ u ∈ V₁, idx u / L < V₁.card)
    (hblk1 : ∀ u ∈ V₁, ∀ v ∈ V₁, u ≠ v → idx u / L ≠ idx v / L)
    (hdeg : ∀ w ∈ V₁ ∪ V₂, 100 * L ≤ cDeg leaves anchor w)
    (hgV₁ : ∀ v ∈ V₁, (g v).val = ap₁.val + idx v ∧ idx v < V₁.card * L)
    (hgV₂ : ∀ v ∈ V₂, (g v).val = ap₂.val + idx v ∧ idx v < V₂.card * L)
    (hgI₀ : ∀ v ∈ core, v ∉ V₁ → v ∉ V₂ → a₀.val ≤ (g v).val ∧ (g v).val < a₀.val + len₀)
    (hV₁L : V₁.card * L ≤ n / 100) (hV₂L : V₂.card * L ≤ n / 100)
    (hV₁le : ∑ u ∈ V₁, cDeg leaves anchor u ≤ 2 * n / 3)
    (hV₁small : 2 ≤ V₁.card → ∑ u ∈ V₁, cDeg leaves anchor u ≤ n / 10)
    (hV₁gt : n / 20 < ∑ u ∈ V₁, cDeg leaves anchor u)
    (hlb : ∀ z ∈ leaves, cCiv leaves V₁ V₂ idx L anchor z ≤ (col z).val)
    (hub : ∀ z ∈ leaves, (col z).val ≤ cCiv leaves V₁ V₂ idx L anchor z + slack)
    (hslack : slack ≤ n / 100)
    {x : V} (hx : x ∈ leaves) {v : V} (hv : v ∈ core) :
    cPos V₁ V₂ idx L g anchor (fun z => (col z).val) x ≠ g v := by
  have hlt := cPosVal_lt leaves V₁ V₂ idx L anchor g col ap₁ ap₂ a₀ slack hn hap₁ hap₂ ha₀
    hV₁V₂ hanchor_big hrank1 hgV₁ hgV₂ hV₁L hV₂L hV₁le hV₁small hV₁gt hlb hub hslack hx
  have hne := cPosVal_off_core leaves V₁ V₂ idx L anchor g col ap₁ ap₂ a₀ slack core hn hap₁ hap₂
    ha₀ len₀ hlen₀ hV₁V₂ hV₁core hV₂core hanchor_big hcrank hrank1 hblk1 hdeg hgV₁ hgV₂ hgI₀
    hV₁L hV₂L hV₁le hV₁small hV₁gt hlb hub hslack hx hv
  intro heq
  apply hne
  have := congrArg Fin.val heq
  simpa [cPos, Nat.mod_eq_of_lt hlt] using this

end Geometry

end Ringel