/-
Copyright (c) 2026 Walid Elkersh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Walid Elkersh
-/
import Ringel.Primitives
import Ringel.NDInterval
import Ringel.CaseCOneVertex

/-!
# Case C: embedding a small tree into prescribed intervals (`Lemma_small_tree`, MPS §7)

This file formalizes `Lemma_small_tree` of arXiv:2001.02665: a small forest `T` whose vertex
set is partitioned as `V₀ ∪ V₁ ∪ V₂` embeds rainbow into the ND-coloured `K_{2n+1}` with
* the image of `V₀` inside a prescribed cyclic interval `I₀`, and
* the image of each side `Vₚ` (`p ∈ {1,2}`) hitting each of `|Vₚ|` consecutive length-`L`
  blocks of a prescribed cyclic interval exactly once.

The embedding is greedy: vertices are added one at a time (formally: a low-degree vertex of
the induced forest is peeled and strong induction applies to the rest), a `V₀`-vertex is
placed in `I₀` on a fresh **odd** colour, and a side-`p` vertex is placed in a *free* block
on a fresh colour from the side-`p` colour class `C_p^s` with `s` minimal available.  The
colour classes partition the even colour values by their residue mod `2k+1`: side `1` gets
residues `1..k`, side `2` gets residues `k+1..2k`.

The heart of the proof is a potential/doubling invariant replacing the paper's Claim
(which is stated per-history; here it is state-only and exactly preserved):

  for `1 ≤ s < k`, if some colour of class `s+1` is used, then
  `Q · (free + used (s+1)) ≤ 2 · used s + 2`,

where `free` is the number of free blocks on the side, `used s` the number of used class-`s`
colours, and `Q = L/(2(2k+1)) - 6` the per-block counting constant from
`card_class_nbrs_in_cyclicInterval'`.  If no class were *available*
(`2·used s + 2 ≤ Q·free`), the invariant forces `used s ≥ 2·used (s+1)` down the chain and
hence `used 1 ≥ 2^(k-1) > |Vₚ|`, a contradiction; so the greedy never gets stuck.
-/

open SimpleGraph

namespace Ringel

/-! ### Partition classes, side blocks and side colour classes -/

/-- The part of the vertex partition tagged `o`: `none` is the `V₀` part, `some p` the side
`p` part. -/
def partClass {V : Type*} [Fintype V] (part : V → Option (Fin 2)) (o : Option (Fin 2)) :
    Finset V :=
  Finset.univ.filter (fun v => part v = o)

lemma mem_partClass {V : Type*} [Fintype V] {part : V → Option (Fin 2)}
    {o : Option (Fin 2)} {v : V} : v ∈ partClass part o ↔ part v = o := by
  simp [partClass]

/-- The `j`-th length-`L` block of the side interval based at `a`. -/
def sideBlock (n : ℕ) (a : Fin (2 * n + 1)) (L j : ℕ) : Finset (Fin (2 * n + 1)) :=
  cyclicInterval n (cyclicShift n a (j * L)) L

lemma sideBlock_eq (n : ℕ) (a : Fin (2 * n + 1)) (L j : ℕ) :
    sideBlock n a L j = cyclicInterval n (cyclicShift n a (j * L)) L := rfl

/-- Colour class `s ∈ [1..k]` of side `p`: even colour values `≡ s + p·k (mod 2k+1)`. -/
def sideClass (n k : ℕ) (p : Fin 2) (s : ℕ) : Finset (Fin n) :=
  colourClass n k (s + p.val * k)

lemma sideClass_eq (n k : ℕ) (p : Fin 2) (s : ℕ) :
    sideClass n k p s = colourClass n k (s + p.val * k) := rfl

/-- All the colour classes of side `p`. -/
def sideClasses (n k : ℕ) (p : Fin 2) : Finset (Fin n) :=
  (Finset.Icc 1 k).biUnion (fun s => sideClass n k p s)

lemma sideClass_residue_lt (k : ℕ) (p : Fin 2) {s : ℕ} (h2 : s ≤ k) :
    s + p.val * k < 2 * k + 1 := by
  have hp : p.val = 0 ∨ p.val = 1 := by omega
  rcases hp with hp | hp <;> rw [hp] <;> omega

lemma sideClass_subset_sideClasses (n k : ℕ) (p : Fin 2) {s : ℕ} (h1 : 1 ≤ s) (h2 : s ≤ k) :
    sideClass n k p s ⊆ sideClasses n k p :=
  Finset.subset_biUnion_of_mem _ (Finset.mem_Icc.mpr ⟨h1, h2⟩)

lemma sideClass_disjoint_of_ne (n k : ℕ) {p q : Fin 2} {s s' : ℕ}
    (h : s + p.val * k ≠ s' + q.val * k) :
    Disjoint (sideClass n k p s) (sideClass n k q s') := by
  rw [sideClass_eq, sideClass_eq]
  exact colourClass_disjoint n k h

/-- Distinct sides have disjoint colour-class unions (their residues mod `2k+1` are the
disjoint ranges `[1, k]` and `[k+1, 2k]`). -/
lemma sideClasses_disjoint_of_ne (n k : ℕ) {p q : Fin 2} (hpq : p ≠ q) :
    Disjoint (sideClasses n k p) (sideClasses n k q) := by
  rw [sideClasses, sideClasses, Finset.disjoint_biUnion_left]
  intro s hs
  rw [Finset.disjoint_biUnion_right]
  intro s' hs'
  rw [Finset.mem_Icc] at hs hs'
  refine sideClass_disjoint_of_ne n k ?_
  have h1 : p.val = 0 ∨ p.val = 1 := by omega
  have h2 : q.val = 0 ∨ q.val = 1 := by omega
  have h3 : p.val ≠ q.val := fun h => hpq (Fin.ext h)
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] <;> omega

/-- Odd colours are disjoint from every side colour class. -/
lemma oddColourClass_disjoint_sideClasses (n k : ℕ) (p : Fin 2) :
    Disjoint (oddColourClass n) (sideClasses n k p) := by
  rw [sideClasses, Finset.disjoint_biUnion_right]
  intro s _
  rw [sideClass_eq]
  exact oddColourClass_disjoint_colourClass n k _

/-- Each side block sits inside the full side interval. -/
lemma sideBlock_subset (n : ℕ) (a : Fin (2 * n + 1)) (L N : ℕ) {j : ℕ} (hj : j < N) :
    sideBlock n a L j ⊆ cyclicInterval n a (N * L) := by
  rw [sideBlock_eq]
  refine cyclicInterval_shift_subset n a ?_
  have h := Nat.mul_le_mul_right L (show j + 1 ≤ N by omega)
  rw [add_mul, one_mul] at h
  omega

/-- Distinct side blocks are disjoint. -/
lemma sideBlock_disjoint (n : ℕ) (a : Fin (2 * n + 1)) (L N : ℕ)
    (hNL : N * L ≤ 2 * n + 1) {i j : ℕ} (hi : i < N) (hj : j < N) (hij : i ≠ j) :
    Disjoint (sideBlock n a L i) (sideBlock n a L j) := by
  rw [sideBlock_eq, sideBlock_eq]
  rcases Nat.lt_or_ge i j with h | h
  · refine cyclicInterval_shift_disjoint n a ?_ ?_
    · have h' := Nat.mul_le_mul_right L (show i + 1 ≤ j by omega)
      rw [add_mul, one_mul] at h'
      omega
    · have h' := Nat.mul_le_mul_right L (show j + 1 ≤ N by omega)
      rw [add_mul, one_mul] at h'
      omega
  · refine (cyclicInterval_shift_disjoint n a ?_ ?_).symm
    · have h' := Nat.mul_le_mul_right L (show j + 1 ≤ i by omega)
      rw [add_mul, one_mul] at h'
      omega
    · have h' := Nat.mul_le_mul_right L (show i + 1 ≤ N by omega)
      rw [add_mul, one_mul] at h'
      omega

/-- Per-block colour-class counting: any vertex `v` has at least `L/(2(2k+1)) - 6`
class-`(p, s)` neighbours in any side block. -/
lemma sideBlock_class_count (n : ℕ) (hn : 0 < n) (k L : ℕ) (a : Fin (2 * n + 1))
    (hL : L ≤ 2 * n + 1) (p : Fin 2) {s : ℕ} (hsk : s ≤ k)
    (j : ℕ) (v : Fin (2 * n + 1)) :
    L / (2 * (2 * k + 1)) ≤
      ((sideBlock n a L j).filter
        (fun u => ndColouring n hn s(v, u) ∈ sideClass n k p s)).card + 6 := by
  rw [sideBlock_eq]
  simp only [sideClass_eq]
  exact card_class_nbrs_in_cyclicInterval' n hn k (s + p.val * k)
    (sideClass_residue_lt k p hsk) (cyclicShift n a (j * L)) L hL v

/-! ### State of the greedy embedding -/

/-- The colours appearing on the embedded edges of `T[S]`. -/
def usedColours (n : ℕ) (hn : 0 < n) {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (S : Finset V) (g : V → Fin (2 * n + 1)) :
    Finset (Fin n) :=
  ((T.edgeFinset ∩ S.sym2).image (Sym2.map g)).image (ndColouring n hn)

/-- The side blocks (among `0..N-1`) already containing an image of `S`. -/
def occupiedBlocks (n : ℕ) {V : Type*} (S : Finset V) (g : V → Fin (2 * n + 1))
    (a : Fin (2 * n + 1)) (L N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun j => (S.filter (fun v => g v ∈ sideBlock n a L j)).Nonempty)

lemma occupiedBlocks_empty (n : ℕ) {V : Type*} (g : V → Fin (2 * n + 1))
    (a : Fin (2 * n + 1)) (L N : ℕ) :
    occupiedBlocks n (∅ : Finset V) g a L N = ∅ := by
  simp [occupiedBlocks]

/-- Updating the embedding at a new vertex adds to the occupied blocks exactly the blocks
containing the new position. -/
lemma occupiedBlocks_insert (n : ℕ) {V : Type*} [DecidableEq V] (S' : Finset V) (w : V)
    (hw : w ∉ S') (g' : V → Fin (2 * n + 1)) (pos : Fin (2 * n + 1))
    (a : Fin (2 * n + 1)) (L N : ℕ) :
    occupiedBlocks n (insert w S') (Function.update g' w pos) a L N
      = occupiedBlocks n S' g' a L N
        ∪ (Finset.range N).filter (fun j => pos ∈ sideBlock n a L j) := by
  ext j
  simp only [occupiedBlocks, Finset.mem_filter, Finset.mem_union, Finset.mem_range]
  constructor
  · rintro ⟨hjN, v, hv⟩
    rw [Finset.mem_filter, Finset.mem_insert] at hv
    obtain ⟨rfl | hvS', hvblock⟩ := hv
    · right
      rw [Function.update_self] at hvblock
      exact ⟨hjN, hvblock⟩
    · left
      refine ⟨hjN, ⟨v, Finset.mem_filter.mpr ⟨hvS', ?_⟩⟩⟩
      rwa [Function.update_of_ne (ne_of_mem_of_not_mem hvS' hw)] at hvblock
  · rintro (⟨hjN, v, hv⟩ | ⟨hjN, hpos⟩)
    · rw [Finset.mem_filter] at hv
      refine ⟨hjN, ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem hv.1, ?_⟩⟩⟩
      rw [Function.update_of_ne (ne_of_mem_of_not_mem hv.1 hw)]
      exact hv.2
    · exact ⟨hjN, ⟨w, Finset.mem_filter.mpr
        ⟨Finset.mem_insert_self w S', by rwa [Function.update_self]⟩⟩⟩

/-! ### The availability chain -/

/-- **No side ever runs out of colour classes.** Abstract arithmetic core of the paper's
Claim inside `Lemma_small_tree`, via the corrected doubling invariant: if class `s+1` has
been used then `Q(F + used (s+1)) ≤ 2·used s + 2`.  If no class `s ∈ [1,k]` were available
(`2·used s + 2 ≤ Q·F` fails for all `s`), the invariant forces `used 1 ≥ 2^(k-1)`. -/
lemma exists_available_class (k Q F : ℕ) (used : ℕ → ℕ) (hk : 1 ≤ k) (hQ4 : 4 ≤ Q)
    (hF : 1 ≤ F)
    (hchain : ∀ s, 1 ≤ s → s < k → 0 < used (s + 1) →
      Q * (F + used (s + 1)) ≤ 2 * used s + 2)
    (hbound : used 1 < 2 ^ (k - 1)) :
    ∃ s, 1 ≤ s ∧ s ≤ k ∧ 2 * used s + 2 ≤ Q * F := by
  by_contra h
  push Not at h
  have hQF : Q ≤ Q * F := by simpa using Nat.mul_le_mul_left Q hF
  have hstep : ∀ d, d ≤ k - 1 → 2 ^ d ≤ used (k - d) := by
    intro d
    induction d with
    | zero =>
      intro _
      have hk' := h k hk le_rfl
      simp only [pow_zero, Nat.sub_zero]
      omega
    | succ d ihd =>
      intro hdk
      have h2d := ihd (by omega)
      have hs1 : 1 ≤ k - d - 1 := by omega
      have hsucc : k - d - 1 + 1 = k - d := by omega
      have h1d : 1 ≤ 2 ^ d := Nat.one_le_two_pow
      have hpos : 0 < used (k - d - 1 + 1) := by
        rw [hsucc]
        omega
      have hc := hchain (k - d - 1) hs1 (by omega) hpos
      rw [hsucc] at hc
      have hmul : 4 * (1 + used (k - d)) ≤ Q * (F + used (k - d)) :=
        Nat.mul_le_mul hQ4 (by omega)
      have hp2 : 2 ^ (d + 1) = 2 ^ d * 2 := pow_succ 2 d
      have hkd : k - (d + 1) = k - d - 1 := by omega
      rw [hkd, hp2]
      omega
  have hfin := hstep (k - 1) le_rfl
  have hone : k - (k - 1) = 1 := by omega
  rw [hone] at hfin
  omega

/-! ### Peeling a low-degree vertex -/

/-- Every nonempty vertex set of a forest contains a vertex with at most one neighbour
among the others. -/
lemma exists_low_degree_mem {V : Type*} [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hac : T.IsAcyclic)
    {S : Finset V} (hS : S.Nonempty) :
    ∃ w ∈ S, ((S.erase w).filter (fun u => T.Adj w u)).card ≤ 1 := by
  classical
  obtain ⟨x, hx⟩ := hS
  rcases Nat.lt_or_ge S.card 2 with h1 | h2
  · refine ⟨x, hx, ?_⟩
    have hS1 : S = {x} := by
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hx, fun y hy => ?_⟩
      by_contra hne
      have : 1 < S.card := Finset.one_lt_card.mpr ⟨y, hy, x, hx, hne⟩
      omega
    rw [hS1]
    simp
  · haveI : DecidableRel (T.induce (S : Set V)).Adj :=
      fun u v => inferInstanceAs (Decidable (T.Adj ↑u ↑v))
    have hcardS : Fintype.card (S : Set V) = S.card := by
      rw [Fintype.card_congr (Equiv.subtypeEquivRight (fun y => Finset.mem_coe))]
      exact Fintype.card_coe S
    obtain ⟨w0, _, hw0deg⟩ := exists_degree_le_one_ne (T.induce (S : Set V))
      (hac.induce _) ⟨x, Finset.mem_coe.mpr hx⟩ (by omega)
    refine ⟨(w0 : V), Finset.mem_coe.mp w0.2, ?_⟩
    have himg : ((T.induce (S : Set V)).neighborFinset w0).image Subtype.val
        = (S.erase (w0 : V)).filter (fun u => T.Adj (w0 : V) u) := by
      ext u
      simp only [Finset.mem_image, SimpleGraph.mem_neighborFinset, Finset.mem_filter,
        Finset.mem_erase]
      constructor
      · rintro ⟨w', hw', rfl⟩
        exact ⟨⟨fun h => hw'.ne' (Subtype.ext h), Finset.mem_coe.mp w'.2⟩, hw'⟩
      · rintro ⟨⟨_, huS⟩, hadj⟩
        exact ⟨⟨u, Finset.mem_coe.mpr huS⟩, hadj, rfl⟩
    calc ((S.erase (w0 : V)).filter (fun u => T.Adj (w0 : V) u)).card
        = (((T.induce (S : Set V)).neighborFinset w0).image Subtype.val).card := by
          rw [himg]
      _ ≤ ((T.induce (S : Set V)).neighborFinset w0).card := Finset.card_image_le
      _ ≤ 1 := by rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hw0deg

/-! ### The invariant of the greedy embedding -/

/-- The full state invariant of the interval-controlled greedy embedding of
`Lemma_small_tree`.  `S` is the set of embedded vertices, `g` the embedding. -/
structure STInv (n : ℕ) (hn : 0 < n) {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (part : V → Option (Fin 2)) (k L : ℕ)
    (a₀ : Fin (2 * n + 1)) (len₀ : ℕ) (ap : Fin 2 → Fin (2 * n + 1))
    (S : Finset V) (g : V → Fin (2 * n + 1)) : Prop where
  inj : Set.InjOn g ↑S
  rainbow : Set.InjOn (ndColouring n hn) ↑((T.edgeFinset ∩ S.sym2).image (Sym2.map g))
  mem₀ : ∀ v ∈ S, part v = none → g v ∈ cyclicInterval n a₀ len₀
  memP : ∀ p : Fin 2, ∀ v ∈ S, part v = some p →
    ∃ j < (partClass part (some p)).card, g v ∈ sideBlock n (ap p) L j
  occEq : ∀ p : Fin 2,
    (occupiedBlocks n S g (ap p) L (partClass part (some p)).card).card
      = (S.filter (fun v => part v = some p)).card
  usedSide : ∀ p : Fin 2, (usedColours n hn T S g ∩ sideClasses n k p).card
    ≤ (S.filter (fun v => part v = some p)).card
  usedOdd : (usedColours n hn T S g ∩ oddColourClass n).card
    ≤ (S.filter (fun v => part v = none)).card
  doubling : ∀ p : Fin 2, ∀ s, 1 ≤ s → s < k →
    0 < (usedColours n hn T S g ∩ sideClass n k p (s + 1)).card →
    (L / (2 * (2 * k + 1)) - 6) * ((partClass part (some p)).card
        - (occupiedBlocks n S g (ap p) L (partClass part (some p)).card).card
        + (usedColours n hn T S g ∩ sideClass n k p (s + 1)).card)
      ≤ 2 * (usedColours n hn T S g ∩ sideClass n k p s).card + 2

/-! ### Small card bookkeeping -/

lemma card_inter_insert_le {α : Type*} [DecidableEq α] (c : α) (X Y : Finset α) :
    ((insert c X) ∩ Y).card ≤ (X ∩ Y).card + 1 := by
  have hsub : (insert c X) ∩ Y ⊆ insert c (X ∩ Y) := by
    intro a ha
    rw [Finset.mem_inter, Finset.mem_insert] at ha
    rcases ha with ⟨rfl | haX, haY⟩
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_inter.mpr ⟨haX, haY⟩)
  exact le_trans (Finset.card_le_card hsub) (Finset.card_insert_le _ _)

lemma card_inter_insert_of_mem_of_notMem {α : Type*} [DecidableEq α] {c : α} {X Y : Finset α}
    (hcY : c ∈ Y) (hcX : c ∉ X) : ((insert c X) ∩ Y).card = (X ∩ Y).card + 1 := by
  rw [Finset.insert_inter_of_mem hcY,
    Finset.card_insert_of_notMem (fun h => hcX (Finset.mem_of_mem_inter_left h))]

/-! ### The greedy embedding -/

/-- **The interval-controlled greedy embedding** (`Lemma_small_tree`, MPS §7, inductive
core).  Under the size, counting and disjointness hypotheses, every vertex subset `S` of
the forest `T` admits an embedding satisfying the full invariant `STInv`. -/
lemma small_tree_greedy (n : ℕ) (hn : 0 < n) {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hac : T.IsAcyclic)
    (part : V → Option (Fin 2)) (k L : ℕ) (hk : 1 ≤ k)
    (a₀ : Fin (2 * n + 1)) (len₀ : ℕ) (ap : Fin 2 → Fin (2 * n + 1))
    (hlen₀n : len₀ ≤ 2 * n + 1)
    (hlen₀ : 6 * (partClass part none).card + 12 ≤ len₀)
    (hQ : 10 ≤ L / (2 * (2 * k + 1)))
    (hJn : ∀ p : Fin 2, (partClass part (some p)).card * L ≤ 2 * n + 1)
    (hpow : ∀ p : Fin 2, (partClass part (some p)).card < 2 ^ (k - 1))
    (hd0 : ∀ p : Fin 2, Disjoint (cyclicInterval n a₀ len₀)
      (cyclicInterval n (ap p) ((partClass part (some p)).card * L)))
    (hd12 : ∀ p q : Fin 2, p ≠ q → Disjoint
      (cyclicInterval n (ap p) ((partClass part (some p)).card * L))
      (cyclicInterval n (ap q) ((partClass part (some q)).card * L))) :
    ∀ S : Finset V, ∃ g : V → Fin (2 * n + 1), STInv n hn T part k L a₀ len₀ ap S g := by
  classical
  intro S
  induction S using Finset.strongInduction with
  | _ S ih =>
    rcases Finset.eq_empty_or_nonempty S with rfl | hSne
    · -- Base case: the empty embedding.
      refine ⟨fun _ => a₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp
      · simp
      · simp
      · simp
      · intro p
        simp [occupiedBlocks_empty]
      · intro p
        simp [usedColours]
      · simp [usedColours]
      · intro p s _ _ hpos
        simp [usedColours] at hpos
    · -- Peel a low-degree vertex `w` of the induced forest.
      obtain ⟨w, hwS, hwdeg⟩ := exists_low_degree_mem T hac hSne
      obtain ⟨g', hinv'⟩ := ih (S.erase w) (Finset.erase_ssubset hwS)
      obtain ⟨hinj', hrb', hmem0', hmemP', hocc', huseS', huseO', hdbl'⟩ := hinv'
      set S' := S.erase w with hS'def
      have hwS' : w ∉ S' := Finset.notMem_erase w S
      have hSins : S = insert w S' := (Finset.insert_erase hwS).symm
      set Nb := S'.filter (fun u => T.Adj w u) with hNbdef
      have hNbcard : Nb.card ≤ 1 := hwdeg
      -- The number-theoretic constant of the counting lemma.
      have hQ4 : 4 ≤ L / (2 * (2 * k + 1)) - 6 := by omega
      have hL1 : 1 ≤ L := le_trans (by omega) (Nat.div_le_self L (2 * (2 * k + 1)))
      -- Off-`w` updates preserve the mapped edges of `S'`.
      have hmapeq : ∀ pos : Fin (2 * n + 1), ∀ e ∈ T.edgeFinset ∩ S'.sym2,
          Sym2.map (Function.update g' w pos) e = Sym2.map g' e := by
        intro pos e he
        rw [Finset.mem_inter] at he
        induction e using Sym2.ind with
        | _ x y =>
          have hxy := he.2
          rw [Finset.mk_mem_sym2_iff] at hxy
          have hxne : x ≠ w := (Finset.mem_erase.mp hxy.1).1
          have hyne : y ≠ w := (Finset.mem_erase.mp hxy.2).1
          simp only [Sym2.map_mk, Prod.map_apply, Function.update_of_ne hxne,
            Function.update_of_ne hyne]
      -- Which vertices can sit in a side block.
      have himg_side : ∀ (p : Fin 2) (j : ℕ), j < (partClass part (some p)).card →
          ∀ v ∈ S', g' v ∈ sideBlock n (ap p) L j → part v = some p := by
        intro p j hj v hv hblock
        have hblocksub := sideBlock_subset n (ap p) L (partClass part (some p)).card hj
        rcases hpv : part v with _ | q
        · exact absurd (hblocksub hblock)
            (Finset.disjoint_left.mp (hd0 p) (hmem0' v hv hpv))
        · rcases eq_or_ne q p with heq | hqp
          · rw [heq]
          · exfalso
            obtain ⟨j', hj', hbq⟩ := hmemP' q v hv hpv
            exact Finset.disjoint_left.mp (hd12 q p hqp)
              (sideBlock_subset n (ap q) L (partClass part (some q)).card hj' hbq)
              (hblocksub hblock)
      -- Fresh positions preserve injectivity.
      have hInjOnOf : ∀ pos : Fin (2 * n + 1), (∀ v ∈ S', g' v ≠ pos) →
          Set.InjOn (Function.update g' w pos) ↑S := by
        intro pos hpos x hx y hy hxy
        by_cases hxw : x = w
        · by_cases hyw : y = w
          · rw [hxw, hyw]
          · rw [hxw, Function.update_self, Function.update_of_ne hyw] at hxy
            exact absurd hxy.symm
              (hpos y (Finset.mem_erase.mpr ⟨hyw, Finset.mem_coe.mp hy⟩))
        · by_cases hyw : y = w
          · rw [hyw, Function.update_of_ne hxw, Function.update_self] at hxy
            exact absurd hxy
              (hpos x (Finset.mem_erase.mpr ⟨hxw, Finset.mem_coe.mp hx⟩))
          · rw [Function.update_of_ne hxw, Function.update_of_ne hyw] at hxy
            exact hinj'
              (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hxw, Finset.mem_coe.mp hx⟩))
              (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hyw, Finset.mem_coe.mp hy⟩)) hxy
      -- Part-count bookkeeping across the insertion.
      have hfiltins : ∀ o : Option (Fin 2), (S.filter (fun v => part v = o)).card
          = (S'.filter (fun v => part v = o)).card + (if part w = o then 1 else 0) := by
        intro o
        rw [hSins, Finset.filter_insert]
        by_cases hwo : part w = o
        · rw [if_pos hwo, if_pos hwo, Finset.card_insert_of_notMem
            (fun h => hwS' (Finset.mem_of_mem_filter w h))]
        · rw [if_neg hwo, if_neg hwo, Nat.add_zero]
      rcases Finset.eq_empty_or_nonempty Nb with hNbe | hNbne
      · -- No new edge: the placed edge set and used colours are unchanged.
        have hseteq : T.edgeFinset ∩ S.sym2 = T.edgeFinset ∩ S'.sym2 := by
          ext e
          induction e using Sym2.ind with
          | _ x y =>
            simp only [Finset.mem_inter, SimpleGraph.mem_edgeFinset, Finset.mk_mem_sym2_iff,
              SimpleGraph.mem_edgeSet]
            constructor
            · rintro ⟨hadj, hxS, hyS⟩
              refine ⟨hadj, Finset.mem_erase.mpr ⟨?_, hxS⟩, Finset.mem_erase.mpr ⟨?_, hyS⟩⟩
              · rintro rfl
                have hyNb : y ∈ Nb := Finset.mem_filter.mpr
                  ⟨Finset.mem_erase.mpr ⟨hadj.ne', hyS⟩, hadj⟩
                simp [hNbe] at hyNb
              · rintro rfl
                have hxNb : x ∈ Nb := Finset.mem_filter.mpr
                  ⟨Finset.mem_erase.mpr ⟨hadj.ne, hxS⟩, hadj.symm⟩
                simp [hNbe] at hxNb
            · rintro ⟨hadj, hxS', hyS'⟩
              exact ⟨hadj, Finset.mem_of_mem_erase hxS', Finset.mem_of_mem_erase hyS'⟩
        have husedeq : ∀ pos : Fin (2 * n + 1),
            usedColours n hn T S (Function.update g' w pos) = usedColours n hn T S' g' := by
          intro pos
          rw [usedColours, usedColours, hseteq, Finset.image_congr (fun e he => hmapeq pos e he)]
        have hrbeq : ∀ pos : Fin (2 * n + 1),
            (T.edgeFinset ∩ S.sym2).image (Sym2.map (Function.update g' w pos))
              = (T.edgeFinset ∩ S'.sym2).image (Sym2.map g') := by
          intro pos
          rw [hseteq, Finset.image_congr (fun e he => hmapeq pos e he)]
        rcases hpw : part w with _ | p
        · -- `w ∈ V₀`, no edge: any unoccupied position of `I₀`.
          have hV0sub : S'.filter (fun v => part v = none) ⊆ partClass part none := by
            intro v hv
            exact mem_partClass.mpr (Finset.mem_filter.mp hv).2
          have himgcard : ((S'.filter (fun v => part v = none)).image g').card
              < (cyclicInterval n a₀ len₀).card := by
            rw [card_cyclicInterval n a₀ hlen₀n]
            have h1 : ((S'.filter (fun v => part v = none)).image g').card
                ≤ (S'.filter (fun v => part v = none)).card := Finset.card_image_le
            have h2 := Finset.card_le_card hV0sub
            omega
          obtain ⟨pos, hposI, hposimg⟩ :=
            Finset.exists_mem_notMem_of_card_lt_card himgcard
          have hposne : ∀ v ∈ S', g' v ≠ pos := by
            intro v hv h
            rcases hpv : part v with _ | q
            · exact hposimg (Finset.mem_image.mpr
                ⟨v, Finset.mem_filter.mpr ⟨hv, hpv⟩, h⟩)
            · obtain ⟨j, hj, hbj⟩ := hmemP' q v hv hpv
              exact Finset.disjoint_left.mp (hd0 q) hposI
                (sideBlock_subset n (ap q) L (partClass part (some q)).card hj (h ▸ hbj))
          have hocceq : ∀ q : Fin 2,
              occupiedBlocks n S (Function.update g' w pos) (ap q) L
                (partClass part (some q)).card
              = occupiedBlocks n S' g' (ap q) L (partClass part (some q)).card := by
            intro q
            rw [hSins, occupiedBlocks_insert n S' w hwS' g' pos (ap q) L _]
            have hempt : (Finset.range (partClass part (some q)).card).filter
                (fun j => pos ∈ sideBlock n (ap q) L j) = ∅ := by
              rw [Finset.filter_eq_empty_iff]
              intro j hj hposb
              exact Finset.disjoint_left.mp (hd0 q) hposI
                (sideBlock_subset n (ap q) L _ (Finset.mem_range.mp hj) hposb)
            rw [hempt, Finset.union_empty]
          refine ⟨Function.update g' w pos, hInjOnOf pos hposne, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hrbeq pos]
            exact hrb'
          · intro v hv hpv
            by_cases hvw : v = w
            · subst hvw
              rw [Function.update_self]
              exact hposI
            · rw [Function.update_of_ne hvw]
              exact hmem0' v (Finset.mem_erase.mpr ⟨hvw, hv⟩) hpv
          · intro q v hv hpv
            by_cases hvw : v = w
            · subst hvw
              simp [hpw] at hpv
            · rw [Function.update_of_ne hvw]
              exact hmemP' q v (Finset.mem_erase.mpr ⟨hvw, hv⟩) hpv
          · intro q
            rw [hocceq q, hocc' q, hfiltins (some q), hpw, if_neg (by simp), Nat.add_zero]
          · intro q
            rw [husedeq pos, hfiltins (some q), hpw, if_neg (by simp), Nat.add_zero]
            exact huseS' q
          · rw [husedeq pos, hfiltins none, hpw, if_pos rfl]
            have := huseO'
            omega
          · intro q s hs1 hsk hpos
            rw [husedeq pos] at hpos
            rw [husedeq pos, hocceq q]
            exact hdbl' q s hs1 hsk hpos
        · -- `w` on side `p`, no edge: any position of a free block.
          have hwVp : w ∈ partClass part (some p) := mem_partClass.mpr hpw
          have hNp1 : 1 ≤ (partClass part (some p)).card :=
            Finset.card_pos.mpr ⟨w, hwVp⟩
          have hL2n : L ≤ 2 * n + 1 := by
            have h1 : 1 * L ≤ (partClass part (some p)).card * L :=
              Nat.mul_le_mul_right L hNp1
            rw [one_mul] at h1
            exact le_trans h1 (hJn p)
          have hfilt_lt : (S'.filter (fun v => part v = some p)).card
              < (partClass part (some p)).card := by
            have hsub : S'.filter (fun v => part v = some p)
                ⊆ (partClass part (some p)).erase w := by
              intro v hv
              rw [Finset.mem_filter] at hv
              exact Finset.mem_erase.mpr
                ⟨ne_of_mem_of_not_mem hv.1 hwS', mem_partClass.mpr hv.2⟩
            have h1 := Finset.card_le_card hsub
            have h2 := Finset.card_erase_of_mem hwVp
            omega
          have hocclt : (occupiedBlocks n S' g' (ap p) L (partClass part (some p)).card).card
              < (Finset.range (partClass part (some p)).card).card := by
            rw [Finset.card_range, hocc' p]
            exact hfilt_lt
          obtain ⟨j₀, hj₀range, hj₀notocc⟩ :=
            Finset.exists_mem_notMem_of_card_lt_card hocclt
          have hj₀N := Finset.mem_range.mp hj₀range
          have hblockne : (sideBlock n (ap p) L j₀).Nonempty := by
            rw [← Finset.card_pos, sideBlock_eq, card_cyclicInterval n _ hL2n]
            omega
          obtain ⟨pos, hposb⟩ := hblockne
          have hj₀no : ∀ v ∈ S', g' v ∉ sideBlock n (ap p) L j₀ := by
            intro v hv hmem
            exact hj₀notocc (Finset.mem_filter.mpr
              ⟨hj₀range, ⟨v, Finset.mem_filter.mpr ⟨hv, hmem⟩⟩⟩)
          have hposne : ∀ v ∈ S', g' v ≠ pos := fun v hv h => hj₀no v hv (h ▸ hposb)
          have hposJp : pos ∈ cyclicInterval n (ap p) ((partClass part (some p)).card * L) :=
            sideBlock_subset n (ap p) L _ hj₀N hposb
          have hposblocks : ∀ q : Fin 2, ∀ j < (partClass part (some q)).card,
              pos ∈ sideBlock n (ap q) L j → q = p ∧ j = j₀ := by
            intro q j hj hposj
            by_cases hqp : q = p
            · refine ⟨hqp, ?_⟩
              by_contra hne
              rw [hqp] at hposj hj
              exact Finset.disjoint_left.mp
                (sideBlock_disjoint n (ap p) L _ (hJn p) hj hj₀N hne) hposj hposb
            · exact absurd hposJp (Finset.disjoint_left.mp (hd12 q p hqp)
                (sideBlock_subset n (ap q) L _ hj hposj))
          have hfilterq : ∀ q : Fin 2, (Finset.range (partClass part (some q)).card).filter
              (fun j => pos ∈ sideBlock n (ap q) L j)
              = if q = p then {j₀} else ∅ := by
            intro q
            by_cases hqp : q = p
            · rw [if_pos hqp]
              ext j
              simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
              constructor
              · rintro ⟨hj, hposj⟩
                exact (hposblocks q j hj hposj).2
              · rintro rfl
                rw [hqp]
                exact ⟨hj₀N, hposb⟩
            · rw [if_neg hqp, Finset.filter_eq_empty_iff]
              intro j hj hposj
              exact hqp (hposblocks q j (Finset.mem_range.mp hj) hposj).1
          have hoccq : ∀ q : Fin 2,
              occupiedBlocks n S (Function.update g' w pos) (ap q) L
                (partClass part (some q)).card
              = occupiedBlocks n S' g' (ap q) L (partClass part (some q)).card
                ∪ (if q = p then {j₀} else ∅) := by
            intro q
            rw [hSins, occupiedBlocks_insert n S' w hwS' g' pos (ap q) L _, hfilterq q]
          refine ⟨Function.update g' w pos, hInjOnOf pos hposne, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hrbeq pos]
            exact hrb'
          · intro v hv hpv
            by_cases hvw : v = w
            · subst hvw
              simp [hpw] at hpv
            · rw [Function.update_of_ne hvw]
              exact hmem0' v (Finset.mem_erase.mpr ⟨hvw, hv⟩) hpv
          · intro q v hv hpv
            by_cases hvw : v = w
            · subst hvw
              rw [hpw] at hpv
              have hqp : p = q := Option.some.inj hpv
              rw [Function.update_self]
              refine ⟨j₀, ?_, ?_⟩
              · rw [← hqp]
                exact hj₀N
              · rw [← hqp]
                exact hposb
            · rw [Function.update_of_ne hvw]
              exact hmemP' q v (Finset.mem_erase.mpr ⟨hvw, hv⟩) hpv
          · intro q
            rw [hoccq q, hfiltins (some q), hpw]
            by_cases hqp : q = p
            · have hj₀nocc : j₀ ∉ occupiedBlocks n S' g' (ap q) L
                  (partClass part (some q)).card := by
                rw [hqp]
                exact hj₀notocc
              rw [if_pos hqp, if_pos (show (some p : Option (Fin 2)) = some q by rw [hqp]),
                Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr hj₀nocc),
                Finset.card_singleton, hocc' q]
            · rw [if_neg hqp, if_neg (fun h => hqp (Option.some.inj h).symm),
                Finset.union_empty, hocc' q, Nat.add_zero]
          · intro q
            rw [husedeq pos, hfiltins (some q), hpw]
            have := huseS' q
            by_cases hqp : q = p
            · rw [if_pos (show (some p : Option (Fin 2)) = some q by rw [hqp])]
              omega
            · rw [if_neg (fun h => hqp (Option.some.inj h).symm)]
              omega
          · rw [husedeq pos, hfiltins none, hpw, if_neg (by simp), Nat.add_zero]
            exact huseO'
          · intro q s hs1 hsk hpos
            rw [husedeq pos] at hpos
            rw [husedeq pos, hoccq q]
            by_cases hqp : q = p
            · have hj₀nocc : j₀ ∉ occupiedBlocks n S' g' (ap q) L
                  (partClass part (some q)).card := by
                rw [hqp]
                exact hj₀notocc
              rw [if_pos hqp,
                Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr hj₀nocc),
                Finset.card_singleton]
              refine le_trans (Nat.mul_le_mul_left _ ?_) (hdbl' q s hs1 hsk hpos)
              omega
            · rw [if_neg hqp, Finset.union_empty]
              exact hdbl' q s hs1 hsk hpos
      · -- One new edge, to `v_f ∈ Nb`.
        obtain ⟨vf, hvf⟩ := hNbne
        have hvfS' : vf ∈ S' := Finset.mem_of_mem_filter vf hvf
        have hadjwvf : T.Adj w vf := (Finset.mem_filter.mp hvf).2
        have hseteq : T.edgeFinset ∩ S.sym2
            = insert s(w, vf) (T.edgeFinset ∩ S'.sym2) := by
          ext e
          induction e using Sym2.ind with
          | _ x y =>
            simp only [Finset.mem_inter, SimpleGraph.mem_edgeFinset, Finset.mk_mem_sym2_iff,
              Finset.mem_insert, Sym2.eq_iff, SimpleGraph.mem_edgeSet]
            constructor
            · rintro ⟨hadj, hxS, hyS⟩
              by_cases hxw : x = w
              · subst hxw
                have hyvf : y = vf := by
                  have hy_nb : y ∈ Nb := Finset.mem_filter.mpr
                    ⟨Finset.mem_erase.mpr ⟨hadj.ne', hyS⟩, hadj⟩
                  exact Finset.card_le_one.mp hNbcard y hy_nb vf hvf
                exact Or.inl (Or.inl ⟨rfl, hyvf⟩)
              · by_cases hyw : y = w
                · subst hyw
                  have hxvf : x = vf := by
                    have hx_nb : x ∈ Nb := Finset.mem_filter.mpr
                      ⟨Finset.mem_erase.mpr ⟨hadj.ne, hxS⟩, hadj.symm⟩
                    exact Finset.card_le_one.mp hNbcard x hx_nb vf hvf
                  exact Or.inl (Or.inr ⟨hxvf, rfl⟩)
                · exact Or.inr ⟨hadj, Finset.mem_erase.mpr ⟨hxw, hxS⟩,
                    Finset.mem_erase.mpr ⟨hyw, hyS⟩⟩
            · rintro ((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨hadj, hxS', hyS'⟩)
              · exact ⟨hadjwvf, hwS, Finset.mem_of_mem_erase hvfS'⟩
              · exact ⟨hadjwvf.symm, Finset.mem_of_mem_erase hvfS', hwS⟩
              · exact ⟨hadj, Finset.mem_of_mem_erase hxS', Finset.mem_of_mem_erase hyS'⟩
        have hvfw : vf ≠ w := (Finset.mem_erase.mp hvfS').1
        -- The mapped edge set gains exactly `s(pos, g' vf)`.
        have hedgeins : ∀ pos : Fin (2 * n + 1),
            (T.edgeFinset ∩ S.sym2).image (Sym2.map (Function.update g' w pos))
              = insert s(pos, g' vf) ((T.edgeFinset ∩ S'.sym2).image (Sym2.map g')) := by
          intro pos
          rw [hseteq, Finset.image_insert]
          have hnew : Sym2.map (Function.update g' w pos) s(w, vf) = s(pos, g' vf) := by
            simp only [Sym2.map_mk, Prod.map_apply, Function.update_self,
              Function.update_of_ne hvfw]
          rw [hnew, Finset.image_congr (fun e he => hmapeq pos e he)]
        have husedins : ∀ pos : Fin (2 * n + 1),
            usedColours n hn T S (Function.update g' w pos)
              = insert (ndColouring n hn s(pos, g' vf)) (usedColours n hn T S' g') := by
          intro pos
          rw [usedColours, hedgeins pos, Finset.image_insert, usedColours]
        -- Freshness of the new colour extends the rainbow property.
        have hrbins : ∀ pos : Fin (2 * n + 1),
            ndColouring n hn s(pos, g' vf) ∉ usedColours n hn T S' g' →
            Set.InjOn (ndColouring n hn)
              ↑((T.edgeFinset ∩ S.sym2).image (Sym2.map (Function.update g' w pos))) := by
          intro pos hfresh
          rw [hedgeins pos, Finset.coe_insert]
          refine (Set.injOn_insert ?_).mpr ⟨hrb', ?_⟩
          · intro hmem
            exact hfresh (Finset.mem_image.mpr ⟨_, Finset.mem_coe.mp hmem, rfl⟩)
          · rintro ⟨e, he, hce⟩
            exact hfresh (hce ▸ Finset.mem_image.mpr ⟨e, Finset.mem_coe.mp he, rfl⟩)
        rcases hpw : part w with _ | p
        · -- `w ∈ V₀`, one edge: fresh odd colour into `I₀`.
          set uf := g' vf with hufdef
          set W : Finset (Fin (2 * n + 1)) := (cyclicInterval n a₀ len₀).filter
            (fun u => ndColouring n hn s(uf, u) ∈ oddColourClass n) with hWdef
          set U : Finset (Fin (2 * n + 1)) :=
            insert uf ((S'.filter (fun v => part v = none)).image g') with hUdef
          set C : Finset (Fin n) := usedColours n hn T S' g' ∩ oddColourClass n with hCdef
          have hWcard : len₀ / 2 ≤ W.card + 6 :=
            card_odd_nbrs_in_cyclicInterval' n hn a₀ len₀ hlen₀n uf
          have hV0sub : S'.filter (fun v => part v = none)
              ⊆ (partClass part none).erase w := by
            intro v hv
            rw [Finset.mem_filter] at hv
            exact Finset.mem_erase.mpr
              ⟨ne_of_mem_of_not_mem hv.1 hwS', mem_partClass.mpr hv.2⟩
          have hwV0 : w ∈ partClass part none := mem_partClass.mpr hpw
          have hV0filt : (S'.filter (fun v => part v = none)).card + 1
              ≤ (partClass part none).card := by
            have h1 := Finset.card_le_card hV0sub
            have h2 := Finset.card_erase_of_mem hwV0
            have h3 : 1 ≤ (partClass part none).card := Finset.card_pos.mpr ⟨w, hwV0⟩
            omega
          have hUcard : U.card ≤ (partClass part none).card := by
            calc U.card ≤ ((S'.filter (fun v => part v = none)).image g').card + 1 :=
                  Finset.card_insert_le _ _
              _ ≤ (S'.filter (fun v => part v = none)).card + 1 := by
                  have h := Finset.card_image_le
                    (s := S'.filter (fun v => part v = none)) (f := g')
                  omega
              _ ≤ _ := hV0filt
          have hlt : U.card + 2 * C.card < W.card := by
            have hC1 : C.card ≤ (S'.filter (fun v => part v = none)).card := huseO'
            have hdiv : 3 * (partClass part none).card + 6 ≤ len₀ / 2 := by
              have h := Nat.div_le_div_right (c := 2) hlen₀
              rw [show (6 * (partClass part none).card + 12) / 2
                  = 3 * (partClass part none).card + 6 by omega] at h
              exact h
            omega
          obtain ⟨pos, hposW, hposU, hposC⟩ := exists_fresh_position_in n hn uf W U
            (Finset.mem_insert_self uf _) C hlt
          rw [hWdef, Finset.mem_filter] at hposW
          obtain ⟨hposI, hposodd⟩ := hposW
          have hcol_mem : ndColouring n hn s(pos, uf) ∈ oddColourClass n := by
            rwa [Sym2.eq_swap] at hposodd
          have hfresh : ndColouring n hn s(pos, uf) ∉ usedColours n hn T S' g' := by
            intro hmem
            apply hposC
            rw [hCdef]
            refine Finset.mem_inter.mpr ⟨?_, hposodd⟩
            rwa [Sym2.eq_swap]
          have hposne : ∀ v ∈ S', g' v ≠ pos := by
            intro v hv h
            rcases hpv : part v with _ | q
            · apply hposU
              rw [hUdef]
              exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
                ⟨v, Finset.mem_filter.mpr ⟨hv, hpv⟩, h⟩)
            · obtain ⟨j, hj, hbj⟩ := hmemP' q v hv hpv
              exact Finset.disjoint_left.mp (hd0 q) hposI
                (sideBlock_subset n (ap q) L (partClass part (some q)).card hj (h ▸ hbj))
          have hocceq : ∀ q : Fin 2, occupiedBlocks n S (Function.update g' w pos) (ap q) L
              (partClass part (some q)).card
              = occupiedBlocks n S' g' (ap q) L (partClass part (some q)).card := by
            intro q
            rw [hSins, occupiedBlocks_insert n S' w hwS' g' pos (ap q) L _]
            have hempt : (Finset.range (partClass part (some q)).card).filter
                (fun j => pos ∈ sideBlock n (ap q) L j) = ∅ := by
              rw [Finset.filter_eq_empty_iff]
              intro j hj hposbj
              exact Finset.disjoint_left.mp (hd0 q) hposI
                (sideBlock_subset n (ap q) L _ (Finset.mem_range.mp hj) hposbj)
            rw [hempt, Finset.union_empty]
          have hcol_notside : ∀ q : Fin 2,
              ndColouring n hn s(pos, uf) ∉ sideClasses n k q := fun q =>
            Finset.disjoint_left.mp (oddColourClass_disjoint_sideClasses n k q) hcol_mem
          have hcol_notclass : ∀ (q : Fin 2) (s : ℕ),
              ndColouring n hn s(pos, uf) ∉ sideClass n k q s := by
            intro q s
            rw [sideClass_eq]
            exact Finset.disjoint_left.mp
              (oddColourClass_disjoint_colourClass n k _) hcol_mem
          refine ⟨Function.update g' w pos, hInjOnOf pos hposne, hrbins pos hfresh,
            ?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro v hv hpv
            by_cases hvw : v = w
            · subst hvw
              rw [Function.update_self]
              exact hposI
            · rw [Function.update_of_ne hvw]
              exact hmem0' v (Finset.mem_erase.mpr ⟨hvw, hv⟩) hpv
          · intro q v hv hpv
            by_cases hvw : v = w
            · subst hvw
              simp [hpw] at hpv
            · rw [Function.update_of_ne hvw]
              exact hmemP' q v (Finset.mem_erase.mpr ⟨hvw, hv⟩) hpv
          · intro q
            rw [hocceq q, hocc' q, hfiltins (some q), hpw, if_neg (by simp), Nat.add_zero]
          · intro q
            rw [husedins pos, Finset.insert_inter_of_notMem (hcol_notside q),
              hfiltins (some q), hpw, if_neg (by simp), Nat.add_zero]
            exact huseS' q
          · rw [husedins pos, hfiltins none, hpw, if_pos rfl]
            have h1 := card_inter_insert_le (ndColouring n hn s(pos, uf))
              (usedColours n hn T S' g') (oddColourClass n)
            rw [← hCdef] at h1
            have h2 := huseO'
            omega
          · intro q s hs1 hsk hpos
            rw [husedins pos, Finset.insert_inter_of_notMem (hcol_notclass q (s + 1))] at hpos
            rw [husedins pos, Finset.insert_inter_of_notMem (hcol_notclass q (s + 1)),
              Finset.insert_inter_of_notMem (hcol_notclass q s), hocceq q]
            exact hdbl' q s hs1 hsk hpos
        · -- `w` on side `p`, one edge: fresh colour of the minimal available class
          -- into a free block.
          set uf := g' vf with hufdef
          have hwVp : w ∈ partClass part (some p) := mem_partClass.mpr hpw
          have hNp1 : 1 ≤ (partClass part (some p)).card :=
            Finset.card_pos.mpr ⟨w, hwVp⟩
          have hL2n : L ≤ 2 * n + 1 := by
            have h1 : 1 * L ≤ (partClass part (some p)).card * L :=
              Nat.mul_le_mul_right L hNp1
            rw [one_mul] at h1
            exact le_trans h1 (hJn p)
          have hfilt_lt : (S'.filter (fun v => part v = some p)).card
              < (partClass part (some p)).card := by
            have hsub : S'.filter (fun v => part v = some p)
                ⊆ (partClass part (some p)).erase w := by
              intro v hv
              rw [Finset.mem_filter] at hv
              exact Finset.mem_erase.mpr
                ⟨ne_of_mem_of_not_mem hv.1 hwS', mem_partClass.mpr hv.2⟩
            have h1 := Finset.card_le_card hsub
            have h2 := Finset.card_erase_of_mem hwVp
            omega
          have hocclt : (occupiedBlocks n S' g' (ap p) L (partClass part (some p)).card).card
              < (partClass part (some p)).card := by
            rw [hocc' p]
            exact hfilt_lt
          -- The free blocks.
          set freeSet : Finset ℕ := (Finset.range (partClass part (some p)).card)
            \ occupiedBlocks n S' g' (ap p) L (partClass part (some p)).card with hfreedef
          have hoccsub : occupiedBlocks n S' g' (ap p) L (partClass part (some p)).card
              ⊆ Finset.range (partClass part (some p)).card := Finset.filter_subset _ _
          have hfreecard : freeSet.card = (partClass part (some p)).card
              - (occupiedBlocks n S' g' (ap p) L (partClass part (some p)).card).card := by
            rw [hfreedef, Finset.card_sdiff, Finset.inter_eq_left.mpr hoccsub,
              Finset.card_range]
          have hF1 : 1 ≤ freeSet.card := by
            rw [hfreecard]
            omega
          -- The minimal available colour class `s₀`.
          have hchain : ∀ s, 1 ≤ s → s < k →
              0 < (usedColours n hn T S' g' ∩ sideClass n k p (s + 1)).card →
              (L / (2 * (2 * k + 1)) - 6) * (freeSet.card
                + (usedColours n hn T S' g' ∩ sideClass n k p (s + 1)).card)
              ≤ 2 * (usedColours n hn T S' g' ∩ sideClass n k p s).card + 2 := by
            intro s h1 h2 h3
            rw [hfreecard]
            exact hdbl' p s h1 h2 h3
          have hbound : (usedColours n hn T S' g' ∩ sideClass n k p 1).card < 2 ^ (k - 1) := by
            have hsub1 : usedColours n hn T S' g' ∩ sideClass n k p 1
                ⊆ usedColours n hn T S' g' ∩ sideClasses n k p :=
              Finset.inter_subset_inter (Finset.Subset.refl _)
                (sideClass_subset_sideClasses n k p le_rfl hk)
            have h1 := Finset.card_le_card hsub1
            have h2 := huseS' p
            have h3 := hpow p
            omega
          set avail : Finset ℕ := (Finset.Icc 1 k).filter
            (fun s => 2 * (usedColours n hn T S' g' ∩ sideClass n k p s).card + 2
              ≤ (L / (2 * (2 * k + 1)) - 6) * freeSet.card) with havaildef
          have havailne : avail.Nonempty := by
            obtain ⟨sa, ha1, ha2, ha3⟩ := exists_available_class k
              (L / (2 * (2 * k + 1)) - 6) freeSet.card
              (fun s => (usedColours n hn T S' g' ∩ sideClass n k p s).card)
              hk hQ4 hF1 hchain hbound
            exact ⟨sa, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨ha1, ha2⟩, ha3⟩⟩
          set s₀ := avail.min' havailne with hs₀def
          have hs₀mem : s₀ ∈ avail := Finset.min'_mem _ _
          have hs₀Icc : 1 ≤ s₀ ∧ s₀ ≤ k :=
            Finset.mem_Icc.mp (Finset.mem_filter.mp hs₀mem).1
          have hs₀avail : 2 * (usedColours n hn T S' g' ∩ sideClass n k p s₀).card + 2
              ≤ (L / (2 * (2 * k + 1)) - 6) * freeSet.card :=
            (Finset.mem_filter.mp hs₀mem).2
          have hs₀min : ∀ s, 1 ≤ s → s < s₀ →
              (L / (2 * (2 * k + 1)) - 6) * freeSet.card
                < 2 * (usedColours n hn T S' g' ∩ sideClass n k p s).card + 2 := by
            intro s h1 h2
            by_contra hcon
            push Not at hcon
            have hsavail : s ∈ avail := Finset.mem_filter.mpr
              ⟨Finset.mem_Icc.mpr ⟨h1, by omega⟩, hcon⟩
            have hle : s₀ ≤ s := Finset.min'_le avail s hsavail
            omega
          -- The witness set: class-`s₀` positions in free blocks.
          have hfreeN : ∀ j ∈ freeSet, j < (partClass part (some p)).card := by
            intro j hj
            rw [hfreedef, Finset.mem_sdiff] at hj
            exact Finset.mem_range.mp hj.1
          set W : Finset (Fin (2 * n + 1)) := freeSet.biUnion
            (fun j => (sideBlock n (ap p) L j).filter
              (fun u => ndColouring n hn s(uf, u) ∈ sideClass n k p s₀)) with hWdef
          have hdisjW : (↑freeSet : Set ℕ).PairwiseDisjoint
              (fun j => (sideBlock n (ap p) L j).filter
                (fun u => ndColouring n hn s(uf, u) ∈ sideClass n k p s₀)) := by
            intro j1 hj1 j2 hj2 hne
            exact Finset.disjoint_filter_filter
              (sideBlock_disjoint n (ap p) L _ (hJn p) (hfreeN j1 (Finset.mem_coe.mp hj1))
                (hfreeN j2 (Finset.mem_coe.mp hj2)) hne)
          have hWcard : (L / (2 * (2 * k + 1)) - 6) * freeSet.card ≤ W.card := by
            rw [hWdef, Finset.card_biUnion hdisjW]
            calc (L / (2 * (2 * k + 1)) - 6) * freeSet.card
                = freeSet.card • (L / (2 * (2 * k + 1)) - 6) := by
                  rw [smul_eq_mul, mul_comm]
              _ ≤ ∑ j ∈ freeSet, ((sideBlock n (ap p) L j).filter
                    (fun u => ndColouring n hn s(uf, u) ∈ sideClass n k p s₀)).card := by
                  refine Finset.card_nsmul_le_sum freeSet _ _ ?_
                  intro j _
                  have h := sideBlock_class_count n hn k L (ap p) hL2n p hs₀Icc.2 j uf
                  omega
          -- A fresh class-`s₀` position in a free block.
          have hlt : ({uf} : Finset (Fin (2 * n + 1))).card
              + 2 * (usedColours n hn T S' g' ∩ sideClass n k p s₀).card < W.card := by
            rw [Finset.card_singleton]
            omega
          obtain ⟨pos, hposW, hposuf, hposC⟩ := exists_fresh_position_in n hn uf W {uf}
            (Finset.mem_singleton_self uf)
            (usedColours n hn T S' g' ∩ sideClass n k p s₀) hlt
          rw [hWdef, Finset.mem_biUnion] at hposW
          obtain ⟨j₀, hj₀free, hposfilter⟩ := hposW
          rw [Finset.mem_filter] at hposfilter
          obtain ⟨hposb, hposclass⟩ := hposfilter
          have hj₀N : j₀ < (partClass part (some p)).card := hfreeN j₀ hj₀free
          have hj₀notocc : j₀ ∉ occupiedBlocks n S' g' (ap p) L
              (partClass part (some p)).card := by
            rw [hfreedef, Finset.mem_sdiff] at hj₀free
            exact hj₀free.2
          have hj₀no : ∀ v ∈ S', g' v ∉ sideBlock n (ap p) L j₀ := by
            intro v hv hmem
            exact hj₀notocc (Finset.mem_filter.mpr
              ⟨Finset.mem_range.mpr hj₀N, ⟨v, Finset.mem_filter.mpr ⟨hv, hmem⟩⟩⟩)
          -- The new colour and its class.
          have hcol_mem : ndColouring n hn s(pos, uf) ∈ sideClass n k p s₀ := by
            rwa [Sym2.eq_swap] at hposclass
          have hfresh : ndColouring n hn s(pos, uf) ∉ usedColours n hn T S' g' := by
            intro hmem
            apply hposC
            refine Finset.mem_inter.mpr ⟨?_, hposclass⟩
            rwa [Sym2.eq_swap]
          have hcol_side : ndColouring n hn s(pos, uf) ∈ sideClasses n k p :=
            sideClass_subset_sideClasses n k p hs₀Icc.1 hs₀Icc.2 hcol_mem
          have hcol_notsideq : ∀ q : Fin 2, q ≠ p →
              ndColouring n hn s(pos, uf) ∉ sideClasses n k q := fun q hqp h =>
            Finset.disjoint_left.mp (sideClasses_disjoint_of_ne n k hqp) h hcol_side
          have hcol_notclass : ∀ (q : Fin 2) (s : ℕ), 1 ≤ s → s ≤ k → (q ≠ p ∨ s ≠ s₀) →
              ndColouring n hn s(pos, uf) ∉ sideClass n k q s := by
            intro q s h1 h2 hne h
            rcases hne with hqp | hss
            · exact hcol_notsideq q hqp (sideClass_subset_sideClasses n k q h1 h2 h)
            · by_cases hqp : q = p
              · rw [hqp] at h
                refine Finset.disjoint_left.mp (sideClass_disjoint_of_ne n k ?_) h hcol_mem
                intro hres
                exact hss (by omega)
              · exact hcol_notsideq q hqp (sideClass_subset_sideClasses n k q h1 h2 h)
          have hcol_notodd : ndColouring n hn s(pos, uf) ∉ oddColourClass n := fun h =>
            Finset.disjoint_left.mp (oddColourClass_disjoint_sideClasses n k p) h hcol_side
          -- Injectivity of the extension.
          have hposJp : pos ∈ cyclicInterval n (ap p) ((partClass part (some p)).card * L) :=
            sideBlock_subset n (ap p) L _ hj₀N hposb
          have hposne : ∀ v ∈ S', g' v ≠ pos := by
            intro v hv h
            rcases hpv : part v with _ | q
            · refine Finset.disjoint_left.mp (hd0 p) (hmem0' v hv hpv) ?_
              rw [h]
              exact hposJp
            · obtain ⟨j, hj, hbj⟩ := hmemP' q v hv hpv
              by_cases hqp : q = p
              · rw [hqp] at hj hbj
                by_cases hjj : j = j₀
                · rw [hjj] at hbj
                  exact hj₀no v hv hbj
                · refine Finset.disjoint_left.mp
                    (sideBlock_disjoint n (ap p) L _ (hJn p) hj hj₀N hjj) hbj ?_
                  rw [h]
                  exact hposb
              · refine Finset.disjoint_left.mp (hd12 q p hqp)
                  (sideBlock_subset n (ap q) L _ hj hbj) ?_
                rw [h]
                exact hposJp
          -- Occupancy update.
          have hposblocks : ∀ q : Fin 2, ∀ j < (partClass part (some q)).card,
              pos ∈ sideBlock n (ap q) L j → q = p ∧ j = j₀ := by
            intro q j hj hposj
            by_cases hqp : q = p
            · refine ⟨hqp, ?_⟩
              by_contra hne
              rw [hqp] at hposj hj
              exact Finset.disjoint_left.mp
                (sideBlock_disjoint n (ap p) L _ (hJn p) hj hj₀N hne) hposj hposb
            · exact absurd hposJp (Finset.disjoint_left.mp (hd12 q p hqp)
                (sideBlock_subset n (ap q) L _ hj hposj))
          have hfilterq : ∀ q : Fin 2, (Finset.range (partClass part (some q)).card).filter
              (fun j => pos ∈ sideBlock n (ap q) L j)
              = if q = p then {j₀} else ∅ := by
            intro q
            by_cases hqp : q = p
            · rw [if_pos hqp]
              ext j
              simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
              constructor
              · rintro ⟨hj, hposj⟩
                exact (hposblocks q j hj hposj).2
              · rintro rfl
                rw [hqp]
                exact ⟨hj₀N, hposb⟩
            · rw [if_neg hqp, Finset.filter_eq_empty_iff]
              intro j hj hposj
              exact hqp (hposblocks q j (Finset.mem_range.mp hj) hposj).1
          have hoccq : ∀ q : Fin 2,
              occupiedBlocks n S (Function.update g' w pos) (ap q) L
                (partClass part (some q)).card
              = occupiedBlocks n S' g' (ap q) L (partClass part (some q)).card
                ∪ (if q = p then {j₀} else ∅) := by
            intro q
            rw [hSins, occupiedBlocks_insert n S' w hwS' g' pos (ap q) L _, hfilterq q]
          -- Assemble the invariant.
          refine ⟨Function.update g' w pos, hInjOnOf pos hposne, hrbins pos hfresh,
            ?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro v hv hpv
            by_cases hvw : v = w
            · subst hvw
              simp [hpw] at hpv
            · rw [Function.update_of_ne hvw]
              exact hmem0' v (Finset.mem_erase.mpr ⟨hvw, hv⟩) hpv
          · intro q v hv hpv
            by_cases hvw : v = w
            · subst hvw
              rw [hpw] at hpv
              have hqp : p = q := Option.some.inj hpv
              rw [Function.update_self]
              refine ⟨j₀, ?_, ?_⟩
              · rw [← hqp]
                exact hj₀N
              · rw [← hqp]
                exact hposb
            · rw [Function.update_of_ne hvw]
              exact hmemP' q v (Finset.mem_erase.mpr ⟨hvw, hv⟩) hpv
          · intro q
            rw [hoccq q, hfiltins (some q), hpw]
            by_cases hqp : q = p
            · have hj₀nocc : j₀ ∉ occupiedBlocks n S' g' (ap q) L
                  (partClass part (some q)).card := by
                rw [hqp]
                exact hj₀notocc
              rw [if_pos hqp, if_pos (show (some p : Option (Fin 2)) = some q by rw [hqp]),
                Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr hj₀nocc),
                Finset.card_singleton, hocc' q]
            · rw [if_neg hqp, if_neg (fun h => hqp (Option.some.inj h).symm),
                Finset.union_empty, hocc' q, Nat.add_zero]
          · intro q
            by_cases hqp : q = p
            · rw [husedins pos, hfiltins (some q), hpw,
                if_pos (show (some p : Option (Fin 2)) = some q by rw [hqp])]
              have h1 := card_inter_insert_le (ndColouring n hn s(pos, uf))
                (usedColours n hn T S' g') (sideClasses n k q)
              have h2 := huseS' q
              omega
            · rw [husedins pos, Finset.insert_inter_of_notMem (hcol_notsideq q hqp),
                hfiltins (some q), hpw, if_neg (fun h => hqp (Option.some.inj h).symm),
                Nat.add_zero]
              exact huseS' q
          · rw [husedins pos, Finset.insert_inter_of_notMem hcol_notodd,
              hfiltins none, hpw, if_neg (by simp), Nat.add_zero]
            exact huseO'
          · -- Preservation of the doubling invariant: the mathematical heart.
            intro q s hs1 hsk hpos
            rw [husedins pos] at hpos
            rw [husedins pos, hoccq q]
            by_cases hqp : q = p
            · rw [hqp] at hpos ⊢
              rw [if_pos rfl,
                Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr hj₀notocc),
                Finset.card_singleton]
              by_cases hs1s : s + 1 = s₀
              · -- `s = s₀ - 1`: use minimality (class `s₀` fresh) or the stored invariant.
                have hsne : s ≠ s₀ := by omega
                rw [Finset.insert_inter_of_notMem
                  (hcol_notclass p s (by omega) (by omega) (Or.inr hsne))]
                have hins : (insert (ndColouring n hn s(pos, uf)) (usedColours n hn T S' g')
                    ∩ sideClass n k p (s + 1)).card
                    = (usedColours n hn T S' g' ∩ sideClass n k p (s + 1)).card + 1 := by
                  refine card_inter_insert_of_mem_of_notMem ?_ hfresh
                  rw [hs1s]
                  exact hcol_mem
                rw [hins]
                by_cases hu0 : (usedColours n hn T S' g' ∩ sideClass n k p (s + 1)).card = 0
                · rw [hu0]
                  have hmin : (L / (2 * (2 * k + 1)) - 6) * freeSet.card
                      < 2 * (usedColours n hn T S' g' ∩ sideClass n k p s).card + 2 := by
                    refine hs₀min s hs1 ?_
                    omega
                  have harg : (partClass part (some p)).card
                      - ((occupiedBlocks n S' g' (ap p) L
                          (partClass part (some p)).card).card + 1) + (0 + 1)
                      = freeSet.card := by
                    rw [hfreecard]
                    omega
                  rw [harg]
                  omega
                · have hpos' : 0 < (usedColours n hn T S' g'
                      ∩ sideClass n k p (s + 1)).card := by omega
                  have hold := hdbl' p s hs1 hsk hpos'
                  have harg : (partClass part (some p)).card
                      - ((occupiedBlocks n S' g' (ap p) L
                          (partClass part (some p)).card).card + 1)
                      + ((usedColours n hn T S' g' ∩ sideClass n k p (s + 1)).card + 1)
                      = (partClass part (some p)).card
                      - (occupiedBlocks n S' g' (ap p) L
                          (partClass part (some p)).card).card
                      + (usedColours n hn T S' g' ∩ sideClass n k p (s + 1)).card := by
                    omega
                  rw [harg]
                  exact hold
              · -- class `s+1` untouched by the new colour
                have hnotin1 := hcol_notclass p (s + 1) (by omega) (by omega) (Or.inr hs1s)
                rw [Finset.insert_inter_of_notMem hnotin1] at hpos
                rw [Finset.insert_inter_of_notMem hnotin1]
                have hold := hdbl' p s hs1 hsk hpos
                by_cases hss : s = s₀
                · -- `s = s₀`: the used count grows with the right-hand side
                  have hins : (insert (ndColouring n hn s(pos, uf)) (usedColours n hn T S' g')
                      ∩ sideClass n k p s).card
                      = (usedColours n hn T S' g' ∩ sideClass n k p s).card + 1 := by
                    refine card_inter_insert_of_mem_of_notMem ?_ hfresh
                    rw [hss]
                    exact hcol_mem
                  rw [hins]
                  refine le_trans (le_trans (Nat.mul_le_mul_left _ (by omega)) hold)
                    (by omega)
                · -- untouched classes: the invariant only relaxes
                  rw [Finset.insert_inter_of_notMem
                    (hcol_notclass p s (by omega) (by omega) (Or.inr hss))]
                  exact le_trans (Nat.mul_le_mul_left _ (by omega)) hold
            · -- other side: nothing changed
              have hnotin1 := hcol_notclass q (s + 1) (by omega) (by omega) (Or.inl hqp)
              rw [Finset.insert_inter_of_notMem hnotin1] at hpos
              rw [Finset.insert_inter_of_notMem hnotin1,
                Finset.insert_inter_of_notMem
                  (hcol_notclass q s (by omega) (by omega) (Or.inl hqp)),
                if_neg hqp, Finset.union_empty]
              exact hdbl' q s hs1 hsk hpos

/-- **Embedding a small tree into prescribed intervals** (`Lemma_small_tree`, MPS §7).
A forest `T` with vertex partition given by `part` (`none` ↦ `V₀`, `some p` ↦ side `p`)
embeds rainbow into the ND-coloured `K_{2n+1}` so that `V₀` lands in the cyclic interval
`I₀` based at `a₀`, and each side-`p` vertex lands in its own private length-`L` block
among the `|Vₚ|` consecutive blocks based at `ap p` (the block index map `bIdx` is
injective on each side).  In particular consecutive side-`p` images are at cyclic distance
less than `2L`. -/
theorem small_tree_into_intervals (n : ℕ) (hn : 0 < n) {V : Type*} [Fintype V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hac : T.IsAcyclic)
    (part : V → Option (Fin 2)) (k L : ℕ) (hk : 1 ≤ k)
    (a₀ : Fin (2 * n + 1)) (len₀ : ℕ) (ap : Fin 2 → Fin (2 * n + 1))
    (hlen₀n : len₀ ≤ 2 * n + 1)
    (hlen₀ : 6 * (partClass part none).card + 12 ≤ len₀)
    (hQ : 10 ≤ L / (2 * (2 * k + 1)))
    (hJn : ∀ p : Fin 2, (partClass part (some p)).card * L ≤ 2 * n + 1)
    (hpow : ∀ p : Fin 2, (partClass part (some p)).card < 2 ^ (k - 1))
    (hd0 : ∀ p : Fin 2, Disjoint (cyclicInterval n a₀ len₀)
      (cyclicInterval n (ap p) ((partClass part (some p)).card * L)))
    (hd12 : ∀ p q : Fin 2, p ≠ q → Disjoint
      (cyclicInterval n (ap p) ((partClass part (some p)).card * L))
      (cyclicInterval n (ap q) ((partClass part (some q)).card * L))) :
    ∃ (g : V → Fin (2 * n + 1)) (bIdx : V → ℕ),
      Function.Injective g ∧
      Set.InjOn (ndColouring n hn) ↑(T.edgeFinset.image (Sym2.map g)) ∧
      (∀ v, part v = none → g v ∈ cyclicInterval n a₀ len₀) ∧
      (∀ p : Fin 2, ∀ v, part v = some p →
        bIdx v < (partClass part (some p)).card ∧ g v ∈ sideBlock n (ap p) L (bIdx v)) ∧
      (∀ p : Fin 2, Set.InjOn bIdx ↑(partClass part (some p))) := by
  classical
  obtain ⟨g, hinv⟩ := small_tree_greedy n hn T hac part k L hk a₀ len₀ ap
    hlen₀n hlen₀ hQ hJn hpow hd0 hd12 Finset.univ
  obtain ⟨hinj, hrb, hmem0, hmemP, hocc, _, _, _⟩ := hinv
  have hedge : T.edgeFinset ∩ (Finset.univ : Finset V).sym2 = T.edgeFinset := by
    ext e
    induction e using Sym2.ind with
    | _ x y => simp
  rw [hedge] at hrb
  have hginj : Function.Injective g := fun a b hab =>
    hinj (Finset.mem_coe.mpr (Finset.mem_univ a)) (Finset.mem_coe.mpr (Finset.mem_univ b)) hab
  -- Choose the block index of each side vertex.
  have hchoice : ∀ v : V, ∃ j : ℕ, ∀ p : Fin 2, part v = some p →
      j < (partClass part (some p)).card ∧ g v ∈ sideBlock n (ap p) L j := by
    intro v
    rcases hpv : part v with _ | p
    · exact ⟨0, fun p hp => absurd hp (by simp)⟩
    · obtain ⟨j, hj, hbj⟩ := hmemP p v (Finset.mem_univ v) hpv
      refine ⟨j, fun q hq => ?_⟩
      have hpq : p = q := Option.some.inj hq
      rw [← hpq]
      exact ⟨hj, hbj⟩
  choose bIdx hbIdx using hchoice
  have hmemBlocks : ∀ p : Fin 2, ∀ v, part v = some p →
      bIdx v < (partClass part (some p)).card ∧ g v ∈ sideBlock n (ap p) L (bIdx v) :=
    fun p v hv => hbIdx v p hv
  -- One vertex per block: `bIdx` is injective on each side by counting.
  have hbinj : ∀ p : Fin 2, Set.InjOn bIdx ↑(partClass part (some p)) := by
    intro p
    rw [← Finset.card_image_iff]
    have himg : (partClass part (some p)).image bIdx
        = occupiedBlocks n Finset.univ g (ap p) L (partClass part (some p)).card := by
      ext j
      simp only [Finset.mem_image, occupiedBlocks, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨v, hv, rfl⟩
        have hpv := mem_partClass.mp hv
        obtain ⟨hlt, hblk⟩ := hmemBlocks p v hpv
        exact ⟨hlt, ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hblk⟩⟩⟩
      · rintro ⟨hj, v, hv⟩
        rw [Finset.mem_filter] at hv
        have hgv := hv.2
        rcases hpv : part v with _ | q
        · exact absurd (sideBlock_subset n (ap p) L _ hj hgv)
            (Finset.disjoint_left.mp (hd0 p) (hmem0 v (Finset.mem_univ v) hpv))
        · obtain ⟨hlt, hblk⟩ := hmemBlocks q v hpv
          by_cases hqp : q = p
          · rw [hqp] at hlt hblk
            have hjb : j = bIdx v := by
              by_contra hne
              exact Finset.disjoint_left.mp
                (sideBlock_disjoint n (ap p) L _ (hJn p) hj hlt hne) hgv hblk
            exact ⟨v, mem_partClass.mpr (by rw [hpv, hqp]), hjb.symm⟩
          · exact absurd (sideBlock_subset n (ap p) L _ hj hgv)
              (Finset.disjoint_left.mp (hd12 q p hqp)
                (sideBlock_subset n (ap q) L _ hlt hblk))
    rw [himg, hocc p]
    rfl
  exact ⟨g, bIdx, hginj, hrb, fun v h => hmem0 v (Finset.mem_univ v) h, hmemBlocks, hbinj⟩

/-- Index form of `small_tree_into_intervals`: each side-`p` image is the `idx v`-th
cyclic successor of the side base `ap p`, with `idx v < |Vₚ|·L` and distinct vertices in
distinct length-`L` blocks (`idx u / L ≠ idx v / L`).  All downstream spacing arithmetic
(the `Theorem_case_C` leaf-attachment) is linear in these indices. -/
theorem small_tree_into_intervals_idx (n : ℕ) (hn : 0 < n) {V : Type*} [Fintype V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hac : T.IsAcyclic)
    (part : V → Option (Fin 2)) (k L : ℕ) (hk : 1 ≤ k)
    (a₀ : Fin (2 * n + 1)) (len₀ : ℕ) (ap : Fin 2 → Fin (2 * n + 1))
    (hlen₀n : len₀ ≤ 2 * n + 1)
    (hlen₀ : 6 * (partClass part none).card + 12 ≤ len₀)
    (hQ : 10 ≤ L / (2 * (2 * k + 1)))
    (hJn : ∀ p : Fin 2, (partClass part (some p)).card * L ≤ 2 * n + 1)
    (hpow : ∀ p : Fin 2, (partClass part (some p)).card < 2 ^ (k - 1))
    (hd0 : ∀ p : Fin 2, Disjoint (cyclicInterval n a₀ len₀)
      (cyclicInterval n (ap p) ((partClass part (some p)).card * L)))
    (hd12 : ∀ p q : Fin 2, p ≠ q → Disjoint
      (cyclicInterval n (ap p) ((partClass part (some p)).card * L))
      (cyclicInterval n (ap q) ((partClass part (some q)).card * L))) :
    ∃ (g : V → Fin (2 * n + 1)) (idx : V → ℕ),
      Function.Injective g ∧
      Set.InjOn (ndColouring n hn) ↑(T.edgeFinset.image (Sym2.map g)) ∧
      (∀ v, part v = none → g v ∈ cyclicInterval n a₀ len₀) ∧
      (∀ p : Fin 2, ∀ v, part v = some p →
        idx v < (partClass part (some p)).card * L ∧
        cyclicShift n (ap p) (idx v) = g v) ∧
      (∀ p : Fin 2, ∀ u, part u = some p → ∀ v, part v = some p → u ≠ v →
        idx u / L ≠ idx v / L) := by
  classical
  obtain ⟨g, bIdx, hginj, hrb, hmem0, hmemP, hbinj⟩ := small_tree_into_intervals n hn T hac
    part k L hk a₀ len₀ ap hlen₀n hlen₀ hQ hJn hpow hd0 hd12
  have hL1 : 1 ≤ L := le_trans (by omega) (Nat.div_le_self L (2 * (2 * k + 1)))
  -- Extract the in-block offset of each side vertex.
  have hchoice : ∀ v : V, ∃ i : ℕ, ∀ p : Fin 2, part v = some p →
      i < L ∧ cyclicShift n (ap p) (bIdx v * L + i) = g v := by
    intro v
    rcases hpv : part v with _ | p
    · exact ⟨0, fun p hp => absurd hp (by simp)⟩
    · obtain ⟨hblt, hblk⟩ := hmemP p v hpv
      rw [sideBlock_eq] at hblk
      obtain ⟨i, hi, hshift⟩ := mem_cyclicInterval.mp hblk
      rw [cyclicShift_cyclicShift] at hshift
      refine ⟨i, fun q hq => ?_⟩
      have hpq : p = q := Option.some.inj hq
      rw [← hpq]
      exact ⟨hi, hshift⟩
  choose off hoff using hchoice
  have hdiv_eq : ∀ v p, part v = some p → (bIdx v * L + off v) / L = bIdx v := by
    intro v p hv
    obtain ⟨hiL, _⟩ := hoff v p hv
    rw [add_comm, Nat.add_mul_div_right _ _ (show 0 < L by omega),
      Nat.div_eq_of_lt hiL, Nat.zero_add]
  refine ⟨g, fun v => bIdx v * L + off v, hginj, hrb, hmem0, ?_, ?_⟩
  · intro p v hv
    obtain ⟨hiL, hshift⟩ := hoff v p hv
    obtain ⟨hblt, _⟩ := hmemP p v hv
    refine ⟨?_, hshift⟩
    change bIdx v * L + off v < (partClass part (some p)).card * L
    have h2 := Nat.mul_le_mul_right L (show bIdx v + 1 ≤ (partClass part (some p)).card
      from hblt)
    rw [add_mul, one_mul] at h2
    omega
  · intro p u hu v hv huv hdiv
    rw [hdiv_eq u p hu, hdiv_eq v p hv] at hdiv
    exact huv (hbinj p (Finset.mem_coe.mpr (mem_partClass.mpr hu))
      (Finset.mem_coe.mpr (mem_partClass.mpr hv)) hdiv)

end Ringel
