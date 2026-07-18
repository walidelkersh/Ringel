/-
Copyright (c) 2026 Walid Elkersh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Walid Elkersh
-/
import Ringel.Primitives
import Ringel.SmallTree

/-!
# Case C: assembling the rainbow copy (`Theorem_case_C`, MPS §7)

This file assembles the Case C embedding: the small core is embedded by
`small_tree_into_intervals_idx`, and the removed leaves are re-attached by explicit
position arithmetic (`u - (c+1)` for type 1 vertices, `u + (c+1)` for types 2 and 3,
realizing the colour `c` on the new edge by `ndColouring_step`).

The present part is the generic *leaf re-attachment engine*
(`extend_rainbow_leaves`): given a rainbow embedding `g` of the core of `T` and a
placement `pos` of the leaves such that positions are fresh and the leaf-edge colours
are fresh and pairwise distinct, the combined map is a rainbow embedding of `T`.
-/

open SimpleGraph

namespace Ringel

/-- **Leaf re-attachment.** Let `leaves` be a set of leaves of `T` with anchors outside
`leaves`, such that every `T`-edge either avoids `leaves` (a *core* edge) or is an
anchor edge `s(x, anchor x)`.  Given a core embedding `g` (injective off `leaves`,
rainbow on core edges) and a leaf placement `pos` with fresh injective positions and
fresh pairwise-distinct leaf-edge colours, the map `f = if · ∈ leaves then pos else g`
is a rainbow embedding of `T`. -/
lemma extend_rainbow_leaves (n : ℕ) (hn : 0 < n) {V : Type*}
    (T : SimpleGraph V)
    (leaves : Finset V) (anchor : V → V)
    (hanchor : ∀ x ∈ leaves, anchor x ∉ leaves)
    (hedges : ∀ e ∈ T.edgeSet,
      (∀ x ∈ leaves, x ∉ e) ∨ ∃ x ∈ leaves, e = s(x, anchor x))
    (g pos : V → Fin (2 * n + 1))
    (hginj : Set.InjOn g {v | v ∉ leaves})
    (hposinj : Set.InjOn pos ↑leaves)
    (hdisj : ∀ x ∈ leaves, ∀ v, v ∉ leaves → pos x ≠ g v)
    (hrb_core : ∀ e₁ ∈ T.edgeSet, ∀ e₂ ∈ T.edgeSet, (∀ x ∈ leaves, x ∉ e₁) →
      (∀ x ∈ leaves, x ∉ e₂) →
      ndColouring n hn (Sym2.map g e₁) = ndColouring n hn (Sym2.map g e₂) →
      Sym2.map g e₁ = Sym2.map g e₂)
    (hleafcol_inj : ∀ x₁ ∈ leaves, ∀ x₂ ∈ leaves,
      ndColouring n hn s(pos x₁, g (anchor x₁))
        = ndColouring n hn s(pos x₂, g (anchor x₂)) → x₁ = x₂)
    (hleafcol_fresh : ∀ x ∈ leaves, ∀ e ∈ T.edgeSet, (∀ y ∈ leaves, y ∉ e) →
      ndColouring n hn s(pos x, g (anchor x)) ≠ ndColouring n hn (Sym2.map g e)) :
    ∃ f : V ↪ Fin (2 * n + 1), Set.InjOn (ndColouring n hn) (T.map f).edgeSet := by
  classical
  set f : V → Fin (2 * n + 1) := fun v => if v ∈ leaves then pos v else g v with hfdef
  have hfleaf : ∀ x ∈ leaves, f x = pos x := by
    intro x hx
    simp only [hfdef, if_pos hx]
  have hfcore : ∀ v, v ∉ leaves → f v = g v := by
    intro v hv
    simp only [hfdef, if_neg hv]
  -- `f` is injective.
  have hfinj : Function.Injective f := by
    intro a b hab
    by_cases ha : a ∈ leaves
    · by_cases hb : b ∈ leaves
      · rw [hfleaf a ha, hfleaf b hb] at hab
        exact hposinj (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab
      · rw [hfleaf a ha, hfcore b hb] at hab
        exact absurd hab (hdisj a ha b hb)
    · by_cases hb : b ∈ leaves
      · rw [hfcore a ha, hfleaf b hb] at hab
        exact absurd hab.symm (hdisj b hb a ha)
      · rw [hfcore a ha, hfcore b hb] at hab
        exact hginj ha hb hab
  -- `f` agrees with `g` on core edges and sends anchor edges to `s(pos x, g (anchor x))`.
  have hmapcore : ∀ e : Sym2 V, (∀ x ∈ leaves, x ∉ e) → Sym2.map f e = Sym2.map g e := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      have ha : a ∉ leaves := fun h => he a h (Sym2.mem_mk_left a b)
      have hb : b ∉ leaves := fun h => he b h (Sym2.mem_mk_right a b)
      simp only [Sym2.map_mk, Prod.map_apply, hfcore a ha, hfcore b hb]
  have hmapleaf : ∀ x ∈ leaves, Sym2.map f s(x, anchor x) = s(pos x, g (anchor x)) := by
    intro x hx
    simp only [Sym2.map_mk, Prod.map_apply, hfleaf x hx, hfcore (anchor x) (hanchor x hx)]
  -- Rainbow on the mapped edge set.
  refine ⟨⟨f, hfinj⟩, ?_⟩
  rw [SimpleGraph.edgeSet_map]
  rintro e₁' ⟨e₁, he₁, rfl⟩ e₂' ⟨e₂, he₂, rfl⟩ hcol
  simp only [Function.Embedding.sym2Map_apply, Function.Embedding.coeFn_mk] at hcol ⊢
  rcases hedges e₁ he₁ with hc₁ | ⟨x₁, hx₁, rfl⟩
  · rcases hedges e₂ he₂ with hc₂ | ⟨x₂, hx₂, rfl⟩
    · -- core / core
      rw [hmapcore e₁ hc₁, hmapcore e₂ hc₂] at hcol ⊢
      exact hrb_core e₁ he₁ e₂ he₂ hc₁ hc₂ hcol
    · -- core / leaf
      rw [hmapcore e₁ hc₁, hmapleaf x₂ hx₂] at hcol
      exact absurd hcol.symm (hleafcol_fresh x₂ hx₂ e₁ he₁ hc₁)
  · rcases hedges e₂ he₂ with hc₂ | ⟨x₂, hx₂, rfl⟩
    · -- leaf / core
      rw [hmapleaf x₁ hx₁, hmapcore e₂ hc₂] at hcol
      exact absurd hcol (hleafcol_fresh x₁ hx₁ e₂ he₂ hc₂)
    · -- leaf / leaf
      rw [hmapleaf x₁ hx₁, hmapleaf x₂ hx₂] at hcol
      have hx12 : x₁ = x₂ := hleafcol_inj x₁ hx₁ x₂ hx₂ hcol
      rw [hx12]

/-- Along a `<`-sorted list in `Fin n`, values grow at least as fast as indices: the
value at position `j` is at least the value at position `i ≤ j` plus `j - i`.  This is
the engine of every colour-block gap estimate in the Case C assembly: consecutive
blocks of the sorted free-colour list are separated by at least the sizes of the blocks
between them. -/
lemma sorted_val_add_index_le {n : ℕ} {l : List (Fin n)} (hs : l.Pairwise (· < ·))
    {i j : ℕ} (hi : i ≤ j) (hj : j < l.length) :
    (l[i]'(lt_of_le_of_lt hi hj)).val + (j - i) ≤ (l[j]'hj).val := by
  induction j with
  | zero =>
    have hi0 : i = 0 := by omega
    subst hi0
    simp
  | succ j ihj =>
    rcases Nat.eq_or_lt_of_le hi with rfl | hlt
    · simp
    · have hij : i ≤ j := by omega
      have hjl : j < l.length := by omega
      have hstep : l[j]'hjl < l[j + 1]'hj :=
        List.pairwise_iff_getElem.mp hs j (j + 1) hjl hj (by omega)
      have hrec := ihj hij hjl
      have hval : (l[j]'hjl).val < (l[j + 1]'hj).val := hstep
      omega

/-- Attaching a leaf *below* `u`: the edge from `u` down to `u - (c+1)` has colour `c`
(type 1 attachment). -/
lemma ndColouring_attach_sub (n : ℕ) (hn : 0 < n) (u : Fin (2 * n + 1)) (c : Fin n)
    (hle : c.val + 1 ≤ u.val) :
    ndColouring n hn s(⟨u.val - (c.val + 1), by omega⟩, u) = c := by
  have hδlt : c.val + 1 < 2 * n + 1 := by
    have := c.isLt
    omega
  have hstep := ndColouring_step n hn ⟨u.val - (c.val + 1), by omega⟩ ⟨c.val + 1, hδlt⟩ c
    (Or.inl rfl)
  have hadd : (⟨u.val - (c.val + 1), by omega⟩ : Fin (2 * n + 1)) + ⟨c.val + 1, hδlt⟩ = u := by
    apply Fin.ext
    change (u.val - (c.val + 1) + (c.val + 1)) % (2 * n + 1) = u.val
    rw [show u.val - (c.val + 1) + (c.val + 1) = u.val by omega]
    exact Nat.mod_eq_of_lt u.isLt
  rwa [hadd] at hstep

/-- Attaching a leaf *above* `u`: the edge from `u` up to `u + (c+1)` has colour `c`
(type 2 and type 3 attachment). -/
lemma ndColouring_attach_add (n : ℕ) (hn : 0 < n) (u : Fin (2 * n + 1)) (c : Fin n)
    (hle : u.val + c.val + 1 ≤ 2 * n) :
    ndColouring n hn s(u, ⟨u.val + c.val + 1, by omega⟩) = c := by
  have hδlt : c.val + 1 < 2 * n + 1 := by
    have := c.isLt
    omega
  have hstep := ndColouring_step n hn u ⟨c.val + 1, hδlt⟩ c (Or.inl rfl)
  have hadd : u + (⟨c.val + 1, hδlt⟩ : Fin (2 * n + 1))
      = ⟨u.val + c.val + 1, by omega⟩ := by
    apply Fin.ext
    change (u.val + (c.val + 1)) % (2 * n + 1) = u.val + c.val + 1
    rw [show u.val + (c.val + 1) = u.val + c.val + 1 by omega]
    exact Nat.mod_eq_of_lt (by omega)
  rwa [hadd] at hstep

/-- An injective map from an `m`-element finset into `{0, …, m-1}` is surjective:
every rank `r < m` is attained.  Used to enumerate the side vertices by their
(one-per-block) block index. -/
lemma finset_bij_of_injOn_lt {V : Type*} (S : Finset V) (m : ℕ)
    (hcard : S.card = m) (b : V → ℕ) (hlt : ∀ v ∈ S, b v < m)
    (hinj : Set.InjOn b ↑S) :
    ∀ r < m, ∃ v ∈ S, b v = r := by
  intro r hr
  have himg : S.image b = Finset.range m := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_range.mpr (hlt v hv)
    · rw [Finset.card_range, Finset.card_image_of_injOn hinj, hcard]
  have hmem : r ∈ S.image b := by
    rw [himg]
    exact Finset.mem_range.mpr hr
  obtain ⟨v, hv, hbv⟩ := Finset.mem_image.mp hmem
  exact ⟨v, hv, hbv⟩

/-- Greedy subset selection: if every part is at most `a` and the total exceeds `a`,
some subset has sum in `(a, 2a]`.  Selects the `V₁` side (the vertices whose colour
blocks form the low colours) without sorting. -/
lemma exists_subset_sum_between {V : Type*} (S : Finset V) (f : V → ℕ)
    (a : ℕ) (htotal : a < ∑ v ∈ S, f v) (hsmall : ∀ v ∈ S, f v ≤ a) :
    ∃ S' ⊆ S, a < ∑ v ∈ S', f v ∧ ∑ v ∈ S', f v ≤ 2 * a := by
  classical
  induction S using Finset.strongInduction with
  | _ S ih =>
    have hSne : S.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      subst h
      simp at htotal
    obtain ⟨v, hv⟩ := hSne
    rcases Nat.lt_or_ge a (∑ u ∈ S.erase v, f u) with hgt | hle
    · obtain ⟨S', hS'sub, hS'⟩ := ih (S.erase v) (Finset.erase_ssubset hv) hgt
        (fun u hu => hsmall u (Finset.mem_of_mem_erase hu))
      exact ⟨S', fun x hx => Finset.mem_of_mem_erase (hS'sub hx), hS'⟩
    · refine ⟨S, Finset.Subset.refl S, htotal, ?_⟩
      have hsplit : ∑ u ∈ S, f u = f v + ∑ u ∈ S.erase v, f u :=
        (Finset.add_sum_erase S f hv).symm
      have hfv := hsmall v hv
      omega

/-- Enumeration of a finset by ranks `0, …, |S|-1`. -/
lemma finset_enum {V : Type*} [Nonempty V] (S : Finset V) :
    ∃ e : ℕ → V, (∀ a, a < S.card → e a ∈ S) ∧
      (∀ a, a < S.card → ∀ b, b < S.card → e a = e b → a = b) ∧
      (∀ v ∈ S, ∃ a, a < S.card ∧ e a = v) := by
  classical
  have hlen : S.toList.length = S.card := Finset.length_toList S
  refine ⟨fun a => S.toList.getD a (Classical.arbitrary V), ?_, ?_, ?_⟩
  · intro a ha
    dsimp only
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact Finset.mem_toList.mp (List.getElem_mem _)
  · intro a ha b hb hab
    dsimp only at hab
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at hab
    exact (List.Nodup.getElem_inj_iff (Finset.nodup_toList S)).mp hab
  · intro v hv
    obtain ⟨a, ha, hav⟩ := List.mem_iff_getElem.mp (Finset.mem_toList.mpr hv)
    refine ⟨a, by omega, ?_⟩
    dsimp only
    rw [List.getD_eq_getElem _ _ ha]
    exact hav

end Ringel
