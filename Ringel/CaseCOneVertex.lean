/-
Copyright (c) 2026 Walid K. Elkersh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Walid K. Elkersh
-/
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
import Ringel.Primitives
import Ringel.TreeStructure

/-!
# Case C: trees with one vertex of very high degree

This file proves `one_large_vertex` (`Theorem_one_large_vertex`, §2 of arXiv:2001.02665): if an
`(n+1)`-vertex tree `T` has a vertex `v₁` adjacent to at least `2n/3` leaves, then the ND-coloured
`K_{2n+1}` contains a rainbow copy of `T`.

The proof follows the paper. Let `T'` be `T` with the leaf-neighbours of `v₁` removed, so
`|T'| ≤ n/3 + 1`. Greedily embed `T'` **inside the interval `[0, n]`** of `Fin (2n+1)` with `v₁`
placed at `0`, keeping the copy rainbow: at each step at most `|T'| - 1` positions are occupied and
at most `|T'| - 2` colours are used, and since the ND-colouring is a 2-factorization these forbid
at most `3|T'| - 5 ≤ n` of the `n+1` positions of the interval, so a fresh position always exists.
Finally, each colour `c` unused by the copy of `T'` is realized by attaching a leaf to `v₁` at
position `-(c+1) = 2n - c`, which lies in `[n+1, 2n]` — disjoint from the interval holding `T'` —
and the number of unused colours is exactly the number of removed leaves.

The interval-restricted greedy (`greedy_embed_interval`) generalizes the free greedy of
`CaseC.lean` and is reused by the general Case C embedding.
-/

open SimpleGraph

namespace Ringel

/-- **Forest edge count inside a vertex subset.** For an acyclic graph, the edges with both
endpoints in a nonempty finset `R` number at most `|R| - 1`. (The induced subgraph is a forest,
whose edge count is `|R|` minus its number of components.) -/
lemma card_edges_in_subset_lt {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsAcyclic)
    (R : Finset V) (hR : R.Nonempty) :
    (G.edgeFinset ∩ R.sym2).card + 1 ≤ R.card := by
  classical
  haveI : Nonempty (R : Set V) := hR.coe_sort
  have hid := TreeStructure.card_connectedComponent_add_card_edgeFinset
    (G.induce (R : Set V)) (hG.induce _)
  have hcomp : 1 ≤ Fintype.card (G.induce (R : Set V)).ConnectedComponent := Fintype.card_pos
  have hcardR : Fintype.card (R : Set V) = R.card := by
    rw [Fintype.card_congr (Equiv.subtypeEquivRight (fun x => Finset.mem_coe))]
    exact Fintype.card_coe R
  have hsurj : Set.SurjOn (Sym2.map (Subtype.val : ↥(R : Set V) → V))
      ↑(G.induce (R : Set V)).edgeFinset ↑(G.edgeFinset ∩ R.sym2) := by
    intro e he
    rw [Finset.coe_inter, Set.mem_inter_iff, Finset.mem_coe, Finset.mem_coe] at he
    induction e using Sym2.ind with
    | _ x y =>
      have hadj : G.Adj x y := by
        have := he.1
        rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at this
      have hxy : x ∈ R ∧ y ∈ R := by
        have := he.2
        rwa [Finset.mk_mem_sym2_iff] at this
      refine ⟨s(⟨x, hxy.1⟩, ⟨y, hxy.2⟩), ?_, ?_⟩
      · rw [Finset.mem_coe, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        exact hadj
      · rw [Sym2.map_mk, Prod.map_apply]
  have hle := Finset.card_le_card_of_surjOn _ hsurj
  omega

/-- **Forests have a low-degree vertex distinct from any given vertex.** In a finite acyclic graph
on at least two vertices, for every vertex `x` there is a vertex `w ≠ x` of degree at most `1`.
(If all vertices other than `x` had degree `≥ 2`, the handshake identity would force the graph to
be a tree in which `x` is isolated — impossible.) -/
lemma exists_degree_le_one_ne {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsAcyclic) (x : V)
    (h2 : 2 ≤ Fintype.card V) :
    ∃ w, w ≠ x ∧ G.degree w ≤ 1 := by
  classical
  by_contra h
  push Not at h
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hsum : ∑ v, G.degree v = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
  have hid := TreeStructure.card_connectedComponent_add_card_edgeFinset G hG
  have hcomp1 : 1 ≤ Fintype.card G.ConnectedComponent := Fintype.card_pos
  have herase : 2 * (Fintype.card V - 1) ≤ ∑ w ∈ Finset.univ.erase x, G.degree w := by
    have hbound : ∀ w ∈ Finset.univ.erase x, 2 ≤ G.degree w := by
      intro w hw
      exact h w (Finset.ne_of_mem_erase hw)
    calc 2 * (Fintype.card V - 1) = (Finset.univ.erase x).card * 2 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ, mul_comm]
      _ = ∑ _w ∈ Finset.univ.erase x, 2 := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ w ∈ Finset.univ.erase x, G.degree w := Finset.sum_le_sum hbound
  have hsplit : G.degree x + ∑ w ∈ Finset.univ.erase x, G.degree w = ∑ v, G.degree v :=
    Finset.add_sum_erase Finset.univ (fun v => G.degree v) (Finset.mem_univ x)
  -- Combining: `deg x = 0` and the graph is connected.
  have hdegx : G.degree x = 0 := by omega
  have hcomp : Fintype.card G.ConnectedComponent = 1 := by omega
  -- Connectivity gives `x` a neighbour, contradicting `deg x = 0`.
  obtain ⟨y, hy⟩ := Fintype.exists_ne_of_one_lt_card (by omega) x
  have hreach : G.Reachable x y := by
    have hsub : Subsingleton G.ConnectedComponent :=
      Fintype.card_le_one_iff_subsingleton.mp (by omega)
    exact (SimpleGraph.ConnectedComponent.eq).mp (Subsingleton.elim _ _)
  obtain ⟨p⟩ := hreach
  cases p with
  | nil => exact hy rfl
  | cons hadj _ =>
    have hpos : 0 < G.degree x := (G.degree_pos_iff_exists_adj x).mpr ⟨_, hadj⟩
    omega

/-- **Fresh position inside a target set.** With a placed vertex at `p_u ∈ U`, used positions `U`,
forbidden colours `C`, and a target position set `W` with `|U| + 2|C| < |W|`, some `p ∈ W` is
unused and makes the edge `{p_u, p}` avoid every forbidden colour. (Each colour is realised by
exactly two edges through `p_u`, as the ND-colouring is a 2-factorization.) -/
lemma exists_fresh_position_in (n : ℕ) (hn : 0 < n) (p_u : Fin (2 * n + 1))
    (W U : Finset (Fin (2 * n + 1))) (hpu : p_u ∈ U) (C : Finset (Fin n))
    (hlt : U.card + 2 * C.card < W.card) :
    ∃ p ∈ W, p ∉ U ∧ ndColouring n hn s(p_u, p) ∉ C := by
  classical
  have hfiber : ∀ c : Fin n,
      (Finset.univ.filter (fun p => p ≠ p_u ∧ ndColouring n hn s(p_u, p) = c)).card ≤ 2 := by
    intro c
    have h2f := ndColouring_isTwoFactorization n hn p_u c
    have hinj : Set.InjOn (fun p => s(p_u, p))
        ↑(Finset.univ.filter (fun p => p ≠ p_u ∧ ndColouring n hn s(p_u, p) = c)) := by
      intro a ha b hb hab
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at ha hb
      rw [Sym2.eq_iff] at hab
      rcases hab with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · exact absurd h.symm hb.1
    have hsub : (Finset.univ.filter (fun p => p ≠ p_u ∧ ndColouring n hn s(p_u, p) = c)).image
          (fun p => s(p_u, p))
        ⊆ {e | p_u ∈ e ∧ ¬e.IsDiag ∧ ndColouring n hn e = c}.toFinset := by
      intro e he
      rw [Finset.mem_image] at he
      obtain ⟨p, hp, rfl⟩ := he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      rw [Set.mem_toFinset]
      exact ⟨Sym2.mem_mk_left _ _,
        by simp only [Sym2.mk_isDiag_iff]; exact fun h => hp.1 h.symm, hp.2⟩
    calc (Finset.univ.filter (fun p => p ≠ p_u ∧ ndColouring n hn s(p_u, p) = c)).card
        = ((Finset.univ.filter (fun p => p ≠ p_u ∧ ndColouring n hn s(p_u, p) = c)).image
            (fun p => s(p_u, p))).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ {e | p_u ∈ e ∧ ¬e.IsDiag ∧ ndColouring n hn e = c}.toFinset.card :=
          Finset.card_le_card hsub
      _ = 2 := by rw [← Set.ncard_eq_toFinset_card', h2f]
  set Bad : Finset (Fin (2 * n + 1)) :=
    Finset.univ.filter (fun p => p ≠ p_u ∧ ndColouring n hn s(p_u, p) ∈ C) with hBad
  have hBadcard : Bad.card ≤ 2 * C.card := by
    have hsub : Bad ⊆ C.biUnion (fun c =>
        Finset.univ.filter (fun p => p ≠ p_u ∧ ndColouring n hn s(p_u, p) = c)) := by
      intro p hp
      simp only [hBad, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      rw [Finset.mem_biUnion]
      exact ⟨_, hp.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.1, rfl⟩⟩
    refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_biUnion_le ?_)
    refine le_trans (Finset.sum_le_sum (fun c _ => hfiber c)) ?_
    rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hcard : (U ∪ Bad).card < W.card := by
    have h1 := Finset.card_union_le U Bad
    omega
  obtain ⟨p, hpW, hp⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  rw [Finset.mem_union, not_or] at hp
  refine ⟨p, hpW, hp.1, fun hc => hp.2 ?_⟩
  simp only [hBad, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => hp.1 (by rw [h]; exact hpu), hc⟩

/-- **Interval-restricted pinned greedy rainbow embedding.** Builds a rainbow embedding of an
acyclic graph `T'` restricted to a vertex finset `S ∋ v₁`, with every image inside a prescribed
position set `W` and `v₁` pinned to a prescribed position `a ∈ W`. Requires the counting slack
`3|S| ≤ |W| + 4`: at each greedy step at most `|S| - 1` positions are occupied and at most
`|S| - 2` colours are used, which (by 2-factorization) forbid fewer than `|W|` positions of `W`.
Strong induction on `S`, peeling a degree-`≤ 1` vertex of the induced forest distinct from `v₁`. -/
lemma greedy_embed_interval (n : ℕ) (hn : 0 < n) {V : Type*} [Fintype V] [DecidableEq V]
    (T' : SimpleGraph V) [DecidableRel T'.Adj] (hac : T'.IsAcyclic)
    (W : Finset (Fin (2 * n + 1))) (a : Fin (2 * n + 1)) (haW : a ∈ W) (v1 : V) :
    ∀ S : Finset V, v1 ∈ S → 3 * S.card ≤ W.card + 4 →
    ∃ g : V → Fin (2 * n + 1), g v1 = a ∧ Set.InjOn g ↑S ∧ (∀ v ∈ S, g v ∈ W) ∧
      Set.InjOn (ndColouring n hn) ↑((T'.edgeFinset ∩ S.sym2).image (Sym2.map g)) := by
  intro S
  induction S using Finset.strongInduction with
  | _ S ih =>
    intro hv1S hcount
    rcases Nat.lt_or_ge S.card 2 with hS1 | hS2
    · -- Base case: `S = {v1}`; the constant map `a` works.
      have hSeq : S = {v1} := by
        refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hv1S, fun y hy => ?_⟩
        by_contra hne
        have : 1 < S.card := Finset.one_lt_card.mpr ⟨y, hy, v1, hv1S, hne⟩
        omega
      subst hSeq
      refine ⟨fun _ => a, rfl, ?_, fun v _ => haW, ?_⟩
      · intro u hu v hv _
        rw [Finset.mem_coe, Finset.mem_singleton] at hu hv
        rw [hu, hv]
      · have hempty : T'.edgeFinset ∩ ({v1} : Finset V).sym2 = ∅ := by
          ext e
          induction e using Sym2.ind with
          | _ x y =>
            simp only [Finset.mem_inter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
              Finset.mk_mem_sym2_iff, Finset.mem_singleton, Finset.notMem_empty, iff_false]
            rintro ⟨hadj, rfl, rfl⟩
            exact hadj.ne rfl
        rw [hempty, Finset.image_empty, Finset.coe_empty]
        exact Set.injOn_empty _
    · -- Inductive step: peel a degree-`≤ 1` vertex `w ≠ v1` of the induced forest.
      haveI : DecidableRel (T'.induce (S : Set V)).Adj :=
        fun u v => inferInstanceAs (Decidable (T'.Adj ↑u ↑v))
      have hcardS : Fintype.card (S : Set V) = S.card := by
        rw [Fintype.card_congr (Equiv.subtypeEquivRight (fun x => Finset.mem_coe))]
        exact Fintype.card_coe S
      obtain ⟨w0, hw0ne, hw0deg⟩ := exists_degree_le_one_ne (T'.induce (S : Set V))
        (hac.induce _) ⟨v1, Finset.mem_coe.mpr hv1S⟩ (by omega)
      set w : V := (w0 : V) with hwdef
      have hwS : w ∈ S := Finset.mem_coe.mp w0.2
      have hwv1 : w ≠ v1 := fun h => hw0ne (Subtype.ext h)
      have hdeg : (S.filter (fun u => T'.Adj w u)).card ≤ 1 := by
        have himg : ((T'.induce (S : Set V)).neighborFinset w0).image Subtype.val
            = S.filter (fun u => T'.Adj w u) := by
          ext u
          simp only [Finset.mem_image, SimpleGraph.mem_neighborFinset, Finset.mem_filter]
          constructor
          · rintro ⟨w', hw', rfl⟩
            exact ⟨Finset.mem_coe.mp w'.2, hw'⟩
          · rintro ⟨huS, hadj⟩
            exact ⟨⟨u, Finset.mem_coe.mpr huS⟩, hadj, rfl⟩
        rw [← himg, Finset.card_image_of_injOn (Set.injOn_of_injective Subtype.val_injective),
          SimpleGraph.card_neighborFinset_eq_degree]
        exact hw0deg
      have hv1erase : v1 ∈ S.erase w := Finset.mem_erase.mpr ⟨Ne.symm hwv1, hv1S⟩
      obtain ⟨g', hg'v1, hg'inj, hg'W, hg'rb⟩ := ih (S.erase w) (Finset.erase_ssubset hwS)
        hv1erase (by have := Finset.card_erase_of_mem hwS; omega)
      have hNbeq : (S.erase w).filter (fun u => T'.Adj w u)
          = S.filter (fun u => T'.Adj w u) := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨⟨_, hu⟩, hadj⟩; exact ⟨hu, hadj⟩
        · rintro ⟨hu, hadj⟩
          exact ⟨⟨hadj.ne', hu⟩, hadj⟩
      set Nb := (S.erase w).filter (fun u => T'.Adj w u) with hNbdef
      have hNbcard : Nb.card ≤ 1 := by rw [hNbeq]; exact hdeg
      set U : Finset (Fin (2 * n + 1)) := (S.erase w).image g' with hUdef
      set Cset : Finset (Fin n) :=
        ((T'.edgeFinset ∩ (S.erase w).sym2).image (Sym2.map g')).image (ndColouring n hn)
        with hCdef
      have hUcard : U.card ≤ S.card - 1 := by
        calc U.card ≤ (S.erase w).card := Finset.card_image_le
          _ = S.card - 1 := by rw [Finset.card_erase_of_mem hwS]
      have herasene : (S.erase w).Nonempty := ⟨v1, hv1erase⟩
      have hCcard : Cset.card + 2 ≤ S.card := by
        have hedge := card_edges_in_subset_lt T' hac (S.erase w) herasene
        have h1 : Cset.card ≤ (T'.edgeFinset ∩ (S.erase w).sym2).card :=
          le_trans Finset.card_image_le Finset.card_image_le
        have h2 : (S.erase w).card = S.card - 1 := Finset.card_erase_of_mem hwS
        omega
      -- Off-`w` agreement: updating `g'` at `w` changes neither injectivity nor old colours.
      have hInjOnOf : ∀ p : Fin (2 * n + 1), p ∉ U →
          Set.InjOn (Function.update g' w p) ↑S := by
        intro p hp x hx y hy hxy
        rcases eq_or_ne x w with rfl | hxw
        · rcases eq_or_ne y w with rfl | hyw
          · rfl
          · rw [Function.update_self, Function.update_of_ne hyw] at hxy
            exact absurd (hxy ▸ Finset.mem_image.mpr
              ⟨y, Finset.mem_erase.mpr ⟨hyw, Finset.mem_coe.mp hy⟩, rfl⟩) hp
        · rcases eq_or_ne y w with rfl | hyw
          · rw [Function.update_of_ne hxw, Function.update_self] at hxy
            exact absurd (hxy.symm ▸ Finset.mem_image.mpr
              ⟨x, Finset.mem_erase.mpr ⟨hxw, Finset.mem_coe.mp hx⟩, rfl⟩) hp
          · rw [Function.update_of_ne hxw, Function.update_of_ne hyw] at hxy
            exact hg'inj (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hxw, Finset.mem_coe.mp hx⟩))
              (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hyw, Finset.mem_coe.mp hy⟩)) hxy
      have hmapeq : ∀ p : Fin (2 * n + 1), ∀ e ∈ T'.edgeFinset ∩ (S.erase w).sym2,
          Sym2.map (Function.update g' w p) e = Sym2.map g' e := by
        intro p e he
        rw [Finset.mem_inter] at he
        induction e using Sym2.ind with
        | _ x y =>
          have hxy := he.2
          rw [Finset.mk_mem_sym2_iff] at hxy
          have hxne : x ≠ w := (Finset.mem_erase.mp hxy.1).1
          have hyne : y ≠ w := (Finset.mem_erase.mp hxy.2).1
          simp only [Sym2.map_mk, Prod.map_apply, Function.update_of_ne hxne,
            Function.update_of_ne hyne]
      rcases Finset.eq_empty_or_nonempty Nb with hNe | hNe
      · -- No new core edge: place `w` at any unused position of `W`.
        have hUlt : U.card < W.card := by omega
        obtain ⟨p, hpW, hpU⟩ := Finset.exists_mem_notMem_of_card_lt_card hUlt
        refine ⟨Function.update g' w p, ?_, hInjOnOf p hpU, ?_, ?_⟩
        · rw [Function.update_of_ne (Ne.symm hwv1)]
          exact hg'v1
        · intro v hv
          rcases eq_or_ne v w with rfl | hvw
          · rw [Function.update_self]; exact hpW
          · rw [Function.update_of_ne hvw]
            exact hg'W v (Finset.mem_erase.mpr ⟨hvw, hv⟩)
        · have hseteq : T'.edgeFinset ∩ S.sym2 = T'.edgeFinset ∩ (S.erase w).sym2 := by
            ext e
            induction e using Sym2.ind with
            | _ x y =>
              simp only [Finset.mem_inter, SimpleGraph.mem_edgeFinset, Finset.mk_mem_sym2_iff,
                Finset.mem_erase]
              constructor
              · rintro ⟨hadj, hxS, hyS⟩
                refine ⟨hadj, ⟨?_, hxS⟩, ⟨?_, hyS⟩⟩
                · rintro rfl
                  have hyNb : y ∈ Nb := Finset.mem_filter.mpr
                    ⟨Finset.mem_erase.mpr ⟨hadj.ne', hyS⟩, hadj⟩
                  simp [hNe] at hyNb
                · rintro rfl
                  have hxNb : x ∈ Nb := Finset.mem_filter.mpr
                    ⟨Finset.mem_erase.mpr ⟨hadj.ne, hxS⟩, hadj.symm⟩
                  simp [hNe] at hxNb
              · rintro ⟨hadj, ⟨_, hxS⟩, ⟨_, hyS⟩⟩
                exact ⟨hadj, hxS, hyS⟩
          rw [hseteq, Finset.image_congr (hmapeq p)]
          exact hg'rb
      · -- One new core edge `s(w, u)`: use a fresh position of `W`.
        obtain ⟨u, hu⟩ := hNe
        have huNb := hu
        rw [hNbdef, Finset.mem_filter] at huNb
        obtain ⟨huSe, hadjwu⟩ := huNb
        have hpuU : g' u ∈ U := Finset.mem_image.mpr ⟨u, huSe, rfl⟩
        have hlt : U.card + 2 * Cset.card < W.card := by omega
        obtain ⟨p, hpW, hpU, hpC⟩ := exists_fresh_position_in n hn (g' u) W U hpuU Cset hlt
        refine ⟨Function.update g' w p, ?_, hInjOnOf p hpU, ?_, ?_⟩
        · rw [Function.update_of_ne (Ne.symm hwv1)]
          exact hg'v1
        · intro v hv
          rcases eq_or_ne v w with rfl | hvw
          · rw [Function.update_self]; exact hpW
          · rw [Function.update_of_ne hvw]
            exact hg'W v (Finset.mem_erase.mpr ⟨hvw, hv⟩)
        · -- The placed edge set gains exactly `s(w, u)`.
          have hseteq : T'.edgeFinset ∩ S.sym2
              = insert s(w, u) (T'.edgeFinset ∩ (S.erase w).sym2) := by
            ext e
            induction e using Sym2.ind with
            | _ x y =>
              simp only [Finset.mem_inter, SimpleGraph.mem_edgeFinset, Finset.mk_mem_sym2_iff,
                Finset.mem_insert, Finset.mem_erase, Sym2.eq_iff]
              constructor
              · rintro ⟨hadj, hxS, hyS⟩
                by_cases hxw : x = w
                · subst hxw
                  have hyu : y = u := by
                    have hy_nb : y ∈ Nb := Finset.mem_filter.mpr
                      ⟨Finset.mem_erase.mpr ⟨hadj.ne', hyS⟩, hadj⟩
                    exact Finset.card_le_one.mp hNbcard y hy_nb u hu
                  exact Or.inl (Or.inl ⟨rfl, hyu⟩)
                · by_cases hyw : y = w
                  · subst hyw
                    have hxu : x = u := by
                      have hx_nb : x ∈ Nb := Finset.mem_filter.mpr
                        ⟨Finset.mem_erase.mpr ⟨hadj.ne, hxS⟩, hadj.symm⟩
                      exact Finset.card_le_one.mp hNbcard x hx_nb u hu
                    exact Or.inl (Or.inr ⟨hxu, rfl⟩)
                  · exact Or.inr ⟨hadj, ⟨hxw, hxS⟩, ⟨hyw, hyS⟩⟩
              · rintro ((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨hadj, ⟨_, hxS⟩, ⟨_, hyS⟩⟩)
                · exact ⟨hadjwu, hwS, Finset.mem_of_mem_erase huSe⟩
                · exact ⟨hadjwu.symm, Finset.mem_of_mem_erase huSe, hwS⟩
                · exact ⟨hadj, hxS, hyS⟩
          rw [hseteq, Finset.image_insert]
          have hnew : Sym2.map (Function.update g' w p) s(w, u) = s(p, g' u) := by
            have hune : u ≠ w := (Finset.mem_erase.mp huSe).1
            simp only [Sym2.map_mk, Prod.map_apply, Function.update_self,
              Function.update_of_ne hune]
          rw [hnew, Finset.image_congr (hmapeq p), Finset.coe_insert]
          refine (Set.injOn_insert ?_).mpr ⟨hg'rb, ?_⟩
          · -- `s(p, g' u)` is not among the old placed edges.
            intro hmem
            rw [Finset.mem_coe, Finset.mem_image] at hmem
            obtain ⟨e, heX, hee⟩ := hmem
            apply hpC
            rw [hCdef, Sym2.eq_swap, ← hee]
            exact Finset.mem_image.mpr ⟨Sym2.map g' e, Finset.mem_image.mpr ⟨e, heX, rfl⟩, rfl⟩
          · -- The fresh colour avoids every old colour.
            rintro ⟨x, hx, hcx⟩
            rw [Finset.mem_coe, Finset.mem_image] at hx
            obtain ⟨e, heX, hee⟩ := hx
            apply hpC
            rw [hCdef, Sym2.eq_swap, ← hcx, ← hee]
            exact Finset.mem_image.mpr ⟨Sym2.map g' e, Finset.mem_image.mpr ⟨e, heX, rfl⟩, rfl⟩

/-- **One large vertex (Theorem `Theorem_one_large_vertex`, §2).** If an `(n+1)`-vertex tree `T`
has a vertex `v₁` adjacent to at least `2n/3` leaves, then the ND-coloured `K_{2n+1}` contains a
rainbow copy of `T`. The core `T'` (obtained by isolating the leaf-neighbours of `v₁`) has at most
`n/3 + 1` vertices and embeds greedily rainbow into the interval `[0, n]` with `v₁` at `0`; each
removed leaf is then attached at `2n - c ∈ [n+1, 2n]` for a fresh colour `c`, realizing the colour
`c` on the new edge since `2n - c ≡ -(c+1) mod (2n+1)`. -/
theorem one_large_vertex (n : ℕ) (hn : 0 < n) {V : Type*} [Finite V]
    (T : SimpleGraph V) (hT : T.IsTree) (hcard : T.edgeSet.ncard = n)
    (v1 : V) (hbig : 2 * n / 3 ≤ {w : V | T.Adj v1 w ∧ IsLeaf T w}.ncard) :
    HasRainbowCopy n T := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  have hVcard : Fintype.card V = n + 1 := by
    have hc := hT.card_edgeFinset
    have he : T.edgeFinset.card = n := by
      rw [← hcard]; exact (Set.ncard_eq_toFinset_card' T.edgeSet).symm
    omega
  -- The leaf-neighbours of `v1`.
  set L : Finset V := Finset.univ.filter (fun w => T.Adj v1 w ∧ IsLeaf T w) with hLdef
  have hD : 2 * n / 3 ≤ L.card := by
    have hLcard : {w : V | T.Adj v1 w ∧ IsLeaf T w}.ncard = L.card := by
      rw [Set.ncard_eq_toFinset_card', Set.toFinset_setOf]
    exact hLcard ▸ hbig
  have hv1L : v1 ∉ L := by
    simp only [hLdef, Finset.mem_filter, Finset.mem_univ, true_and]
    rintro ⟨hadj, _⟩
    exact hadj.ne rfl
  -- Each leaf in `L` has `v1` as its unique neighbour.
  have hLnbr : ∀ w ∈ L, ∀ x, T.Adj w x → x = v1 := by
    intro w hw x hx
    simp only [hLdef, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    obtain ⟨hadj, y, _, huniq⟩ := hw
    rw [huniq x hx, ← huniq v1 hadj.symm]
  -- The core: `T` with the leaves of `L` isolated.
  set T' : SimpleGraph V :=
    { Adj := fun x y => T.Adj x y ∧ x ∉ L ∧ y ∉ L,
      symm := fun x y h => ⟨h.1.symm, h.2.2, h.2.1⟩,
      loopless := ⟨fun _ h => T.irrefl h.1⟩ } with hT'def
  have hT'adj : ∀ x y, T'.Adj x y ↔ (T.Adj x y ∧ x ∉ L ∧ y ∉ L) := by
    intro x y; rw [hT'def]
  have hT'le : T' ≤ T := fun x y h => ((hT'adj x y).mp h).1
  have hac : T'.IsAcyclic := hT.IsAcyclic.anti hT'le
  -- The core vertex set.
  set S : Finset V := Finset.univ.filter (fun v => v ∉ L) with hSdef
  have hv1S : v1 ∈ S := by
    simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hv1L
  -- Edge partition: core edges and the `v1`-leaf edges.
  have hedge_partition : T.edgeFinset = T'.edgeFinset ∪ L.image (fun w => s(v1, w)) := by
    ext e
    induction e using Sym2.ind with
    | _ x y =>
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Finset.mem_union,
        Finset.mem_image]
      constructor
      · intro hadj
        by_cases hxL : x ∈ L
        · exact Or.inr ⟨x, hxL, (hLnbr x hxL y hadj) ▸ Sym2.eq_swap⟩
        · by_cases hyL : y ∈ L
          · exact Or.inr ⟨y, hyL, (hLnbr y hyL x hadj.symm) ▸ rfl⟩
          · exact Or.inl ((hT'adj x y).mpr ⟨hadj, hxL, hyL⟩)
      · rintro (h | ⟨w, hwL, hew⟩)
        · exact hT'le h
        · have hadj : T.Adj v1 w := by
            simp only [hLdef, Finset.mem_filter, Finset.mem_univ, true_and] at hwL
            exact hwL.1
          rcases Sym2.eq_iff.mp hew with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [← h1, ← h2]; exact hadj
          · rw [← h1, ← h2]; exact hadj.symm
  have hdisj : Disjoint T'.edgeFinset (L.image (fun w => s(v1, w))) := by
    rw [Finset.disjoint_right]
    intro e he hmem
    rw [Finset.mem_image] at he
    obtain ⟨w, hwL, rfl⟩ := he
    have : T'.Adj v1 w := by
      rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hmem
    exact ((hT'adj v1 w).mp this).2.2 hwL
  have hLimg_card : (L.image (fun w => s(v1, w))).card = L.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    rcases Sym2.eq_iff.mp hxy with ⟨_, h⟩ | ⟨hy1, hx1⟩
    · exact h
    · exact absurd (hx1 ▸ hx) hv1L
  have hecard : T.edgeFinset.card = n := by
    rw [← hcard]; exact (Set.ncard_eq_toFinset_card' T.edgeSet).symm
  have hcore_card : T'.edgeFinset.card + L.card = n := by
    rw [← hecard, hedge_partition, Finset.card_union_of_disjoint hdisj, hLimg_card]
  -- The target interval `[0, n]` and the counting slack.
  set W : Finset (Fin (2 * n + 1)) := Finset.univ.filter (fun p => p.val ≤ n) with hWdef
  have hWcard : W.card = n + 1 := by
    have hattach : W = (Finset.range (n + 1)).attachFin
        (fun m hm => by rw [Finset.mem_range] at hm; omega) := by
      ext p
      simp only [hWdef, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_attachFin,
        Finset.mem_range]
      omega
    rw [hattach, Finset.card_attachFin, Finset.card_range]
  have hScard : S.card + L.card = n + 1 := by
    have hSc : S = Lᶜ := by
      ext v
      simp [hSdef, Finset.mem_compl]
    have hLle : L.card ≤ n + 1 := by rw [← hVcard]; exact Finset.card_le_univ L
    rw [hSc, Finset.card_compl, hVcard]
    omega
  have hcount : 3 * S.card ≤ W.card + 4 := by
    rw [hWcard]
    omega
  -- Greedy rainbow embedding of the core into `[0, n]` with `v1 ↦ 0`.
  have h0W : (0 : Fin (2 * n + 1)) ∈ W := by
    simp only [hWdef, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_zero]
    omega
  obtain ⟨g, hgv1, hginj, hgW, hgrb⟩ := greedy_embed_interval n hn T' hac W
    0 h0W v1 S hv1S hcount
  -- Core edges live inside `S`, so the greedy conclusion covers all of them.
  have hT'S : T'.edgeFinset ∩ S.sym2 = T'.edgeFinset := by
    rw [Finset.inter_eq_left]
    intro e he
    rw [Finset.mem_sym2_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.mp hx
    have hadj : T'.Adj x y := by
      rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ((hT'adj x y).mp hadj).2.1
  rw [hT'S] at hgrb
  -- Colours used by the core, and fresh colours for the leaves.
  set usedC : Finset (Fin n) := (T'.edgeFinset.image (Sym2.map g)).image (ndColouring n hn)
    with husedCdef
  have husedC_le : usedC.card ≤ T'.edgeFinset.card :=
    le_trans Finset.card_image_le Finset.card_image_le
  have hLle_unused : L.card ≤ (Finset.univ \ usedC).card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨tC, htCsub, htCcard⟩ := Finset.exists_subset_card_eq hLle_unused
  have heqv : L.card = tC.card := htCcard.symm
  set eqv : ↥L ≃ ↥tC := Finset.equivOfCardEq heqv with heqvdef
  -- The leaf attachment positions.
  set attachPos : Fin n → Fin (2 * n + 1) := fun c => ⟨2 * n - c.val, by omega⟩
    with hattachdef
  -- The full vertex map.
  set f : V → Fin (2 * n + 1) :=
    fun v => if h : v ∈ L then attachPos ↑(eqv ⟨v, h⟩) else g v with hfdef
  have hfL : ∀ (w : V) (hw : w ∈ L), f w = attachPos ↑(eqv ⟨w, hw⟩) := by
    intro w hw
    simp only [hfdef]
    rw [dif_pos hw]
  have hfS : ∀ w ∉ L, f w = g w := by
    intro w hw
    simp only [hfdef]
    rw [dif_neg hw]
  have hmemS : ∀ w ∉ L, w ∈ S := by
    intro w hw
    simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hw
  have hgle : ∀ w ∉ L, (g w).val ≤ n := by
    intro w hw
    have := hgW w (hmemS w hw)
    simpa only [hWdef, Finset.mem_filter, Finset.mem_univ, true_and] using this
  have hattach_ge : ∀ c : Fin n, n + 1 ≤ (attachPos c).val := by
    intro c
    have := c.isLt
    simp only [hattachdef]
    omega
  -- `f` is injective.
  have hfinj : Function.Injective f := by
    intro x y hxy
    by_cases hx : x ∈ L <;> by_cases hy : y ∈ L
    · rw [hfL x hx, hfL y hy] at hxy
      have hc : (↑(eqv ⟨x, hx⟩) : Fin n) = ↑(eqv ⟨y, hy⟩) := by
        have hval := congrArg Fin.val hxy
        simp only [hattachdef] at hval
        have h1 := (↑(eqv ⟨x, hx⟩) : Fin n).isLt
        have h2 := (↑(eqv ⟨y, hy⟩) : Fin n).isLt
        exact Fin.ext (by omega)
      have := eqv.injective (Subtype.ext hc)
      exact congrArg Subtype.val this
    · rw [hfL x hx, hfS y hy] at hxy
      have h1 := hattach_ge ↑(eqv ⟨x, hx⟩)
      have h2 := hgle y hy
      rw [hxy] at h1
      omega
    · rw [hfS x hx, hfL y hy] at hxy
      have h1 := hattach_ge ↑(eqv ⟨y, hy⟩)
      have h2 := hgle x hx
      rw [← hxy] at h1
      omega
    · rw [hfS x hx, hfS y hy] at hxy
      exact hginj (Finset.mem_coe.mpr (hmemS x hx)) (Finset.mem_coe.mpr (hmemS y hy)) hxy
  -- On core edges, `f` agrees with `g`.
  have hfg : ∀ d ∈ T'.edgeFinset, Sym2.map f d = Sym2.map g d := by
    intro d hd
    induction d using Sym2.ind with
    | _ a b =>
      have hadj : T'.Adj a b := by
        rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hd
      obtain ⟨_, haL, hbL⟩ := (hT'adj a b).mp hadj
      rw [Sym2.map_mk, Sym2.map_mk, Prod.map_apply, Prod.map_apply, hfS a haL, hfS b hbL]
  -- Colour of a leaf edge.
  have hleafcol : ∀ (w : V) (hw : w ∈ L),
      ndColouring n hn (Sym2.map f s(v1, w)) = ↑(eqv ⟨w, hw⟩) := by
    intro w hw
    have hfv1 : f v1 = 0 := by rw [hfS v1 hv1L]; exact hgv1
    rw [Sym2.map_mk, Prod.map_apply, hfv1, hfL w hw]
    have hzero : s((0 : Fin (2 * n + 1)), attachPos ↑(eqv ⟨w, hw⟩))
        = s((0 : Fin (2 * n + 1)), 0 + attachPos ↑(eqv ⟨w, hw⟩)) := by rw [zero_add]
    rw [hzero]
    refine ndColouring_step n hn 0 _ _ (Or.inr ?_)
    have := (↑(eqv ⟨w, hw⟩) : Fin n).isLt
    simp only [hattachdef]
    omega
  -- Colour of a core edge lies in `usedC`.
  have hcorecol : ∀ d ∈ T'.edgeFinset, ndColouring n hn (Sym2.map f d) ∈ usedC := by
    intro d hd
    rw [hfg d hd]
    exact Finset.mem_image.mpr ⟨Sym2.map g d, Finset.mem_image.mpr ⟨d, hd, rfl⟩, rfl⟩
  -- Leaf colours avoid `usedC`.
  have hleaf_fresh : ∀ (w : V) (hw : w ∈ L), (↑(eqv ⟨w, hw⟩) : Fin n) ∉ usedC := by
    intro w hw
    have := htCsub (eqv ⟨w, hw⟩).2
    exact (Finset.mem_sdiff.mp this).2
  -- Classification of `T`-edges.
  have hclassify : ∀ d ∈ T.edgeSet, d ∈ T'.edgeFinset ∨ ∃ w, ∃ hw : w ∈ L, d = s(v1, w) := by
    intro d hd
    have hmem : d ∈ T.edgeFinset := SimpleGraph.mem_edgeFinset.mpr hd
    rw [hedge_partition, Finset.mem_union] at hmem
    rcases hmem with h | h
    · exact Or.inl h
    · rw [Finset.mem_image] at h
      obtain ⟨w, hw, rfl⟩ := h
      exact Or.inr ⟨w, hw, rfl⟩
  -- The full map is rainbow on `T`.
  set femb : V ↪ Fin (2 * n + 1) := ⟨f, hfinj⟩ with hfembdef
  have hrainbow : Set.InjOn (ndColouring n hn) ((T.map femb).edgeSet) := by
    rw [SimpleGraph.edgeSet_map]
    intro E1 hE1 E2 hE2 hcol
    obtain ⟨d1, hd1, rfl⟩ := hE1
    obtain ⟨d2, hd2, rfl⟩ := hE2
    simp only [Function.Embedding.sym2Map_apply, hfembdef, Function.Embedding.coeFn_mk]
      at hcol ⊢
    rcases hclassify d1 hd1 with h1 | ⟨w1, hw1, rfl⟩ <;>
      rcases hclassify d2 hd2 with h2 | ⟨w2, hw2, rfl⟩
    · -- both core edges: greedy rainbow
      rw [hfg d1 h1, hfg d2 h2] at hcol ⊢
      exact hgrb (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨d1, h1, rfl⟩))
        (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨d2, h2, rfl⟩)) hcol
    · -- core vs leaf: colours live in disjoint sets
      exfalso
      rw [hleafcol w2 hw2] at hcol
      exact hleaf_fresh w2 hw2 (hcol ▸ hcorecol d1 h1)
    · -- leaf vs core
      exfalso
      rw [hleafcol w1 hw1] at hcol
      exact hleaf_fresh w1 hw1 (hcol.symm ▸ hcorecol d2 h2)
    · -- both leaf edges: the assigned colours are distinct
      rw [hleafcol w1 hw1, hleafcol w2 hw2] at hcol
      have hww : w1 = w2 := by
        have := eqv.injective (Subtype.ext hcol)
        exact congrArg Subtype.val this
      subst hww
      rfl
  exact ⟨femb, fun _ => hrainbow⟩

end Ringel
