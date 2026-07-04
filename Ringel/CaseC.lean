import Ringel.Statement
import Ringel.Primitives
import Ringel.TreeStructure
import Mathlib.Data.Set.Card.Arithmetic

namespace Ringel

/-!
## Case C: caterpillar decomposition (MPS §6–§7)

A tree $T$ is **Case C** if, after removing all leaves adjacent to vertices of
high leaf-degree ($\geq \lfloor\delta^{-4}\rfloor$ leaf-neighbours), the remaining
graph has $\leq n/100$ vertices. The proof decomposes $T$ into a small "core" and
a collection of leaves, embeds the core rainbow in the ND-coloured $K_{2n+1}$, then
absorbs the leaves.
-/

open SimpleGraph in
/-- A finite acyclic graph (forest) with at least one edge has a *leaf*: a vertex $v$
with a unique neighbour $u$. We obtain it from the tree structure of the connected
component containing an edge, which has a degree-one vertex. -/
lemma exists_leaf_of_acyclic {V : Type*} [Finite V] (G : SimpleGraph V) (hG : G.IsAcyclic)
    (he : G.edgeSet.Nonempty) : ∃ u v : V, G.Adj v u ∧ ∀ w, G.Adj v w → w = u := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  obtain ⟨e, he⟩ := he
  induction e using Sym2.ind with
  | _ a b =>
  rw [SimpleGraph.mem_edgeSet] at he
  set C := G.connectedComponentMk a with hC
  have haC : a ∈ C.supp := by simp [hC, ConnectedComponent.mem_supp_iff]
  have hbC : b ∈ C.supp := by
    simp only [hC, ConnectedComponent.mem_supp_iff]
    exact (ConnectedComponent.connectedComponentMk_eq_of_adj he.symm)
  haveI : Fintype C.supp := Fintype.ofFinite _
  have hTree : C.toSimpleGraph.IsTree := hG.isTree_connectedComponent C
  haveI : Nontrivial C := by
    refine ⟨⟨a, haC⟩, ⟨b, hbC⟩, ?_⟩
    simp only [ne_eq, Subtype.mk.injEq]
    exact he.ne
  obtain ⟨⟨v, hv⟩, hdeg⟩ := hTree.exists_vert_degree_one_of_nontrivial
  rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj] at hdeg
  obtain ⟨⟨u, hu⟩, hadj, huniq⟩ := hdeg
  have hvC : G.connectedComponentMk v = C := by
    simpa [ConnectedComponent.mem_supp_iff] using hv
  refine ⟨u, v, ?_, ?_⟩
  · rw [← C.toSimpleGraph_adj hv hu]; exact hadj
  · intro w hw
    have hwC : w ∈ C.supp := by
      have : G.connectedComponentMk w = C := by
        rw [← hvC, ConnectedComponent.eq]; exact hw.symm.reachable
      simpa [ConnectedComponent.mem_supp_iff] using this
    have := huniq ⟨w, hwC⟩ ((C.toSimpleGraph_adj hv hwC).mpr hw)
    exact congrArg Subtype.val this

/-- In a finite acyclic graph (forest), the number of edges is at most the number of
non-isolated vertices: each component is a tree with $|E_c| = |V_c| - 1 \leq |V_c|$, and
summing over components gives $|E| = |V_\text{supp}| - \#\text{components} \leq |V_\text{supp}|$. -/
lemma acyclic_ncard_edgeSet_le_ncard_support {V : Type*} [Finite V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) : G.edgeSet.ncard ≤ G.support.ncard := by
  -- Strong induction on the number of edges: delete a leaf edge and recurse.
  suffices H : ∀ n (G : SimpleGraph V), G.IsAcyclic → G.edgeSet.ncard = n →
      G.edgeSet.ncard ≤ G.support.ncard by
    exact H _ G hG rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G hG hn
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; rw [hn]; positivity
    · have hne : G.edgeSet.Nonempty :=
        (Set.ncard_pos (Set.toFinite _)).mp (by omega)
      obtain ⟨u, v, hadj, huniq⟩ := exists_leaf_of_acyclic G hG hne
      set G' := G.deleteEdges {s(v, u)} with hG'
      have hle : G' ≤ G := SimpleGraph.deleteEdges_le _
      have hG'ac : G'.IsAcyclic := hG.anti hle
      have hmem : s(v, u) ∈ G.edgeSet := by rw [SimpleGraph.mem_edgeSet]; exact hadj
      have hedge' : G'.edgeSet = G.edgeSet \ {s(v, u)} := by
        rw [hG', SimpleGraph.edgeSet_deleteEdges]
      have hcard' : G'.edgeSet.ncard = n - 1 := by
        rw [hedge', Set.ncard_diff_singleton_of_mem hmem, hn]
      have hvnot : v ∉ G'.support := by
        rw [SimpleGraph.mem_support]
        rintro ⟨w, hw⟩
        rw [hG', SimpleGraph.deleteEdges_adj] at hw
        obtain ⟨hadjw, hne'⟩ := hw
        have : w = u := huniq w hadjw
        subst this
        exact hne' (by simp)
      have hvin : v ∈ G.support := hadj.mem_support_left
      have hsub : G'.support ⊆ G.support := SimpleGraph.support_mono hle
      have hsub2 : G'.support ⊆ G.support \ {v} := by
        intro x hx
        exact ⟨hsub hx, fun hxv => hvnot (hxv ▸ hx)⟩
      have hsfin : G.support.Finite := Set.toFinite _
      have hcard_le : G'.support.ncard ≤ (G.support \ {v}).ncard :=
        Set.ncard_le_ncard hsub2 (hsfin.diff)
      have hdiff : (G.support \ {v}).ncard = G.support.ncard - 1 :=
        Set.ncard_diff_singleton_of_mem hvin
      have hIH : G'.edgeSet.ncard ≤ G'.support.ncard :=
        ih (n - 1) (by omega) G' hG'ac hcard'
      have hsupp_pos : 1 ≤ G.support.ncard := (Set.ncard_pos hsfin).mpr ⟨v, hvin⟩
      omega

/-- **Structural decomposition.** A Case C tree decomposes into a core subgraph
(on the non-removed vertices) and a leaf set. The core has $\leq n/100$ edges
because the acyclic restriction to $\leq n/100$ vertices has $\leq n/100$ edges. -/
lemma caseC_decompose (δ : ℝ) (n : ℕ) {V : Type*} [Finite V] (T : SimpleGraph V)
    (hT : T.IsTree) (hC : IsCaseC δ n T) :
    ∃ (T_core : SimpleGraph V) (leaves : Set V),
      T_core ≤ T ∧
      (∀ v ∈ leaves, IsLeaf T v) ∧
      (T_core.edgeSet.ncard ≤ n / 100) ∧
      (T_core.edgeSet ∪ {e ∈ T.edgeSet | ∃ v ∈ leaves, v ∈ e}) = T.edgeSet := by
  simp only [IsCaseC] at hC
  set highLeafDeg : Set V :=
    {v | ⌊(δ : ℝ)⁻¹ ^ 4⌋₊ ≤ {w | T.Adj v w ∧ IsLeaf T w}.ncard}
  set removedLeaves : Set V :=
    {v | IsLeaf T v ∧ ∃ w, T.Adj v w ∧ w ∈ highLeafDeg}
  -- Define core as the restriction of T away from removedLeaves
  let T_core : SimpleGraph V := {
    Adj := fun u v => T.Adj u v ∧ u ∉ removedLeaves ∧ v ∉ removedLeaves
    symm := fun u v ⟨h, hu, hv⟩ => ⟨h.symm, hv, hu⟩
    loopless := ⟨fun v h => h.1.ne rfl⟩
  }
  refine ⟨T_core, removedLeaves, ?_, ?_, ?_, ?_⟩
  · -- T_core ≤ T
    intro u v h
    exact h.1
  · -- removedLeaves consists of leaves of T
    intro v ⟨hv_leaf, _⟩
    exact hv_leaf
  · -- T_core.edgeSet.ncard ≤ n / 100
    have hle : T_core ≤ T := fun u v h => h.1
    have hac : T_core.IsAcyclic := hT.isAcyclic.anti hle
    have hsupp : T_core.support ⊆ Set.univ \ removedLeaves := by
      intro v hv
      obtain ⟨w, hw⟩ := hv
      exact ⟨Set.mem_univ v, hw.2.1⟩
    calc T_core.edgeSet.ncard
        ≤ T_core.support.ncard := acyclic_ncard_edgeSet_le_ncard_support T_core hac
      _ ≤ (Set.univ \ removedLeaves).ncard := Set.ncard_le_ncard hsupp (Set.toFinite _)
      _ ≤ n / 100 := hC
  · -- Decomposition: T_core ∪ leaf-edges = T
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      simp only [Set.mem_union, Set.mem_setOf_eq, SimpleGraph.mem_edgeSet, T_core]
      constructor
      · rintro (⟨h, _, _⟩ | ⟨h, _, _, _⟩)
        · exact h
        · exact h
      · intro h
        by_cases hu : u ∈ removedLeaves
        · exact Or.inr ⟨h, u, hu, Sym2.mem_mk_left u v⟩
        · by_cases hv : v ∈ removedLeaves
          · exact Or.inr ⟨h, v, hv, Sym2.mem_mk_right u v⟩
          · exact Or.inl ⟨h, hu, hv⟩

/-- **Greedy counting step (Case C).** With a placed vertex at position `p_u`, a set `U ∋ p_u` of
used positions, and a set `C` of forbidden colours, if `|U| + 2|C| < 2n+1` then some unused position
`p` makes the edge `{p_u, p}` avoid every forbidden colour. (The `2|C|` is because `ndColouring` is a
2-factorization, so each colour is realised by exactly two edges through `p_u`.) The core counting
step of the greedy rainbow embedding of the Case C core. -/
lemma exists_fresh_position (n : ℕ) (hn : 0 < n) (p_u : Fin (2 * n + 1))
    (U : Finset (Fin (2 * n + 1))) (hpu : p_u ∈ U) (C : Finset (Fin n))
    (hlt : U.card + 2 * C.card < 2 * n + 1) :
    ∃ p, p ∉ U ∧ ndColouring n hn s(p_u, p) ∉ C := by
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
        by simp only [Sym2.isDiag_iff_proj_eq]; exact fun h => hp.1 h.symm, hp.2⟩
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
  have hcompl : ((U ∪ Bad)ᶜ).Nonempty := by
    rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin]
    have := Finset.card_union_le U Bad
    omega
  obtain ⟨p, hp⟩ := hcompl
  rw [Finset.mem_compl, Finset.mem_union, not_or] at hp
  refine ⟨p, hp.1, fun hc => hp.2 ?_⟩
  simp only [hBad, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => hp.1 (by rw [h]; exact hpu), hc⟩

/-- **Greedy core construction.** Builds a rainbow embedding of an acyclic `T_core` by
`Finset.strongInduction` on the embedded vertex set `S`: peel a degree-`≤1` vertex `w` of the
induced forest, embed `S.erase w`, then place `w` at a position making its (unique) new core edge
avoid every already-used colour (`exists_fresh_position`). The colour set has size `≤ n/100` (at most
one colour per core edge) and the position set size `≤ n`, so a fresh position always exists. -/
private lemma caseC_greedy (n : ℕ) (hn : 0 < n) {V : Type*} [Fintype V] [DecidableEq V]
    (hVcard : Fintype.card V = n + 1)
    (T_core : SimpleGraph V) [DecidableRel T_core.Adj] (hac : T_core.IsAcyclic)
    (hbound : T_core.edgeFinset.card ≤ n / 100) (S : Finset V) :
    ∃ g : V → Fin (2 * n + 1), Set.InjOn g ↑S ∧
      Set.InjOn (ndColouring n hn)
        ↑((T_core.edgeFinset ∩ S.sym2).image (Sym2.map g)) := by
  induction S using Finset.strongInduction with
  | _ S ih =>
    rcases S.eq_empty_or_nonempty with rfl | hSne
    · exact ⟨fun _ => ⟨0, by omega⟩, by simp, by simp⟩
    · haveI : Nonempty (S : Set V) := hSne.coe_sort
      obtain ⟨w0, hw0⟩ :=
        TreeStructure.exists_degree_le_one_of_acyclic (T_core.induce (S : Set V)) (hac.induce _)
      set w : V := (w0 : V) with hwdef
      have hwS : w ∈ S := Finset.mem_coe.mp w0.2
      -- The number of neighbours of `w` inside `S` is at most one.
      have hdeg : (S.filter (fun u => T_core.Adj w u)).card ≤ 1 := by
        have himg : ((T_core.induce (S : Set V)).neighborFinset w0).image Subtype.val
            = S.filter (fun u => T_core.Adj w u) := by
          ext u
          simp only [Finset.mem_image, SimpleGraph.mem_neighborFinset, Finset.mem_filter]
          constructor
          · rintro ⟨w', hw', rfl⟩
            exact ⟨Finset.mem_coe.mp w'.2, hw'⟩
          · rintro ⟨huS, hadj⟩
            exact ⟨⟨u, Finset.mem_coe.mpr huS⟩, hadj, rfl⟩
        rw [← himg, Finset.card_image_of_injOn (Set.injOn_of_injective Subtype.val_injective),
          SimpleGraph.card_neighborFinset_eq_degree]
        exact hw0
      obtain ⟨g', hg'inj, hg'rb⟩ := ih (S.erase w) (Finset.erase_ssubset hwS)
      -- Neighbours of `w` inside `S.erase w` coincide with neighbours inside `S`.
      have hNbeq : (S.erase w).filter (fun u => T_core.Adj w u)
          = S.filter (fun u => T_core.Adj w u) := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨⟨_, hu⟩, hadj⟩; exact ⟨hu, hadj⟩
        · rintro ⟨hu, hadj⟩
          exact ⟨⟨hadj.ne', hu⟩, hadj⟩
      set Nb := (S.erase w).filter (fun u => T_core.Adj w u) with hNbdef
      have hNbcard : Nb.card ≤ 1 := by rw [hNbeq]; exact hdeg
      set U : Finset (Fin (2 * n + 1)) := (S.erase w).image g' with hUdef
      set Cset : Finset (Fin n) :=
        ((T_core.edgeFinset ∩ (S.erase w).sym2).image (Sym2.map g')).image (ndColouring n hn)
        with hCdef
      have hScardle : S.card ≤ n + 1 := le_trans (Finset.card_le_univ S) (by rw [hVcard])
      have hUcard : U.card ≤ n := by
        calc U.card ≤ (S.erase w).card := Finset.card_image_le
          _ = S.card - 1 := by rw [Finset.card_erase_of_mem hwS]
          _ ≤ n := by omega
      have hCcard : Cset.card ≤ n / 100 := by
        calc Cset.card
            ≤ ((T_core.edgeFinset ∩ (S.erase w).sym2).image (Sym2.map g')).card :=
              Finset.card_image_le
          _ ≤ (T_core.edgeFinset ∩ (S.erase w).sym2).card := Finset.card_image_le
          _ ≤ T_core.edgeFinset.card := Finset.card_le_card Finset.inter_subset_left
          _ ≤ n / 100 := hbound
      -- Off-`w` agreement: updating `g'` at `w` does not change colours of old core edges.
      have hInjOnOf : ∀ p : Fin (2 * n + 1), p ∉ U →
          Set.InjOn (Function.update g' w p) ↑S := by
        intro p hp a ha b hb hab
        rcases eq_or_ne a w with rfl | haw
        · rcases eq_or_ne b w with rfl | hbw
          · rfl
          · rw [Function.update_self, Function.update_of_ne hbw] at hab
            exact absurd (hab ▸ Finset.mem_image.mpr
              ⟨b, Finset.mem_erase.mpr ⟨hbw, Finset.mem_coe.mp hb⟩, rfl⟩) hp
        · rcases eq_or_ne b w with rfl | hbw
          · rw [Function.update_of_ne haw, Function.update_self] at hab
            exact absurd (hab.symm ▸ Finset.mem_image.mpr
              ⟨a, Finset.mem_erase.mpr ⟨haw, Finset.mem_coe.mp ha⟩, rfl⟩) hp
          · rw [Function.update_of_ne haw, Function.update_of_ne hbw] at hab
            exact hg'inj (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨haw, Finset.mem_coe.mp ha⟩))
              (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hbw, Finset.mem_coe.mp hb⟩)) hab
      have hmapeq : ∀ p : Fin (2 * n + 1), ∀ e ∈ T_core.edgeFinset ∩ (S.erase w).sym2,
          Sym2.map (Function.update g' w p) e = Sym2.map g' e := by
        intro p e he
        rw [Finset.mem_inter] at he
        induction e using Sym2.ind with
        | _ a b =>
          have hab := he.2
          rw [Finset.mk_mem_sym2_iff] at hab
          have hane : a ≠ w := (Finset.mem_erase.mp hab.1).1
          have hbne : b ≠ w := (Finset.mem_erase.mp hab.2).1
          simp only [Sym2.map_mk, Function.update_of_ne hane, Function.update_of_ne hbne]
      rcases Finset.eq_empty_or_nonempty Nb with hNe | hNe
      · -- No new core edge: place `w` at any unused position.
        obtain ⟨p, hp⟩ : ∃ p : Fin (2 * n + 1), p ∉ U := by
          have hUne : U ≠ Finset.univ := by
            intro hU
            have : U.card = 2 * n + 1 := by rw [hU, Finset.card_univ, Fintype.card_fin]
            omega
          obtain ⟨p, _, hp⟩ := Finset.exists_of_ssubset
            (lt_of_le_of_ne (Finset.subset_univ U) hUne)
          exact ⟨p, hp⟩
        refine ⟨Function.update g' w p, hInjOnOf p hp, ?_⟩
        have hseteq : T_core.edgeFinset ∩ S.sym2 = T_core.edgeFinset ∩ (S.erase w).sym2 := by
          ext e
          induction e using Sym2.ind with
          | _ a b =>
            simp only [Finset.mem_inter, SimpleGraph.mem_edgeFinset, Finset.mk_mem_sym2_iff,
              Finset.mem_erase]
            constructor
            · rintro ⟨hadj, haS, hbS⟩
              refine ⟨hadj, ⟨?_, haS⟩, ⟨?_, hbS⟩⟩
              · rintro rfl
                have hbNb : b ∈ Nb :=
                  Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hadj.ne', hbS⟩, hadj⟩
                simp [hNe] at hbNb
              · rintro rfl
                have haNb : a ∈ Nb :=
                  Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hadj.ne, haS⟩, hadj.symm⟩
                simp [hNe] at haNb
            · rintro ⟨hadj, ⟨_, haS⟩, ⟨_, hbS⟩⟩
              exact ⟨hadj, haS, hbS⟩
        rw [hseteq, Finset.image_congr (hmapeq p)]
        exact hg'rb
      · -- One new core edge `s(w, u)`.
        obtain ⟨u, hu⟩ := hNe
        have huNb := hu
        rw [hNbdef, Finset.mem_filter] at huNb
        obtain ⟨huSe, hadjwu⟩ := huNb
        have hpuU : g' u ∈ U := Finset.mem_image.mpr ⟨u, huSe, rfl⟩
        have hlt : U.card + 2 * Cset.card < 2 * n + 1 := by omega
        obtain ⟨p, hpU, hpC⟩ := exists_fresh_position n hn (g' u) U hpuU Cset hlt
        refine ⟨Function.update g' w p, hInjOnOf p hpU, ?_⟩
        -- The placed edge set gains exactly `s(w, u)`.
        have hseteq : T_core.edgeFinset ∩ S.sym2
            = insert s(w, u) (T_core.edgeFinset ∩ (S.erase w).sym2) := by
          ext e
          induction e using Sym2.ind with
          | _ a b =>
            simp only [Finset.mem_inter, SimpleGraph.mem_edgeFinset, Finset.mk_mem_sym2_iff,
              Finset.mem_insert, Finset.mem_erase, Sym2.eq_iff]
            constructor
            · rintro ⟨hadj, haS, hbS⟩
              by_cases haw : a = w
              · subst haw
                have hbu : b = u := by
                  have hb_nb : b ∈ Nb :=
                    Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hadj.ne', hbS⟩, hadj⟩
                  exact Finset.card_le_one.mp hNbcard b hb_nb u hu
                exact Or.inl (Or.inl ⟨rfl, hbu⟩)
              · by_cases hbw : b = w
                · subst hbw
                  have hau : a = u := by
                    have ha_nb : a ∈ Nb :=
                      Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hadj.ne, haS⟩, hadj.symm⟩
                    exact Finset.card_le_one.mp hNbcard a ha_nb u hu
                  exact Or.inl (Or.inr ⟨hau, rfl⟩)
                · exact Or.inr ⟨hadj, ⟨haw, haS⟩, ⟨hbw, hbS⟩⟩
            · rintro ((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨hadj, ⟨_, haS⟩, ⟨_, hbS⟩⟩)
              · exact ⟨hadjwu, hwS, Finset.mem_of_mem_erase huSe⟩
              · exact ⟨hadjwu.symm, Finset.mem_of_mem_erase huSe, hwS⟩
              · exact ⟨hadj, haS, hbS⟩
        rw [hseteq, Finset.image_insert]
        have hnew : Sym2.map (Function.update g' w p) s(w, u) = s(p, g' u) := by
          have hune : u ≠ w := (Finset.mem_erase.mp huSe).1
          simp only [Sym2.map_mk, Function.update_self, Function.update_of_ne hune]
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

/-- **Core embedding.** A subforest of $T$ with $\leq n/100$ edges embeds rainbow
into the ND-coloured $K_{2n+1}$. The key inputs are that $T$ is a tree (giving
$|V| = n+1 \leq 2n+1$) and $T_\text{core} \leq T$ (so $T_\text{core}$ is acyclic). -/
lemma caseC_embed_core (n : ℕ) (hn : 0 < n) {V : Type*} [Finite V]
    (T : SimpleGraph V) (hT : T.IsTree) (hcard : T.edgeSet.ncard = n)
    (T_core : SimpleGraph V) (h_le : T_core ≤ T)
    (h_small : T_core.edgeSet.ncard ≤ n / 100) :
    ∃ f_core : V ↪ Fin (2 * n + 1), Set.InjOn (ndColouring n hn) (T_core.map f_core).edgeSet := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  have hVcard : Fintype.card V = n + 1 := by
    have hc := hT.card_edgeFinset
    have he : T.edgeFinset.card = n := by
      rw [← hcard]; exact (Set.ncard_eq_toFinset_card' T.edgeSet).symm
    omega
  have hac : T_core.IsAcyclic := hT.isAcyclic.anti h_le
  have hbound : T_core.edgeFinset.card ≤ n / 100 := by
    rw [show T_core.edgeFinset.card = T_core.edgeSet.ncard from
      (Set.ncard_eq_toFinset_card' T_core.edgeSet).symm]
    exact h_small
  obtain ⟨g, hginj, hrb⟩ := caseC_greedy n hn hVcard T_core hac hbound Finset.univ
  have ginj : Function.Injective g := fun a b hab => hginj (by simp) (by simp) hab
  refine ⟨⟨g, ginj⟩, ?_⟩
  rw [SimpleGraph.edgeSet_map]
  have hcoe : (⟨g, ginj⟩ : V ↪ Fin (2 * n + 1)).sym2Map '' T_core.edgeSet
      = ↑((T_core.edgeFinset ∩ Finset.univ.sym2).image (Sym2.map g)) := by
    rw [Finset.sym2_univ, Finset.inter_univ, Finset.coe_image, SimpleGraph.coe_edgeFinset]
    ext e
    simp only [Set.mem_image, Function.Embedding.sym2Map_apply, Function.Embedding.coeFn_mk]
  rw [hcoe]
  exact hrb

/-- **Leaf extension.** Given a rainbow embedding of the core, extend it to a full
rainbow copy of $T$ by absorbing the leaf edges via the ND-colouring's 2-factorization. -/
lemma caseC_extend_embedding (n : ℕ) (hn : 0 < n) {V : Type*} [Finite V]
    (T : SimpleGraph V) (T_core : SimpleGraph V) (leaves : Set V)
    (h_decomp1 : T_core ≤ T) (h_decomp2 : ∀ v ∈ leaves, IsLeaf T v)
    (h_decomp3 : T_core.edgeSet ∪ {e ∈ T.edgeSet | ∃ v ∈ leaves, v ∈ e} = T.edgeSet)
    (f_core : V ↪ Fin (2 * n + 1))
    (h_core_inj : Set.InjOn (ndColouring n hn) (T_core.map f_core).edgeSet) :
    ∃ f : V ↪ Fin (2 * n + 1), Set.InjOn (ndColouring n hn) (T.map f).edgeSet := by
  sorry

lemma caseC_embedding_exists (δ : ℝ) (hδ : 0 < δ) (n : ℕ) (hn_pos : 0 < n) {V : Type*} [Finite V]
    (T : SimpleGraph V) (hT : T.IsTree) (hn : T.edgeSet.ncard = n) (hC : IsCaseC δ n T) :
    HasRainbowCopy n T := by
  obtain ⟨T_core, leaves, h_decomp1, h_decomp2, h_small, h_decomp3⟩ :=
    caseC_decompose δ n T hT hC
  obtain ⟨f_core, h_core_inj⟩ :=
    caseC_embed_core n hn_pos T hT hn T_core h_decomp1 h_small
  obtain ⟨f, hf_inj⟩ :=
    caseC_extend_embedding n hn_pos T T_core leaves h_decomp1 h_decomp2 h_decomp3 f_core h_core_inj
  exact ⟨f, fun _ => hf_inj⟩

/-- **Case C rainbow copy (§6–§7, M3, deterministic).** For small $\delta > 0$ and large $n$,
every Case C tree has a rainbow copy in the ND-coloured $K_{2n+1}$. -/
theorem caseC_rainbow (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ (n : ℕ) in Filter.atTop, ∀ {V : Type*} [Finite V] (T : SimpleGraph V),
      T.IsTree → T.edgeSet.ncard = n →
      IsCaseC δ n T → HasRainbowCopy n T := by
  apply Filter.eventually_atTop.2
  use 1
  intro n hn_large V _ T hT hn hC
  have hn_pos : 0 < n := by omega
  exact caseC_embedding_exists δ hδ n hn_pos T hT hn hC

end Ringel
