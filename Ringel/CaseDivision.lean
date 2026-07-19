import Mathlib
import Ringel.Primitives
import Ringel.TreeStructure
import Ringel.CaseA

namespace Ringel

/-- Raising the leaf-degree threshold can only remove fewer leaves. -/
lemma leavesAtHighDegreeVertices_anti {V : Type*} (T : SimpleGraph V)
    {a b : ℕ} (hab : a ≤ b) :
    leavesAtHighDegreeVertices T b ⊆ leavesAtHighDegreeVertices T a := by
  rintro w ⟨hleaf, v, hwv, hv⟩
  exact ⟨hleaf, v, hwv, hab.trans hv⟩

/-- A Case C reduction made at a threshold above the repository's deterministic threshold
still satisfies `IsCaseC`. -/
lemma isCaseC_of_large_threshold (δ : ℝ) (n threshold : ℕ) {V : Type*}
    [Finite V] (T : SimpleGraph V)
    (hthreshold : caseCThreshold n ≤ threshold)
    (hsmall :
      (Set.univ \ leavesAtHighDegreeVertices T threshold).ncard ≤ n / 100) :
    IsCaseC δ n T := by
  change
    (Set.univ \ leavesAtHighDegreeVertices T (caseCThreshold n)).ncard ≤ n / 100
  have hremoved :=
    leavesAtHighDegreeVertices_anti T hthreshold
  exact (Set.ncard_le_ncard
    (Set.diff_subset_diff_right hremoved) (Set.toFinite _)).trans hsmall

/-- Leaf-neighbour sets at distinct vertices are disjoint. -/
lemma leafNeighbours_disjoint {V : Type*} (T : SimpleGraph V) {u v : V}
    (huv : u ≠ v) :
    Disjoint (leafNeighbours T u) (leafNeighbours T v) := by
  rw [Set.disjoint_left]
  intro w hwu hwv
  obtain ⟨a, _, huniq⟩ := hwu.2
  have hua : u = a := huniq u hwu.1.symm
  have hva : v = a := huniq v hwv.1.symm
  exact huv (hua.trans hva.symm)

/-- A vertex with at least two pendant-leaf neighbours is not a leaf. -/
lemma highLeafDegreeVertices_not_leaf {V : Type*} (T : SimpleGraph V)
    {threshold : ℕ} (hthreshold : 2 ≤ threshold) {v : V}
    (hv : v ∈ highLeafDegreeVertices T threshold) :
    ¬ IsLeaf T v := by
  intro hleaf
  obtain ⟨w, _, huniq⟩ := hleaf
  have hsub : leafNeighbours T v ⊆ ({w} : Set V) := by
    intro x hx
    exact Set.mem_singleton_iff.mpr (huniq x hx.1)
  have hle : (leafNeighbours T v).ncard ≤ 1 := by
    calc
      (leafNeighbours T v).ncard ≤ ({w} : Set V).ncard :=
        Set.ncard_le_ncard hsub (Set.finite_singleton w)
      _ = 1 := Set.ncard_singleton w
  change threshold ≤ (leafNeighbours T v).ncard at hv
  omega

/-- Leaves deleted at a threshold of at least two are pairwise nonadjacent. -/
lemma leavesAtHighDegreeVertices_independent {V : Type*} (T : SimpleGraph V)
    {threshold : ℕ} (hthreshold : 2 ≤ threshold) :
    ∀ x ∈ leavesAtHighDegreeVertices T threshold,
      ∀ y ∈ leavesAtHighDegreeVertices T threshold, x ≠ y → ¬ T.Adj x y := by
  intro x hx y hy _ hxy
  obtain ⟨w, _, huniq⟩ := hx.1
  obtain ⟨a, hxa, hahigh⟩ := hx.2
  have hya : y = a := (huniq y hxy).trans (huniq a hxa).symm
  exact highLeafDegreeVertices_not_leaf T hthreshold hahigh (hya ▸ hy.1)

/-- Removing pendant leaves at centers of leaf degree at least two preserves a tree. -/
lemma residualTree_isTree {V : Type*} (T : SimpleGraph V) (hT : T.IsTree)
    {threshold : ℕ} (hthreshold : 2 ≤ threshold) :
    (CaseACore T (leavesAtHighDegreeVertices T threshold)).IsTree := by
  apply isTree_core T hT
  · intro v hv
    exact hv.1
  · exact leavesAtHighDegreeVertices_independent T hthreshold

/-- There are at most `|V| / threshold` vertices with `threshold` pendant-leaf neighbours. -/
lemma highLeafDegreeVertices_mul_le_card {V : Type*} [Finite V]
    (T : SimpleGraph V) (threshold : ℕ) :
    threshold * (highLeafDegreeVertices T threshold).ncard ≤ Nat.card V := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  let H : Finset V := (Set.toFinite (highLeafDegreeVertices T threshold)).toFinset
  let L : V → Finset V := fun v =>
    (Set.toFinite (leafNeighbours T v)).toFinset
  have hpairwise : (H : Set V).PairwiseDisjoint L := by
    intro u hu v hv huv
    change Disjoint (L u) (L v)
    rw [Finset.disjoint_left]
    intro w hwu hwv
    exact Set.disjoint_left.mp (leafNeighbours_disjoint T huv)
      (by simpa [L] using hwu) (by simpa [L] using hwv)
  have hlower : H.card * threshold ≤ ∑ v ∈ H, (L v).card := by
    simpa [nsmul_eq_mul] using
      (Finset.card_nsmul_le_sum H (fun v => (L v).card) threshold (by
        intro v hv
        have hv' : v ∈ highLeafDegreeVertices T threshold := by
          simpa [H] using hv
        change threshold ≤ (leafNeighbours T v).ncard at hv'
        change threshold ≤ (Set.toFinite (leafNeighbours T v)).toFinset.card
        simpa only [Set.ncard_eq_toFinset_card'] using hv'))
  have hunion : (H.biUnion L).card ≤ Fintype.card V := by
    simpa using Finset.card_le_card (Finset.subset_univ (H.biUnion L))
  have hbound : threshold * H.card ≤ Fintype.card V := by
    rw [Nat.mul_comm]
    exact hlower.trans ((Finset.card_biUnion hpairwise).symm ▸ hunion)
  simpa [H, Set.ncard_eq_toFinset_card', Nat.card_eq_fintype_card] using hbound

/-- **Lemma `Lemma_case_division` (§2).** For `0 < δ ≤ 1/4` and any `n`, every `n`-edge tree is in
Case A, Case B, or Case C. Proved via the geometric `split` lemma (`TreeStructure.tree_split_via_split`):
applying `split` with `k = ⌊δ⁻¹⌋ ≥ 4`, the leaf branch yields Case A and the bare-path branch yields
Case B. (The small-δ hypothesis is necessary: for large δ the trichotomy is false — a path graph
satisfies none of the three cases.) -/
lemma tree_split (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4) (n : ℕ) {V : Type*} [Finite V]
    (T : SimpleGraph V) (hTree : T.IsTree) (hn : T.edgeSet.ncard = n) :
    IsCaseA δ n T ∨ IsCaseB δ n T ∨ IsCaseC δ n T :=
  TreeStructure.tree_split_via_split δ hδ hδ' n T hTree hn

theorem case_division (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4) :
    ∀ᶠ (n : ℕ) in Filter.atTop, ∀ {V : Type*} [Finite V] (T : SimpleGraph V),
      T.IsTree → T.edgeSet.ncard = n →
      IsCaseA δ n T ∨ IsCaseB δ n T ∨ IsCaseC δ n T := by
  filter_upwards
  intro n V _ T hT hn
  exact tree_split δ hδ hδ' n T hT hn

end Ringel
