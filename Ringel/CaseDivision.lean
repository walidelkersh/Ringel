import Mathlib
import Ringel.Primitives
import Ringel.TreeStructure

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
        change threshold ≤ (L v).card
        rw [L, ← Set.ncard_eq_toFinset_card']
        exact hv'))
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
