import Ringel.CaseA
import Ringel.PaperFinishing



namespace Ringel

open Classical


theorem pairwise_nonadjacent_leaves_do_not_force_distinct_anchors :
    ∃ (T : SimpleGraph (Fin 3)) (leaves : Finset (Fin 3)),
      (∀ x ∈ leaves, IsLeaf T x) ∧
      (∀ x ∈ leaves, caseALeafAnchor T x ∉ leaves) ∧
      (∀ x ∈ leaves, ∀ y ∈ leaves, x ≠ y → ¬T.Adj x y) ∧
      ∃ x ∈ leaves, ∃ y ∈ leaves, x ≠ y ∧
        caseALeafAnchor T x = caseALeafAnchor T y := by
  use ( SimpleGraph.mk fun v w => v ≠ w ∧ ( v = 0 ∧ w = 1 ∨ v = 1 ∧ w = 0 ∨ v = 1 ∧ w = 2 ∨ v = 2 ∧ w = 1 ) );
  refine' ⟨ { 0, 2 }, _, _, _, _ ⟩ <;> simp +decide [ IsLeaf ];
  · exact ⟨ ⟨ 1, by decide, by decide ⟩, ⟨ 1, by decide, by decide ⟩ ⟩;
  · unfold caseALeafAnchor;
    split_ifs <;> simp_all +decide [ IsLeaf ];
    · grind +splitIndPred;
    · exact ‹¬∃! w : Fin 3, ¬2 = w ∧ w = 1› ⟨ 1, by decide, by decide ⟩;
    · exact ‹¬∃! w : Fin 3, ¬0 = w ∧ w = 1› ⟨ 1, by decide, by decide ⟩;
    · simp_all +decide [ ExistsUnique ];
  · unfold caseALeafAnchor; simp +decide [ IsLeaf ] ;
    split_ifs <;> simp_all +decide [ ExistsUnique ];
    grind


noncomputable def caseAAnchorImages
    (n : ℕ) {V : Type*} [Finite V] (T : SimpleGraph V) (leaves : Finset V)
    (g : V → Fin (2 * n + 1)) : Finset (Fin (2 * n + 1)) :=
  leaves.image (fun x => g (caseALeafAnchor T x))


lemma valid_caseA_embedding_of_nearEmbedding_finishing
    (n : ℕ) (hn : 0 < n) {V : Type*} [Finite V]
    (T : SimpleGraph V) (leaves : Finset V)
    (hanchor_outside : ∀ x ∈ leaves, caseALeafAnchor T x ∉ leaves)
    (hanchor_injective : ∀ x ∈ leaves, ∀ y ∈ leaves,
      caseALeafAnchor T x = caseALeafAnchor T y → x = y)
    (g : V → Fin (2 * n + 1))
    (hcore_injective : Set.InjOn g {v | v ∉ leaves})
    (hcore_rainbow : ∀ e₁ ∈ T.edgeSet, ∀ e₂ ∈ T.edgeSet,
      (∀ x ∈ leaves, x ∉ e₁) → (∀ x ∈ leaves, x ∉ e₂) →
      ndColouring n hn (Sym2.map g e₁) = ndColouring n hn (Sym2.map g e₂) →
      Sym2.map g e₁ = Sym2.map g e₂)
    (Y : Finset (Fin (2 * n + 1)))
    (colours : Finset (Fin n))
    (M : PerfectRainbowMatching (ndColouring n hn)
      (caseAAnchorImages n T leaves g) Y colours)
    (htarget_disjoint : Disjoint (Y : Set (Fin (2 * n + 1)))
      (g '' {v : V | v ∉ leaves}))
    (hcolours_disjoint : Disjoint colours
      (T.edgeFinset.filter (fun e => ∀ x ∈ leaves, x ∉ e) |>.image
        (fun e => ndColouring n hn (Sym2.map g e)))) :
    ∃ pos : V → Fin (2 * n + 1), valid_caseA_embedding n hn T leaves g pos := by
  refine' ⟨ _, _, _, _, _, _ ⟩;
  use fun x => if hx : x ∈ leaves then M.target ( g ( caseALeafAnchor T x ) ) ( by
    exact Finset.mem_image_of_mem _ hx ) else 0;
  · exact hcore_injective;
  · intro x hx y hy hxy;
    simp_all +decide;
    exact hanchor_injective x hx y hy ( hcore_injective ( show caseALeafAnchor T x ∉ leaves from hanchor_outside x hx ) ( show caseALeafAnchor T y ∉ leaves from hanchor_outside y hy ) ( M.target_injective _ _ _ _ hxy ) );
  · intro x hx v hv
    simp [hx];
    exact fun h => htarget_disjoint.le_bot ⟨ M.target_mem _ _, ⟨ v, hv, h.symm ⟩ ⟩;
  · exact hcore_rainbow;
  · refine' ⟨ _, _ ⟩;
    · intro x₁ hx₁ x₂ hx₂ h;
      have := M.rainbow ( g ( caseALeafAnchor T x₁ ) ) ( by
        exact Finset.mem_image_of_mem _ hx₁ ) ( g ( caseALeafAnchor T x₂ ) ) ( by
        exact Finset.mem_image_of_mem _ hx₂ ) ?_;
      · exact hanchor_injective x₁ hx₁ x₂ hx₂ ( hcore_injective ( show caseALeafAnchor T x₁ ∉ leaves from hanchor_outside x₁ hx₁ ) ( show caseALeafAnchor T x₂ ∉ leaves from hanchor_outside x₂ hx₂ ) this );
      · grind;
    · intro x hx e he hle
      have hcolour : ndColouring n hn s(M.target (g (caseALeafAnchor T x)) (by
      exact Finset.mem_image_of_mem _ hx), g (caseALeafAnchor T x)) ∈ colours := by
        all_goals generalize_proofs at *;
        convert M.colours_eq.symm ▸ Finset.mem_image_of_mem _ ( Finset.mem_univ ( ⟨ g ( caseALeafAnchor T x ), by assumption ⟩ : caseAAnchorImages n T leaves g ) ) using 1;
        exact congr_arg _ ( Sym2.eq_swap );
      simp_all +decide [ Finset.disjoint_left ];
      contrapose! hcolours_disjoint;
      exact ⟨ _, hcolour, _, he, hle, hcolours_disjoint.symm ⟩


theorem caseA_positive_probability_of_nearEmbedding_finishing
    (n : ℕ) (hn : 0 < n) {V : Type*} [Finite V]
    (T : SimpleGraph V) (leaves : Finset V)
    (hanchor_outside : ∀ x ∈ leaves, caseALeafAnchor T x ∉ leaves)
    (hanchor_injective : ∀ x ∈ leaves, ∀ y ∈ leaves,
      caseALeafAnchor T x = caseALeafAnchor T y → x = y)
    (g : V → Fin (2 * n + 1))
    (hcore_injective : Set.InjOn g {v | v ∉ leaves})
    (hcore_rainbow : ∀ e₁ ∈ T.edgeSet, ∀ e₂ ∈ T.edgeSet,
      (∀ x ∈ leaves, x ∉ e₁) → (∀ x ∈ leaves, x ∉ e₂) →
      ndColouring n hn (Sym2.map g e₁) = ndColouring n hn (Sym2.map g e₂) →
      Sym2.map g e₁ = Sym2.map g e₂)
    (Y : Finset (Fin (2 * n + 1))) (colours : Finset (Fin n))
    (M : PerfectRainbowMatching (ndColouring n hn)
      (caseAAnchorImages n T leaves g) Y colours)
    (htarget_disjoint : Disjoint (Y : Set (Fin (2 * n + 1)))
      (g '' {v : V | v ∉ leaves}))
    (hcolours_disjoint : Disjoint colours
      (T.edgeFinset.filter (fun e => ∀ x ∈ leaves, x ∉ e) |>.image
        (fun e => ndColouring n hn (Sym2.map g e))))
    [Fintype ((V → Fin (2 * n + 1)) × (V → Fin (2 * n + 1)))] :
    prob_event (fun gp : (V → Fin (2 * n + 1)) × (V → Fin (2 * n + 1)) =>
      valid_caseA_embedding n hn T leaves gp.1 gp.2) > 0 := by
  obtain ⟨pos, hpos⟩ := valid_caseA_embedding_of_nearEmbedding_finishing n hn T leaves hanchor_outside hanchor_injective g hcore_injective hcore_rainbow Y colours M htarget_disjoint hcolours_disjoint;
  apply Ringel.prob_pos_of_exists;
  exact ⟨ ⟨ g, pos ⟩, hpos ⟩

end Ringel
namespace Ringel


lemma valid_caseA_embedding_of_hasRainbowCopy
    (n : ℕ) (hn : 0 < n) {V : Type*} [Finite V] (T : SimpleGraph V)
    (leaves : Finset V)
    (hleaf : ∀ x ∈ leaves, IsLeaf T x)
    (hanchor : ∀ x ∈ leaves, caseALeafAnchor T x ∉ leaves)
    (hcopy : HasRainbowCopy n T) :
    ∃ g pos : V → Fin (2 * n + 1), valid_caseA_embedding n hn T leaves g pos := by
  obtain ⟨f, hf⟩ := hcopy
  use f ∘ fun x => x, f ∘ fun x => x;
  refine' ⟨ _, _, _, _, _ ⟩;
  · exact f.injective.injOn;
  · exact f.injective.injOn;
  · exact fun x hx v hv => f.injective.ne ( by aesop );
  · intro e₁ he₁ e₂ he₂ h₁ h₂ h₃;
    convert hf hn _ _ h₃;
    · cases e₁ ; aesop;
    · cases e₂ ; aesop;
  · refine' ⟨ _, _ ⟩;
    · intro x₁ hx₁ x₂ hx₂ h;
      have := hf hn;
      have := @this s(f x₁, f (caseALeafAnchor T x₁)) ?_
        s(f x₂, f (caseALeafAnchor T x₂)) ?_ h <;>
        simp_all +decide [SimpleGraph.map];
      · grind;
      · exact ⟨(caseALeafAnchor_adj T (hleaf x₁ hx₁)).ne,
          ⟨x₁, caseALeafAnchor T x₁,
            caseALeafAnchor_adj T (hleaf x₁ hx₁), rfl, rfl⟩⟩
      · exact ⟨(caseALeafAnchor_adj T (hleaf x₂ hx₂)).ne,
          ⟨x₂, caseALeafAnchor T x₂,
            caseALeafAnchor_adj T (hleaf x₂ hx₂), rfl, rfl⟩⟩
    · intro x hx e he hne;
      have := hf hn;
      refine' this.ne _ _ _;
      · rw [SimpleGraph.edgeSet_map]
        exact ⟨s(x, caseALeafAnchor T x), caseALeafAnchor_adj T (hleaf x hx), rfl⟩
      · rw [SimpleGraph.edgeSet_map]
        exact ⟨e, he, rfl⟩;
      · rcases e with ⟨ u, v ⟩ ; simp_all +decide [ Sym2.eq ]


theorem caseAEmbeddingInput_of_hasRainbowCopy
    (n : ℕ) {V : Type*} [Finite V] (T : SimpleGraph V)
    (hcopy : HasRainbowCopy n T) : CaseAEmbeddingInput n T := by
  intro _δ hn leaves _ _hδ _hnlarge _hT _hcard hleaf hanchor _hindep _hsize
  obtain ⟨g, pos, hg⟩ :=
    valid_caseA_embedding_of_hasRainbowCopy n hn T leaves hleaf hanchor hcopy
  classical
  exact prob_pos_of_exists _ ⟨⟨g, pos⟩, hg⟩


theorem hasRainbowCopy_of_caseAEmbeddingInput_of_admissibleLeaves
    (δ : ℝ) (hδ : 0 < δ) (n : ℕ) (hn : 0 < n) (hnlarge : 1 < n)
    {V : Type*} [Finite V] (T : SimpleGraph V)
    (hT : T.IsTree) (hcard : T.edgeSet.ncard = n)
    (S : Set V) (hleaf : ∀ x ∈ S, IsLeaf T x)
    (hindep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ T.Adj x y)
    (hsize : ⌊δ ^ 6 * (n : ℝ)⌋₊ ≤ S.ncard)
    (hinput : CaseAEmbeddingInput n T) : HasRainbowCopy n T := by
  exact caseA_rainbow δ hδ n hn hnlarge T hT hcard S hleaf hsize hindep hinput

end Ringel
namespace Ringel


theorem caseAEmbeddingInput_iff_hasRainbowCopy
    (δ : ℝ) (hδ : 0 < δ) (n : ℕ) (hn : 0 < n) (hnlarge : 1 < n)
    {V : Type*} [Finite V] (T : SimpleGraph V)
    (hT : T.IsTree) (hcard : T.edgeSet.ncard = n)
    (S : Set V) (hleaf : ∀ x ∈ S, IsLeaf T x)
    (hindep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ T.Adj x y)
    (hsize : ⌊δ ^ 6 * (n : ℝ)⌋₊ ≤ S.ncard) :
    CaseAEmbeddingInput n T ↔ HasRainbowCopy n T := by
  constructor
  · exact hasRainbowCopy_of_caseAEmbeddingInput_of_admissibleLeaves
      δ hδ n hn hnlarge T hT hcard S hleaf hindep hsize
  · exact caseAEmbeddingInput_of_hasRainbowCopy n T

end Ringel
