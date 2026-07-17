import Ringel.CaseANearEmbedding

namespace Ringel

open Classical

def IsCaseASource (δ : ℝ) (n : ℕ) {V : Type*} (T : SimpleGraph V) : Prop :=
  ∃ L : Set V,
    (∀ x ∈ L, IsLeaf T x) ∧
    (∀ x ∈ L, caseALeafAnchor T x ∉ L) ∧
    Set.InjOn (caseALeafAnchor T) L ∧
    ⌊δ ^ 6 * (n : ℝ)⌋₊ ≤ L.ncard

structure CaseAJointOutput (n : ℕ) (hn : 0 < n) {V : Type*} [Finite V]
    (T : SimpleGraph V) (L : Finset V) where
  anchor_outside : ∀ x ∈ L, caseALeafAnchor T x ∉ L
  anchor_injective : Set.InjOn (caseALeafAnchor T) (L : Set V)
  coreMap : V → Fin (2 * n + 1)
  core_injective : Set.InjOn coreMap {v | v ∉ L}
  core_rainbow : ∀ e₁ ∈ T.edgeSet, ∀ e₂ ∈ T.edgeSet,
    (∀ x ∈ L, x ∉ e₁) → (∀ x ∈ L, x ∉ e₂) →
    ndColouring n hn (Sym2.map coreMap e₁) = ndColouring n hn (Sym2.map coreMap e₂) →
    Sym2.map coreMap e₁ = Sym2.map coreMap e₂
  targets : Finset (Fin (2 * n + 1))
  colours : Finset (Fin n)
  matching : PerfectRainbowMatching (ndColouring n hn)
    (caseAAnchorImages n T L coreMap) targets colours
  targets_fresh : Disjoint (targets : Set (Fin (2 * n + 1)))
    (coreMap '' {v : V | v ∉ L})
  colours_fresh : Disjoint colours
    (T.edgeFinset.filter (fun e => ∀ x ∈ L, x ∉ e) |>.image
      (fun e => ndColouring n hn (Sym2.map coreMap e)))

theorem CaseAJointOutput.valid_embedding
    (n : ℕ) (hn : 0 < n) {V : Type*} [Finite V] (T : SimpleGraph V) (L : Finset V)
    (o : CaseAJointOutput n hn T L) :
    ∃ pos : V → Fin (2 * n + 1),
      valid_caseA_embedding n hn T L o.coreMap pos := by
  apply valid_caseA_embedding_of_nearEmbedding_finishing n hn T L o.anchor_outside
    (fun x hx y hy hxy => o.anchor_injective hx hy hxy) o.coreMap o.core_injective
    o.core_rainbow o.targets o.colours o.matching o.targets_fresh o.colours_fresh

theorem rainbowCopy_of_caseAJointOutput
    (n : ℕ) (hn : 0 < n) {V : Type*} [Finite V] (T : SimpleGraph V) (L : Finset V)
    (hleaf : ∀ x ∈ L, IsLeaf T x) (o : CaseAJointOutput n hn T L) :
    HasRainbowCopy n T := by
  obtain ⟨pos, hpos⟩ := o.valid_embedding n hn T L;
  obtain ⟨hcore_inj, hpos_inj, hpos_disjoint, hcore_rainbow, hpos_rainbow, hpos_disjoint_core⟩ := hpos;
  obtain ⟨g, hg⟩ := Ringel.extend_rainbow_leaves n hn T L (fun x => caseALeafAnchor T x) (by
  exact o.anchor_outside) (by
  intro e he;
  rcases e with ⟨ x, y ⟩;
  by_cases hx : x ∈ L <;> by_cases hy : y ∈ L <;> simp +decide at he ⊢;
  · grind +suggestions;
  · exact Or.inr ⟨ x, hx, Or.inl ⟨ rfl, by exact caseALeafAnchor_unique T ( hleaf x hx ) he ⟩ ⟩;
  · exact Or.inr ⟨ y, hy, by have := caseALeafAnchor_unique T ( hleaf y hy ) he.symm; tauto ⟩;
  · exact Or.inl fun z hz => ⟨ by rintro rfl; exact hx hz, by rintro rfl; exact hy hz ⟩) o.coreMap pos hcore_inj hpos_inj hpos_disjoint hcore_rainbow hpos_rainbow hpos_disjoint_core;
  use g;
  exact fun _ => hg

def AdmissibleCaseALeafSet (δ : ℝ) (n : ℕ) {V : Type*}
    (T : SimpleGraph V) (L : Finset V) : Prop :=
  (∀ x ∈ L, IsLeaf T x) ∧
  (∀ x ∈ L, caseALeafAnchor T x ∉ L) ∧
  Set.InjOn (caseALeafAnchor T) (L : Set V) ∧
  L.card = ⌊δ ^ 6 * (n : ℝ)⌋₊

theorem exists_admissibleCaseALeafSet_of_isCaseASource
    (δ : ℝ) (n : ℕ) {V : Type*} [Finite V] (T : SimpleGraph V)
    (h : IsCaseASource δ n T) :
    ∃ L : Finset V, AdmissibleCaseALeafSet δ n T L := by
  obtain ⟨ L, hL₁, hL₂, hL₃, hL₄ ⟩ := h;
  obtain ⟨ L', hL' ⟩ := Set.Finite.exists_finset_coe ( Set.toFinite L );
  obtain ⟨ L'', hL'' ⟩ := Finset.exists_subset_card_eq ( show ⌊δ ^ 6 * ( n : ℝ ) ⌋₊ ≤ L'.card from by simpa [ ← hL', Set.ncard_eq_toFinset_card' ] using hL₄ ) ; use L''; simp_all +decide [ AdmissibleCaseALeafSet ] ;
  exact ⟨ fun x hx => hL₁ x ( hL'.subset ( hL''.1 hx ) ), fun x hx => fun hx' => hL₂ x ( hL'.subset ( hL''.1 hx ) ) ( hL'.subset ( hL''.1 hx' ) ), hL₃.mono ( by aesop_cat ) ⟩

def CaseASourceJointGoal : Prop :=
  ∀ (δ : ℝ), 0 < δ →
    ∀ᶠ n : ℕ in Filter.atTop, ∀ {V : Type*} [Finite V] (T : SimpleGraph V),
      T.IsTree → T.edgeSet.ncard = n → IsCaseASource δ n T →
      ∃ (L : Finset V) (hn : 0 < n),
        AdmissibleCaseALeafSet δ n T L ∧ Nonempty (CaseAJointOutput n hn T L)

set_option maxHeartbeats 800000 in
theorem caseAJointOutput_of_hasRainbowCopy
    (δ : ℝ) (n : ℕ) (hn : 0 < n) {V : Type*} [Finite V] (T : SimpleGraph V)
    (L : Finset V) (hL : AdmissibleCaseALeafSet δ n T L)
    (hcopy : HasRainbowCopy n T) : Nonempty (CaseAJointOutput n hn T L) := by
  cases' hcopy with f hf
  generalize_proofs at *;
  have hleafEdge : ∀ x ∈ L,
      s(f x, f (caseALeafAnchor T x)) ∈ (T.map f).edgeSet := by
    intro x hx
    rw [SimpleGraph.edgeSet_map]
    exact ⟨s(x, caseALeafAnchor T x), caseALeafAnchor_adj T (hL.1 x hx), by simp⟩
  use hL.2.1, hL.2.2.1, f, f.injective.injOn, by
    intro e₁ he₁ e₂ he₂ h₁ h₂ h₃; have := hf hn; have := this; simp_all +decide [ Set.InjOn ] ;
    exact this ( by cases e₁; aesop ) ( by cases e₂; aesop ) h₃, L.image f, ?_, ?_, ?_, ?_;
  exact Finset.image ( fun x => ndColouring n hn s(f x, f ( caseALeafAnchor T x)) ) L;
  · constructor;
    case matching.target => exact fun x hx => f ( Classical.choose ( Finset.mem_image.mp hx ) );
    · grind +qlia;
    · grind +qlia;
    · intro x hx x' hx' h
      let a := Classical.choose (Finset.mem_image.mp hx)
      let b := Classical.choose (Finset.mem_image.mp hx')
      have ha := Classical.choose_spec (Finset.mem_image.mp hx)
      have hb := Classical.choose_spec (Finset.mem_image.mp hx')
      have hxa : f (caseALeafAnchor T a) = x := ha.2
      have hxb : f (caseALeafAnchor T b) = x' := hb.2
      have hedge := hf hn (hleafEdge a ha.1) (hleafEdge b hb.1) (by
        simpa [hxa, hxb, Sym2.eq_swap] using h)
      rw [Sym2.eq_iff] at hedge
      rcases hedge with hdirect | hswap
      · exact hxa.symm.trans (hdirect.2.trans hxb)
      · have hab : a = caseALeafAnchor T b := f.injective hswap.1
        exact (hL.2.1 b hb.1 (hab ▸ ha.1)).elim
    · ext; simp [Finset.mem_image];
      constructor;
      · grind +splitIndPred;
      · rintro ⟨ x, hx, rfl ⟩
        generalize_proofs at *;
        use f (caseALeafAnchor T x);
        refine' ⟨ _, _ ⟩
        all_goals generalize_proofs at *;
        · exact Finset.mem_image_of_mem _ hx;
        · have := Classical.choose_spec ‹∃ x_1 ∈ L, f ( caseALeafAnchor T x_1 ) = f ( caseALeafAnchor T x ) ›
          generalize_proofs at *;
          have := hL.2.2.1 this.1 hx; simp_all +decide [ f.injective.eq_iff ] ;
          grind +revert;
  · grind +suggestions;
  · simp +decide [ Finset.disjoint_left ];
    intro x hx e he hne h; have := hf hn; simp_all +decide [ Set.InjOn ] ;
    specialize this ( show Sym2.map f e ∈ ( SimpleGraph.map f T ).edgeSet from ?_ ) ( show s(f x, f ( caseALeafAnchor T x )) ∈ ( SimpleGraph.map f T ).edgeSet from ?_ ) h;
    · cases e ; aesop;
    · rw [SimpleGraph.edgeSet_map]
      exact ⟨s(x, caseALeafAnchor T x), caseALeafAnchor_adj T (hL.1 x hx), by simp⟩
    · rcases e with ⟨ u, v ⟩ ; simp_all +decide ;
      grind

theorem nonempty_caseAJointOutput_iff_hasRainbowCopy
    (δ : ℝ) (n : ℕ) (hn : 0 < n) {V : Type*} [Finite V] (T : SimpleGraph V)
    (L : Finset V) (hL : AdmissibleCaseALeafSet δ n T L) :
    Nonempty (CaseAJointOutput n hn T L) ↔ HasRainbowCopy n T := by
  constructor
  · rintro ⟨o⟩
    exact rainbowCopy_of_caseAJointOutput n hn T L hL.1 o
  · exact caseAJointOutput_of_hasRainbowCopy δ n hn T L hL

universe u

theorem caseASourceJointGoal_iff_eventual_rainbow :
    CaseASourceJointGoal.{u} ↔
      ∀ (δ : ℝ), 0 < δ →
        ∀ᶠ n : ℕ in Filter.atTop, ∀ {V : Type u} [Finite V] (T : SimpleGraph V),
          T.IsTree → T.edgeSet.ncard = n → IsCaseASource δ n T → HasRainbowCopy n T := by
  constructor
  · intro h δ hδ
    filter_upwards [h δ hδ] with n hn
    intro V _ T hT hcard hsource
    obtain ⟨L, hnpos, hL, ⟨o⟩⟩ := @hn V _ T hT hcard hsource
    exact rainbowCopy_of_caseAJointOutput n hnpos T L hL.1 o
  · intro h δ hδ
    have hpos : ∀ᶠ n : ℕ in Filter.atTop, 0 < n :=
      Filter.eventually_atTop.2 ⟨1, by omega⟩
    filter_upwards [h δ hδ, hpos] with n hcopy hnpos
    intro V _ T hT hcard hsource
    obtain ⟨L, hL⟩ := exists_admissibleCaseALeafSet_of_isCaseASource δ n T hsource
    exact ⟨L, hnpos, hL, caseAJointOutput_of_hasRainbowCopy δ n hnpos T L hL
      (@hcopy V _ T hT hcard hsource)⟩

end Ringel