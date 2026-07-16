import Mathlib
import Ringel.Primitives
import Ringel.PaperFinishing

namespace Ringel

open Classical

set_option maxHeartbeats 800000

/-!
# MPS §4: deterministic colour-cover matching

This module formalizes Lemma `colourcover` from §4, lines 96–111.  All parameters are finite.
The two asymptotic uses in the paper are replaced by the inequalities
`4 * C'.card ≤ repletion` and `3 * X.card ≤ colourDegree ...`.
-/

/-- Every colour has at least `r` edges with one endpoint in `X` and the other in `V`.
This is the paper's pair-repletion notion (as opposed to a minimum vertex degree). -/
def ColourPairReplete {W K : Type*} [DecidableEq K]
    (colour : Sym2 W → K) (X V : Finset W) (r : ℕ) : Prop :=
  ∀ col : K, r ≤ ((X ×ˢ V).filter (fun p => colour s(p.1, p.2) = col)).card

/-- Number of neighbours of `x` in `V` joined to it by a colour from `C`. -/
def allowedColourDegree {W K : Type*} [DecidableEq W] [DecidableEq K]
    (colour : Sym2 W → K) (C : Finset K) (V : Finset W) (x : W) : ℕ :=
  (V.filter (fun v => colour s(x, v) ∈ C)).card

/-
Finite greedy conflict-avoidance principle.  If every item has at least `q|S|`
candidates, while each previous choice rules out at most `q` candidates for a later item, choices
can be made pairwise nonconflicting.
-/
lemma greedy_conflict_choice {A B : Type*} [DecidableEq A] [DecidableEq B]
    (S : Finset A) (candidate : A → Finset B) (bad : B → B → Prop) [DecidableRel bad]
    (q : ℕ) (hq : 0 < q) (hbad_symm : Symmetric bad)
    (hcandidates : ∀ a ∈ S, q * S.card ≤ (candidate a).card)
    (hbad : ∀ a ∈ S, ∀ b : B,
      ((candidate a).filter (fun b' => bad b b')).card ≤ q) :
    ∃ choose : (a : A) → a ∈ S → B,
      (∀ a ha, choose a ha ∈ candidate a) ∧
      (∀ a ha a' ha', a ≠ a' → ¬ bad (choose a ha) (choose a' ha')) := by
  induction' S using Finset.induction with a S haS ih;
  · simp +zetaDelta at *;
    exact ⟨ fun _ _ => by contradiction ⟩;
  · simp_all +decide [ Nat.mul_succ ];
    obtain ⟨ choose, hchoose₁, hchoose₂ ⟩ := ih fun a ha => by linarith [ hcandidates.2 a ha ] ;
    -- Let's choose a candidate for `a` that is not in conflict with any of the previous choices.
    obtain ⟨b, hb⟩ : ∃ b ∈ candidate a, ∀ a' ha', ¬bad b (choose a' ha') := by
      have h_forbidden : (Finset.biUnion (Finset.attach S) (fun i => Finset.filter (fun b => bad (choose i.1 i.2) b) (candidate a))).card ≤ q * S.card := by
        exact le_trans ( Finset.card_biUnion_le ) ( by simpa [ mul_comm ] using Finset.sum_le_sum fun i ( hi : i ∈ S.attach ) => hbad.1 ( choose i.1 i.2 ) );
      contrapose! h_forbidden;
      rw [ show ( S.attach.biUnion fun i => { b ∈ candidate a | bad (choose i.1 i.2) b } ) = candidate a from ?_ ];
      · linarith;
      · ext b; simp;
        exact fun hb => by obtain ⟨ a', ha', hab ⟩ := h_forbidden b hb; exact ⟨ a', ha', hbad_symm hab ⟩ ;
    refine' ⟨ fun x hx => if hx' : x = a then b else choose x ( by aesop ), _, _ ⟩ <;> simp_all +decide [ Symmetric ];
    · grind;
    · grind +ring

/-
In a two-factorization, among the ordered `X × V` edges of one colour, at most four
meet either endpoint of a fixed ordered edge.
-/
lemma colour_pair_conflict_card_le_four
    (n : ℕ) (colour : Sym2 (Fin (2 * n + 1)) → Fin n)
    (X V : Finset (Fin (2 * n + 1))) (htwo : IsTwoFactorization n colour)
    (hXV : Disjoint X V) (col : Fin n) (p : Fin (2 * n + 1) × Fin (2 * n + 1)) :
    (((X ×ˢ V).filter (fun q => colour s(q.1, q.2) = col)).filter
      (fun q => q.1 = p.1 ∨ q.1 = p.2 ∨ q.2 = p.1 ∨ q.2 = p.2)).card ≤ 4 := by
  have h_card : (Finset.filter (fun q => q.1 = p.1 ∨ q.2 = p.1) (Finset.filter (fun q => colour (s(q.1, q.2)) = col) (X ×ˢ V))).card ≤ 2 ∧ (Finset.filter (fun q => q.1 = p.2 ∨ q.2 = p.2) (Finset.filter (fun q => colour (s(q.1, q.2)) = col) (X ×ˢ V))).card ≤ 2 := by
    constructor <;> have := htwo p.1 col <;> have := htwo p.2 col <;> simp_all +decide [ Finset.filter_or, Finset.filter_and ];
    · convert Set.ncard_le_ncard ( show { e : Sym2 ( Fin ( 2 * n + 1 ) ) | p.1 ∈ e ∧ ¬e.IsDiag ∧ colour e = col } ⊇ ( Finset.image ( fun q : Fin ( 2 * n + 1 ) × Fin ( 2 * n + 1 ) => s(q.1, q.2) ) ( Finset.filter ( fun q : Fin ( 2 * n + 1 ) × Fin ( 2 * n + 1 ) => q.1 = p.1 ∨ q.2 = p.1 ) ( Finset.filter ( fun q : Fin ( 2 * n + 1 ) × Fin ( 2 * n + 1 ) => colour s(q.1, q.2) = col ) ( X ×ˢ V ) ) ) ) from ?_ ) using 2;
      · rw [ Set.ncard_coe_finset, Finset.card_image_of_injOn ];
        · exact congr_arg Finset.card ( by ext; aesop );
        · intro q hq q' hq' h; simp_all +decide [ Finset.disjoint_left, Sym2.eq_iff ] ;
          grind;
      · linarith;
      · simp +decide [ Set.subset_def, Finset.mem_image ];
        rintro _ a b ha hb h₁ h₂ rfl; rcases h₂ with ( rfl | rfl ) <;> simp_all +decide [ Finset.disjoint_left ] ;
        · exact fun h => hXV ha ( h.symm ▸ hb );
        · grind +splitIndPred;
    · have h_card : (Finset.image (fun q => s(q.1, q.2)) (Finset.filter (fun q => q.1 = p.2 ∨ q.2 = p.2) (Finset.filter (fun q => colour (s(q.1, q.2)) = col) (X ×ˢ V)))).card ≤ 2 := by
        rw [ ← Set.ncard_coe_finset ];
        refine' le_trans ( Set.ncard_le_ncard _ ) this.le;
        simp +contextual [ Set.subset_def, Finset.mem_image ];
        rintro x a b ha hb h₁ h₂ rfl; cases h₂ <;> simp_all +decide [ Finset.disjoint_left ] ;
        · exact fun h => hXV ha ( h.symm ▸ hb );
        · exact fun h => hXV ha ( h.symm ▸ hb );
      rw [ Finset.card_image_of_injOn ] at h_card;
      · convert h_card using 2 ; ext ; aesop;
      · intro x hx y hy; simp_all +decide [ Sym2.eq_iff ] ;
        rintro ( rfl | rfl ) <;> simp_all +decide [ Finset.disjoint_left ];
  convert le_trans ( Finset.card_union_le _ _ ) ( add_le_add h_card.1 h_card.2 ) using 2 ; ext ; aesop

/-
The prescribed-colour phase: repletion and local 2-boundedness select one vertex-disjoint
edge of every prescribed colour.
-/
lemma prescribed_colour_matching
    (n : ℕ) (colour : Sym2 (Fin (2 * n + 1)) → Fin n)
    (X V : Finset (Fin (2 * n + 1))) (C' : Finset (Fin n)) (repletion : ℕ)
    (htwo : IsTwoFactorization n colour) (hXV : Disjoint X V)
    (hreplete : ColourPairReplete colour X V repletion)
    (hprescribed : 4 * C'.card ≤ repletion) :
    ∃ edge : (c : Fin n) → c ∈ C' → (Fin (2 * n + 1) × Fin (2 * n + 1)),
      (∀ c hc, edge c hc ∈ X ×ˢ V) ∧
      (∀ c hc, colour s((edge c hc).1, (edge c hc).2) = c) ∧
      (∀ c hc d hd, c ≠ d →
        (edge c hc).1 ≠ (edge d hd).1 ∧ (edge c hc).2 ≠ (edge d hd).2) := by
  convert greedy_conflict_choice C' ( fun c => Finset.filter ( fun p => colour s(p.1, p.2) = c ) ( X ×ˢ V ) ) ( fun p q => p.1 = q.1 ∨ p.2 = q.2 ) 4 ?_ ?_ ?_ ?_ using 1;
  · grind;
  · norm_num;
  · exact fun p q h => by tauto;
  · exact fun c hc => le_trans hprescribed ( hreplete c );
  · simp +zetaDelta at *;
    intro c hc a b;
    have := colour_pair_conflict_card_le_four n colour X V htwo hXV c ( a, b );
    refine' le_trans _ this;
    refine Finset.card_mono ?_;
    simp +contextual [ Finset.subset_iff ];
    grind +qlia

/-
A two-factorization has at most two neighbours of any fixed colour at a vertex,
when the neighbours lie in a set disjoint from that vertex.
-/
lemma vertex_colour_degree_le_two
    (n : ℕ) (colour : Sym2 (Fin (2 * n + 1)) → Fin n)
    (X V : Finset (Fin (2 * n + 1))) (htwo : IsTwoFactorization n colour)
    (hXV : Disjoint X V) (x : Fin (2 * n + 1)) (hx : x ∈ X) (col : Fin n) :
    (V.filter (fun v => colour s(x, v) = col)).card ≤ 2 := by
  have h_image : (Set.image (fun v => s(x, v)) {v ∈ V | colour s(x, v) = col}).ncard ≤ 2 := by
    refine' le_trans _ ( htwo x col |> le_of_eq );
    refine' Set.ncard_le_ncard _;
    simp +contextual [ Set.image_subset_iff ];
    exact fun y hy hxy => fun h => Finset.disjoint_left.mp hXV hx ( h ▸ hy );
  rw [ ← Set.ncard_coe_finset ];
  convert h_image using 1;
  rw [ Set.InjOn.ncard_image ];
  · congr ; aesop;
  · intro v hv w hw; aesop

/-
After deleting prescribed targets and prescribed colours, every remaining source still has
at least three times the number of remaining sources as available targets.
-/
lemma remaining_candidate_card
    (n : ℕ) (colour : Sym2 (Fin (2 * n + 1)) → Fin n)
    (X V : Finset (Fin (2 * n + 1))) (C C' : Finset (Fin n))
    (htwo : IsTwoFactorization n colour) (hXV : Disjoint X V)
    (edge : (c : Fin n) → c ∈ C' → (Fin (2 * n + 1) × Fin (2 * n + 1)))
    (hedge_mem : ∀ c hc, edge c hc ∈ X ×ˢ V)
    (hedge_disjoint : ∀ c hc d hd, c ≠ d →
      (edge c hc).1 ≠ (edge d hd).1 ∧ (edge c hc).2 ≠ (edge d hd).2)
    (hdense : ∀ x : Fin (2 * n + 1),
      3 * X.card ≤ allowedColourDegree colour C V x) :
    let XP := Finset.image (fun c : C' => (edge c.1 c.2).1) Finset.univ
    let VP := Finset.image (fun c : C' => (edge c.1 c.2).2) Finset.univ
    let R := X \ XP
    ∀ x ∈ R, 3 * R.card ≤
      ((V \ VP).filter (fun v => colour s(x, v) ∈ C \ C')).card := by
  intros XP VP R x hxR
  have h_card_R : R.card = X.card - C'.card := by
    rw [ Finset.card_sdiff ];
    rw [ Finset.card_eq_sum_ones, Finset.card_eq_sum_ones ];
    rw [ show XP ∩ X = XP from Finset.inter_eq_left.mpr <| Finset.image_subset_iff.mpr fun c hc => by aesop ] ; rw [ Finset.sum_image <| by intros a ha b hb hab; contrapose! hab; aesop ] ; aesop;
  have h_card_VP : VP.card = C'.card := by
    rw [ Finset.card_image_of_injective ];
    · simp +decide [ Finset.card_univ ];
    · intro c d hcd; specialize hedge_disjoint c c.2 d d.2; aesop;
  have h_card_XP : XP.card = C'.card := by
    grind
  generalize_proofs at *;
  have h_card_candidates : (V.filter (fun v => colour s(x, v) ∈ C \ C')).card ≥ (V.filter (fun v => colour s(x, v) ∈ C)).card - 2 * C'.card := by
    have h_card_candidates : (V.filter (fun v => colour s(x, v) ∈ C \ C')).card ≥ (V.filter (fun v => colour s(x, v) ∈ C)).card - (V.filter (fun v => colour s(x, v) ∈ C')).card := by
      simp +decide [ Finset.filter_mem_eq_inter, Finset.filter_not ];
      rw [ ← Finset.card_union_add_card_inter ];
      exact le_add_right ( Finset.card_le_card fun v hv => by by_cases hv' : colour s(x, v) ∈ C' <;> aesop );
    have h_card_candidates : (V.filter (fun v => colour s(x, v) ∈ C')).card ≤ 2 * C'.card := by
      have h_card_candidates : (V.filter (fun v => colour s(x, v) ∈ C')).card ≤ Finset.sum C' (fun c => (V.filter (fun v => colour s(x, v) = c)).card) := by
        rw [ ← Finset.card_biUnion ];
        · exact Finset.card_le_card fun v hv => by aesop;
        · exact fun a ha b hb hab => Finset.disjoint_left.mpr fun v hv₁ hv₂ => hab <| by aesop;
      exact h_card_candidates.trans ( le_trans ( Finset.sum_le_sum fun _ _ => vertex_colour_degree_le_two n colour X V htwo hXV x ( Finset.mem_sdiff.mp hxR |>.1 ) _ ) ( by simp +decide [ mul_comm ] ) );
    exact le_trans ( Nat.sub_le_sub_left h_card_candidates _ ) ‹_›;
  have h_card_candidates : (V.filter (fun v => colour s(x, v) ∈ C \ C')).card ≤ (V.filter (fun v => colour s(x, v) ∈ C \ C') \ VP).card + VP.card := by
    grind;
  simp_all +decide [ Finset.filter_filter, Finset.sdiff_eq_filter ];
  simp_all +decide [ and_comm, and_left_comm, and_assoc ];
  have := hdense x; unfold allowedColourDegree at this; omega;

/-
At a fixed remaining source, one previously chosen source-target pair forbids at most three
candidate pairs: one through its target and two through its colour.
-/
lemma completion_conflict_card_le_three
    (n : ℕ) (colour : Sym2 (Fin (2 * n + 1)) → Fin n)
    (X V : Finset (Fin (2 * n + 1))) (htwo : IsTwoFactorization n colour)
    (hXV : Disjoint X V) (x : Fin (2 * n + 1)) (hx : x ∈ X)
    (A : Finset (Fin (2 * n + 1))) (hA : A ⊆ V)
    (p : Fin (2 * n + 1) × Fin (2 * n + 1)) :
    ((A.image (fun v => (x, v))).filter (fun q =>
      q.2 = p.2 ∨ colour s(q.1, q.2) = colour s(p.1, p.2))).card ≤ 3 := by
  by_cases h : p.2 ∈ A <;> simp_all +decide [ Finset.filter_image ];
  · have h_filter : (Finset.filter (fun a => colour s(x, a) = colour s(p.1, p.2)) A).card ≤ 2 := by
      convert vertex_colour_degree_le_two n colour X V htwo hXV x hx ( colour s(p.1, p.2) ) |> le_trans ( Finset.card_mono <| show Finset.filter ( fun a => colour s(x, a) = colour s(p.1, p.2) ) A ⊆ Finset.filter ( fun a => colour s(x, a) = colour s(p.1, p.2) ) V from Finset.filter_subset_filter _ hA ) using 1;
    rw [ Finset.card_image_of_injective _ fun a b h => by injection h ] ; simp_all +decide [ Finset.filter_eq', Finset.filter_or ] ;
    grind +revert;
  · rw [ Finset.card_image_of_injective _ fun a b h => by injection h ];
    have := vertex_colour_degree_le_two n colour X V htwo hXV x hx ( colour s(p.1, p.2) ) ; simp_all +decide [ Finset.filter_eq', Finset.filter_or ] ;
    exact le_trans ( Finset.card_le_card ( Finset.filter_subset_filter _ hA ) ) ( by linarith )

/-
Complete a prescribed vertex-disjoint colour matching using a dense allowed-colour set.
-/
lemma extend_prescribed_colour_matching
    (n : ℕ) (colour : Sym2 (Fin (2 * n + 1)) → Fin n)
    (X V : Finset (Fin (2 * n + 1))) (C C' : Finset (Fin n))
    (htwo : IsTwoFactorization n colour) (hXV : Disjoint X V)
    (edge : (c : Fin n) → c ∈ C' → (Fin (2 * n + 1) × Fin (2 * n + 1)))
    (hedge_mem : ∀ c hc, edge c hc ∈ X ×ˢ V)
    (hedge_colour : ∀ c hc, colour s((edge c hc).1, (edge c hc).2) = c)
    (hedge_disjoint : ∀ c hc d hd, c ≠ d →
      (edge c hc).1 ≠ (edge d hd).1 ∧ (edge c hc).2 ≠ (edge d hd).2)
    (hdense : ∀ x : Fin (2 * n + 1),
      3 * X.card ≤ allowedColourDegree colour C V x) :
    ∃ D : Finset (Fin n),
      C' ⊆ D ∧ D ⊆ C' ∪ C ∧ Nonempty (PerfectRainbowMatching colour X V D) := by
  -- Define XP, VP, and R as in the provided solution.
  set XP := Finset.image (fun c : C' => (edge c.1 c.2).1) Finset.univ
  set VP := Finset.image (fun c : C' => (edge c.1 c.2).2) Finset.univ
  set R := X \ XP;
  obtain ⟨choosePair, hchoosePair⟩ : ∃ choosePair : (x : Fin (2 * n + 1)) → x ∈ R → Fin (2 * n + 1),
    (∀ x hx, choosePair x hx ∈ V \ VP ∧ colour s(x, choosePair x hx) ∈ C \ C') ∧
    (∀ x hx x' hx' (hxx' : x ≠ x'), choosePair x hx ≠ choosePair x' hx' ∧ colour s(x, choosePair x hx) ≠ colour s(x', choosePair x' hx')) := by
      have := @greedy_conflict_choice ( Fin ( 2 * n + 1 ) ) ( Fin ( 2 * n + 1 ) × Fin ( 2 * n + 1 ) );
      specialize this R (fun x => ((V \ VP).filter (fun v => colour s(x, v) ∈ C \ C')).image (fun v => (x, v))) (fun p q => p.2 = q.2 ∨ colour s(p.1, p.2) = colour s(q.1, q.2)) 3 (by norm_num) (by
      exact fun p q h => Or.imp ( fun h => h.symm ) ( fun h => h.symm ) h) (by
      intro x hx;
      rw [ Finset.card_image_of_injective _ fun a b h => by simpa using h ];
      convert remaining_candidate_card n colour X V C C' htwo hXV edge hedge_mem hedge_disjoint hdense x hx using 1) (by
      intro a ha b; specialize hdense a; specialize hdense; simp_all +decide [ Finset.card_image_of_injective, Function.Injective ] ;
      convert completion_conflict_card_le_three n colour X V htwo hXV a ( Finset.mem_sdiff.mp ha |>.1 ) ( Finset.filter ( fun v => colour s(a, v) ∈ C ∧ colour s(a, v) ∉ C' ) ( V \ VP ) ) ( Finset.filter_subset _ _ |> Finset.Subset.trans <| Finset.sdiff_subset ) b using 1;
      simp +decide [ eq_comm, Sym2.eq_swap ]);
      obtain ⟨ choose, hchoose₁, hchoose₂ ⟩ := this; use fun x hx => ( choose x hx ).2; simp_all +decide [ Finset.mem_image ] ;
      grind;
  refine' ⟨ Finset.image ( fun c : C' => colour s( ( edge c.1 c.2 ).1, ( edge c.1 c.2 ).2 ) ) Finset.univ ∪ Finset.image ( fun x : R => colour s(x.1, choosePair x.1 x.2) ) Finset.univ, _, _, _ ⟩;
  · intro c hc; by_cases h : c ∈ C' <;> simp_all +decide [ Finset.subset_iff ] ;
  · grind;
  · refine' ⟨ ⟨ fun x hx => if hx' : x ∈ XP then ( Classical.choose ( Finset.mem_image.mp hx' ) |> fun c => ( edge c.1 c.2 ).2 ) else choosePair x ( by aesop ), _, _, _, _ ⟩ ⟩;
    · grind;
    · grind +splitImp;
    · grind;
    · ext; simp [Finset.mem_image];
      grind +qlia

/-
**Colour cover (MPS §4, Lemma `colourcover`).**

In a 2-factorized `K_(2n+1)`, let `X` and `V` be disjoint.  Pair-repletion supplies a matching
using every prescribed colour in `C'`; the first numerical inequality ensures that deleting the
two endpoints of each previously selected edge cannot exhaust the next colour.  The remaining
vertices of `X` are then matched greedily with colours in `C`; the second inequality pays for at
most two forbidden edges per used colour and one per already used target.

The resulting perfect rainbow matching from all of `X` into `V` uses every colour of `C'` and no
colour outside `C' ∪ C`.
-/
theorem colourcover
    (n : ℕ) (colour : Sym2 (Fin (2 * n + 1)) → Fin n)
    (X V : Finset (Fin (2 * n + 1))) (C C' : Finset (Fin n)) (repletion : ℕ)
    (htwo : IsTwoFactorization n colour)
    (hXV : Disjoint X V)
    (hreplete : ColourPairReplete colour X V repletion)
    (hprescribed : 4 * C'.card ≤ repletion)
    (hdense : ∀ x : Fin (2 * n + 1),
      3 * X.card ≤ allowedColourDegree colour C V x) :
    ∃ D : Finset (Fin n),
      C' ⊆ D ∧ D ⊆ C' ∪ C ∧ Nonempty (PerfectRainbowMatching colour X V D) := by
  convert extend_prescribed_colour_matching n colour X V C C' htwo hXV _ _ _ _ hdense;
  exact ( prescribed_colour_matching n colour X V C' repletion htwo hXV hreplete hprescribed ) |> Classical.choose;
  · grind +qlia;
  · grind +qlia;
  · grind +suggestions

/-- ND-colouring specialization of `colourcover`. -/
theorem ndColourcover
    (n : ℕ) (hn : 0 < n)
    (X V : Finset (Fin (2 * n + 1))) (C C' : Finset (Fin n)) (repletion : ℕ)
    (hXV : Disjoint X V)
    (hreplete : ColourPairReplete (ndColouring n hn) X V repletion)
    (hprescribed : 4 * C'.card ≤ repletion)
    (hdense : ∀ x : Fin (2 * n + 1),
      3 * X.card ≤ allowedColourDegree (ndColouring n hn) C V x) :
    ∃ D : Finset (Fin n),
      C' ⊆ D ∧ D ⊆ C' ∪ C ∧
        Nonempty (PerfectRainbowMatching (ndColouring n hn) X V D) := by
  exact colourcover n (ndColouring n hn) X V C C' repletion
    (ndColouring_isTwoFactorization n hn) hXV hreplete hprescribed hdense

end Ringel