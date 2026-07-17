import Ringel.Primitives
import Mathlib.Tactic

open SimpleGraph

namespace Ringel

def switchPathColours (n : ℕ) (hn : 0 < n) (p : Fin 8 → Fin (2 * n + 1)) : Finset (Fin n) :=
  Finset.univ.image fun i : Fin 7 => ndColouring n hn s(p i.castSucc, p i.succ)

def IsFreshLengthSevenPath (n : ℕ) (p : Fin 8 → Fin (2 * n + 1))
    (x y : Fin (2 * n + 1)) (X : Finset (Fin (2 * n + 1))) : Prop :=
  Function.Injective p ∧ p 0 = x ∧ p 7 = y ∧ ∀ i : Fin 8, i ≠ 0 → i ≠ 7 → p i ∉ X

def HasOneInTwoColourSwitcher (n : ℕ) (hn : 0 < n)
    (x y : Fin (2 * n + 1)) (c₁ c₂ : Fin n)
    (X : Finset (Fin (2 * n + 1))) (C : Finset (Fin n)) : Prop :=
  ∃ (D : Finset (Fin n)) (p₁ p₂ : Fin 8 → Fin (2 * n + 1)),
    D.card = 6 ∧
    Disjoint D (C ∪ {c₁, c₂}) ∧
    IsFreshLengthSevenPath n p₁ x y X ∧
    IsFreshLengthSevenPath n p₂ x y X ∧
    switchPathColours n hn p₁ = insert c₁ D ∧
    switchPathColours n hn p₂ = insert c₂ D

lemma exists_mem_not_mem_of_card_lt {α : Type*} [DecidableEq α]
    (available forbidden : Finset α) (hcard : forbidden.card < available.card) :
    ∃ a ∈ available, a ∉ forbidden := by
  exact Set.not_subset.mp fun h => hcard.not_ge <| Finset.card_le_card h

lemma exists_avoiding_bounded_fibres {α β : Type*} [DecidableEq α] [DecidableEq β]
    (available : Finset α) (bad : Finset β) (f : α → β) (k : ℕ)
    (hfibre : ∀ b ∈ bad, (available.filter fun a => f a = b).card ≤ k)
    (hcard : k * bad.card < available.card) :
    ∃ a ∈ available, f a ∉ bad := by
  contrapose! hcard;
  have h_union : available.card ≤ ∑ b ∈ bad, (Finset.filter (fun a => f a = b) available).card := by
    rw [ ← Finset.card_biUnion ] ; exact Finset.card_le_card fun x hx => by aesop;
    exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun a ha₁ ha₂ => hxy <| by aesop;
  exact h_union.trans ( by simpa [ mul_comm ] using Finset.sum_le_sum hfibre )

structure OneInTwoCandidate (n : ℕ) (hn : 0 < n)
    (x y : Fin (2 * n + 1)) (c₁ c₂ : Fin n) (C : Finset (Fin n)) where
  D : Finset (Fin n)
  p₁ : Fin 8 → Fin (2 * n + 1)
  p₂ : Fin 8 → Fin (2 * n + 1)
  D_card : D.card = 6
  D_fresh : Disjoint D (C ∪ {c₁, c₂})
  p₁_simple : Function.Injective p₁
  p₂_simple : Function.Injective p₂
  p₁_start : p₁ 0 = x
  p₂_start : p₂ 0 = x
  p₁_end : p₁ 7 = y
  p₂_end : p₂ 7 = y
  colours₁ : switchPathColours n hn p₁ = insert c₁ D
  colours₂ : switchPathColours n hn p₂ = insert c₂ D

def colourStep (n : ℕ) (c : Fin n) : Fin (2 * n + 1) :=
  ⟨c.val + 1, by omega⟩

lemma orient_colour_pair
    (n : ℕ) (hn : 0 < n) (c₁ c₂ : Fin n) (hc : c₁ ≠ c₂) :
    ∃ (swap : Bool) (k : Fin n),
      (if swap then colourStep n c₂ else colourStep n c₁) +
          2 • colourStep n k =
        (if swap then colourStep n c₁ else colourStep n c₂) := by
  by_cases h_cases : c₁.val < c₂.val;
  · simp_all +decide [ two_smul ];
    by_cases h_even : Even (c₂.val - c₁.val);
    · obtain ⟨ k, hk ⟩ := h_even;
      refine Or.inl ⟨ ⟨ k - 1, by omega ⟩, ?_ ⟩ ; simp +decide [ Fin.ext_iff, Fin.val_add, Fin.val_mul, colourStep ] ; ring;
      rw [ Nat.mod_eq_of_lt ] <;> omega;
    · refine' Or.inr ⟨ ⟨ ( 2 * n + 1 - ( c₂.val - c₁.val ) ) / 2 - 1, _ ⟩, _ ⟩ <;> norm_num [ colourStep ];
      grind;
      norm_num [ Fin.ext_iff, Fin.val_add, Fin.val_mul ];
      rw [ Nat.mod_eq_sub_mod ];
      · rw [ Nat.mod_eq_of_lt ];
        · grind;
        · omega;
      · omega;
  · cases le_iff_exists_add'.mp ( le_of_not_gt h_cases ) ; simp_all +decide [ Fin.add_def, two_smul, colourStep ];
    rename_i k hk;
    by_cases hk_even : Even k;
    · obtain ⟨ m, rfl ⟩ := hk_even;
      refine Or.inr ⟨ ⟨ m - 1, ?_ ⟩, ?_ ⟩ <;> norm_num;
      · omega;
      · rw [ Nat.mod_eq_of_lt ] <;> omega;
    · obtain ⟨ m, rfl ⟩ := Nat.odd_iff.mpr ( Nat.mod_two_ne_zero.mp fun h => hk_even <| even_iff_two_dvd.mpr <| Nat.dvd_of_mod_eq_zero h );
      refine Or.inl ⟨ ⟨ n - m - 1, ?_ ⟩, ?_ ⟩ <;> norm_num;
      · omega;
      · rw [ Nat.mod_eq_sub_mod ] <;> norm_num [ Nat.sub_sub ];
        · rw [ Nat.mod_eq_of_lt ] <;> omega;
        · omega

lemma oriented_two_edge_switch
    (n : ℕ) (hn : 0 < n) (a b k : Fin n)
    (hrel : colourStep n a + 2 • colourStep n k = colourStep n b)
    (z : Fin (2 * n + 1)) :
    let q₁ : Fin 3 → Fin (2 * n + 1) := ![z, z + colourStep n a,
      z + colourStep n a + colourStep n k]
    let q₂ : Fin 3 → Fin (2 * n + 1) := ![z, z - colourStep n k,
      z - colourStep n k + colourStep n b]
    q₁ 0 = q₂ 0 ∧ q₁ 2 = q₂ 2 ∧
      switchPathColours n hn (fun i : Fin 8 => q₁ ⟨i.val % 3, by omega⟩) ⊇ {a, k} ∧
      switchPathColours n hn (fun i : Fin 8 => q₂ ⟨i.val % 3, by omega⟩) ⊇ {b, k} := by
  refine' ⟨ _, _, _, _ ⟩;
  · rfl;
  · simp +decide [ ← hrel, two_smul ];
    grind;
  · simp +decide [ Finset.subset_iff, switchPathColours ];
    refine' ⟨ ⟨ 0, _ ⟩, ⟨ 1, _ ⟩ ⟩ <;> simp +decide [ ndColouring_step ];
    · convert ndColouring_step n hn z ( colourStep n a ) a _ using 1 ; simp +decide [ colourStep ];
    · convert ndColouring_step n hn ( z + colourStep n a ) ( colourStep n k ) k _ using 1;
      exact Or.inl rfl;
  · intro c hc; simp_all +decide [ Finset.subset_iff, switchPathColours ] ;
    rcases hc with ( rfl | rfl ) <;> [ refine' ⟨ 1, _ ⟩ ; refine' ⟨ 0, _ ⟩ ] <;> simp +decide [ *, ndColouring_step ];
    · convert ndColouring_step n hn ( z - colourStep n k ) ( colourStep n c ) c _ using 1 ; norm_num [ colourStep ];
    · convert ndColouring_step n hn z ( -colourStep n c ) c _ using 1;
      · norm_num [ sub_eq_add_neg ];
      · norm_num [ Fin.val_neg', colourStep ]

set_option maxHeartbeats 2000000 in
lemma switcher_template_correct
    (n : ℕ) (hn : 0 < n) (x y : Fin (2 * n + 1))
    (a b i e d₁ d₂ d₃ d₄ : Fin n)
    (hk : colourStep n a + 2 •
      (colourStep n d₁ + colourStep n d₂ - colourStep n d₃ - colourStep n d₄) =
      colourStep n b)
    (hend : x + colourStep n i + colourStep n a + colourStep n d₁ + colourStep n d₂ -
      colourStep n d₃ - colourStep n d₄ + colourStep n e = y) :
    let p₁ : Fin 8 → Fin (2 * n + 1) := ![
      x,
      x + colourStep n i,
      x + colourStep n i + colourStep n a,
      x + colourStep n i + colourStep n a + colourStep n d₁,
      x + colourStep n i + colourStep n a + colourStep n d₁ + colourStep n d₂,
      x + colourStep n i + colourStep n a + colourStep n d₁ + colourStep n d₂ - colourStep n d₃,
      x + colourStep n i + colourStep n a + colourStep n d₁ + colourStep n d₂ - colourStep n d₃ - colourStep n d₄,
      y]
    let p₂ : Fin 8 → Fin (2 * n + 1) := ![
      x,
      x + colourStep n i,
      x + colourStep n i + colourStep n b,
      x + colourStep n i + colourStep n b + colourStep n d₄,
      x + colourStep n i + colourStep n b + colourStep n d₄ + colourStep n d₃,
      x + colourStep n i + colourStep n b + colourStep n d₄ + colourStep n d₃ - colourStep n d₂,
      x + colourStep n i + colourStep n b + colourStep n d₄ + colourStep n d₃ - colourStep n d₂ - colourStep n d₁,
      y]
    p₁ 0 = x ∧ p₁ 7 = y ∧ p₂ 0 = x ∧ p₂ 7 = y ∧
    switchPathColours n hn p₁ = {i, a, d₁, d₂, d₃, d₄, e} ∧
    switchPathColours n hn p₂ = {i, b, d₁, d₂, d₃, d₄, e} := by
  refine' ⟨ rfl, rfl, rfl, rfl, _, _ ⟩;
  · unfold switchPathColours; simp +decide [ Finset.ext_iff ] ;
    intro c; constructor <;> intro hc; simp_all +decide [ Fin.exists_fin_succ ] ;
    · rcases hc with ( hc | hc | hc | hc | hc | hc | hc ) <;> rw [ ← hc ];
      exact Or.inl <| ndColouring_step n hn x ( colourStep n i ) i <| Or.inl rfl;
      exact Or.inr <| Or.inl <| ndColouring_step n hn ( x + colourStep n i ) ( colourStep n a ) a <| Or.inl rfl;
      · exact Or.inr <| Or.inr <| Or.inl <| ndColouring_step n hn ( x + colourStep n i + colourStep n a ) ( colourStep n d₁ ) d₁ <| Or.inl rfl;
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inl <| ndColouring_step n hn ( x + colourStep n i + colourStep n a + colourStep n d₁ ) ( colourStep n d₂ ) d₂ <| Or.inl rfl;
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| by rw [ show s(x + colourStep n i + colourStep n a + colourStep n d₁ + colourStep n d₂, x + colourStep n i + colourStep n a + colourStep n d₁ + colourStep n d₂ - colourStep n d₃) = s(x + colourStep n i + colourStep n a + colourStep n d₁ + colourStep n d₂ - colourStep n d₃, (x + colourStep n i + colourStep n a + colourStep n d₁ + colourStep n d₂ - colourStep n d₃) + colourStep n d₃) by simp +decide [ Sym2.eq_swap ] ] ; exact ndColouring_step n hn _ _ _ <| Or.inl rfl;
      · rw [ show s(x + colourStep n i + colourStep n a + colourStep n d₁ + colourStep n d₂ - colourStep n d₃, x + colourStep n i + colourStep n a + colourStep n d₁ + colourStep n d₂ - colourStep n d₃ - colourStep n d₄) = s(x + colourStep n i + colourStep n a + colourStep n d₁ + colourStep n d₂ - colourStep n d₃ - colourStep n d₄, (x + colourStep n i + colourStep n a + colourStep n d₁ + colourStep n d₂ - colourStep n d₃ - colourStep n d₄) + colourStep n d₄) by simp +decide [ Sym2.eq_swap ] ] ; exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| ndColouring_step n hn _ _ _ <| Or.inl rfl;
      · rw [ ← hend ];
        exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| ndColouring_step n hn _ _ _ <| Or.inl rfl;
    · rcases hc with ( rfl | rfl | rfl | rfl | rfl | rfl | rfl );
      exact ⟨ 0, ndColouring_step n hn x ( colourStep n c ) c ( Or.inl rfl ) ⟩;
      exact ⟨ 1, ndColouring_step n hn ( x + colourStep n i ) ( colourStep n c ) c ( Or.inl rfl ) ⟩;
      · use 2; simp +decide [ ndColouring_step ] ;
        convert ndColouring_step n hn ( x + colourStep n i + colourStep n a ) ( colourStep n c ) c _ using 1 ; norm_num [ colourStep ];
      · use 3; simp +decide [ ndColouring_step ] ;
        convert ndColouring_step n hn ( x + colourStep n i + colourStep n a + colourStep n d₁ ) ( colourStep n c ) c _ using 1 ; norm_num [ colourStep ];
      · use 4; simp +decide [ ndColouring_step ] ;
        convert ndColouring_step n hn ( x + colourStep n i + colourStep n a + colourStep n d₁ + colourStep n d₂ - colourStep n c ) ( colourStep n c ) c _ using 1;
        · simp +decide [ Sym2.eq_swap ];
        · exact Or.inl rfl;
      · use 5; simp +decide [ ndColouring_step ] ;
        convert ndColouring_step n hn ( x + colourStep n i + colourStep n a + colourStep n d₁ + colourStep n d₂ - colourStep n d₃ - colourStep n c ) ( colourStep n c ) c _ using 1;
        · simp +decide [ Sym2.eq_swap ];
        · exact Or.inl rfl;
      · use 6; simp +decide [ ← hend ] ;
        convert ndColouring_step n hn ( x + colourStep n i + colourStep n a + colourStep n d₁ + colourStep n d₂ - colourStep n d₃ - colourStep n d₄ ) ( colourStep n c ) c ( Or.inl rfl ) using 1;
  · refine' ( Finset.eq_of_subset_of_card_le _ _ );
    · simp +decide [ Finset.subset_iff, switchPathColours ];
      intro a; fin_cases a <;> simp +decide [ *, ndColouring_step ] ;
      exact Or.inl <| ndColouring_step n hn x ( colourStep n i ) i ( Or.inl rfl );
      exact Or.inr <| Or.inl <| ndColouring_step n hn ( x + colourStep n i ) ( colourStep n b ) b ( Or.inl rfl );
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| ndColouring_step n hn ( x + colourStep n i + colourStep n b ) ( colourStep n d₄ ) d₄ ( Or.inl rfl );
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| ndColouring_step n hn ( x + colourStep n i + colourStep n b + colourStep n d₄ ) ( colourStep n d₃ ) d₃ ( Or.inl rfl );
      · rw [ show s(x + colourStep n i + colourStep n b + colourStep n d₄ + colourStep n d₃, x + colourStep n i + colourStep n b + colourStep n d₄ + colourStep n d₃ - colourStep n d₂) = s(x + colourStep n i + colourStep n b + colourStep n d₄ + colourStep n d₃ - colourStep n d₂, (x + colourStep n i + colourStep n b + colourStep n d₄ + colourStep n d₃ - colourStep n d₂) + colourStep n d₂) by simp +decide [ Sym2.eq_swap ] ] ; simp +decide [ *, ndColouring_step ] ;
        exact Or.inr <| Or.inr <| Or.inr <| Or.inl <| by rw [ show s(x + colourStep n i + colourStep n b + colourStep n d₄ + colourStep n d₃ - colourStep n d₂, x + colourStep n i + colourStep n b + colourStep n d₄ + colourStep n d₃) = s(x + colourStep n i + colourStep n b + colourStep n d₄ + colourStep n d₃ - colourStep n d₂, (x + colourStep n i + colourStep n b + colourStep n d₄ + colourStep n d₃ - colourStep n d₂) + colourStep n d₂) by simp +decide [ Sym2.eq_swap ] ] ; exact ndColouring_step n hn _ _ _ ( Or.inl rfl ) ;
      · rw [ show s(x + colourStep n i + colourStep n b + colourStep n d₄ + colourStep n d₃ - colourStep n d₂, x + colourStep n i + colourStep n b + colourStep n d₄ + colourStep n d₃ - colourStep n d₂ - colourStep n d₁) = s(x + colourStep n i + colourStep n b + colourStep n d₄ + colourStep n d₃ - colourStep n d₂ - colourStep n d₁, x + colourStep n i + colourStep n b + colourStep n d₄ + colourStep n d₃ - colourStep n d₂) by simp +decide [ Sym2.eq_swap ] ] ; exact Or.inr <| Or.inr <| Or.inl <| by
              convert ndColouring_step n hn ( x + colourStep n i + colourStep n b + colourStep n d₄ + colourStep n d₃ - colourStep n d₂ - colourStep n d₁ ) ( colourStep n d₁ ) d₁ _ using 1 ; norm_num [ colourStep ];
              exact Or.inl rfl;
      · convert Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| ndColouring_step n hn _ _ _ _ using 1;
        congr! 1;
        congr! 1;
        congr! 1;
        congr! 1;
        congr! 1;
        congr! 1;
        rotate_left;
        exact x + colourStep n i + colourStep n a + colourStep n d₁ + colourStep n d₂ - colourStep n d₃ - colourStep n d₄;
        exact colourStep n e;
        · exact Or.inl rfl;
        · rw [ ← hend ];
          rw [ ← hk ] ; ring;
          norm_num [ two_smul, add_assoc, add_sub_assoc ];
    · refine' le_trans _ ( Finset.card_mono _ );
      rotate_left;
      exact { i, b, d₄, d₃, d₂, d₁, e };
      · simp +decide [ Finset.subset_iff, switchPathColours ];
        refine' ⟨ ⟨ 0, _ ⟩, ⟨ 1, _ ⟩, ⟨ 2, _ ⟩, ⟨ 3, _ ⟩, ⟨ 4, _ ⟩, ⟨ 5, _ ⟩, ⟨ 6, _ ⟩ ⟩ <;> simp +decide [ ndColouring_step ];
        exact ndColouring_step n hn x ( colourStep n i ) i ( Or.inl rfl );
        exact ndColouring_step n hn ( x + colourStep n i ) ( colourStep n b ) b ( Or.inl rfl );
        · convert ndColouring_step n hn ( x + colourStep n i + colourStep n b ) ( colourStep n d₄ ) d₄ _ using 1 ; norm_num [ colourStep ];
        · convert ndColouring_step n hn ( x + colourStep n i + colourStep n b + colourStep n d₄ ) ( colourStep n d₃ ) d₃ _ using 1 ; norm_num [ colourStep ];
        · convert ndColouring_step n hn ( x + colourStep n i + colourStep n b + colourStep n d₄ + colourStep n d₃ - colourStep n d₂ ) ( colourStep n d₂ ) d₂ _ using 1;
          · simp +decide [ Sym2.eq_swap ];
          · exact Or.inl rfl;
        · convert ndColouring_step n hn ( x + colourStep n i + colourStep n b + colourStep n d₄ + colourStep n d₃ - colourStep n d₂ - colourStep n d₁ ) ( colourStep n d₁ ) d₁ _ using 1 ; norm_num [ colourStep ];
          · grind +splitIndPred;
          · exact Or.inl rfl;
        · convert ndColouring_step n hn ( x + colourStep n i + colourStep n a + colourStep n d₁ + colourStep n d₂ - colourStep n d₃ - colourStep n d₄ ) ( colourStep n e ) e _ using 1;
          · rw [ ← hend ];
            rw [ ← hk ] ; ring;
            norm_num [ two_smul, add_assoc, add_sub_assoc ];
          · exact Or.inl rfl;
      · simp +decide [ Finset.insert_comm, Finset.insert_subset_iff ]

def IsGoodDetour (n : ℕ) (a b k d₁ d₂ d₃ d₄ : Fin n) : Prop :=
  colourStep n d₁ + colourStep n d₂ - colourStep n d₃ - colourStep n d₄ =
      colourStep n k ∧
  Function.Injective (![0,
    colourStep n a,
    colourStep n a + colourStep n d₁,
    colourStep n a + colourStep n d₁ + colourStep n d₂,
    colourStep n a + colourStep n d₁ + colourStep n d₂ - colourStep n d₃,
    colourStep n a + colourStep n d₁ + colourStep n d₂ - colourStep n d₃ - colourStep n d₄] :
      Fin 6 → Fin (2 * n + 1)) ∧
  Function.Injective (![0,
    colourStep n b,
    colourStep n b + colourStep n d₄,
    colourStep n b + colourStep n d₄ + colourStep n d₃,
    colourStep n b + colourStep n d₄ + colourStep n d₃ - colourStep n d₂,
    colourStep n b + colourStep n d₄ + colourStep n d₃ - colourStep n d₂ - colourStep n d₁] :
      Fin 6 → Fin (2 * n + 1))

theorem caseB_one_in_two_colour_switcher_large_of_family
    (n : ℕ) (hn : 500 ≤ n)
    (x y : Fin (2 * n + 1)) (hxy : x ≠ y)
    (c₁ c₂ : Fin n) (hc : c₁ ≠ c₂)
    (X : Finset (Fin (2 * n + 1))) (C : Finset (Fin n))
    (hX : X.card ≤ n / 25) (hC : C.card ≤ n / 25)
    (hfamily : ∃ (ι : Type) (_ : Fintype ι)
      (cand : ι → OneInTwoCandidate n (by omega) x y c₁ c₂ C),
      n / 2 < Fintype.card ι ∧
      ∀ v : Fin (2 * n + 1),
        Fintype.card {i : ι //
          (∃ j : Fin 8, j ≠ 0 ∧ j ≠ 7 ∧ (cand i).p₁ j = v) ∨
          (∃ j : Fin 8, j ≠ 0 ∧ j ≠ 7 ∧ (cand i).p₂ j = v)} ≤ 12) :
    HasOneInTwoColourSwitcher n (by omega) x y c₁ c₂ X C := by
  obtain ⟨ι, hι⟩ := hfamily
  obtain ⟨ _, cand, hι₁, hι₂ ⟩ := hι;
  have h_bad_card : (Finset.filter (fun i => ∃ v ∈ X, (∃ j : Fin 8, j ≠ 0 ∧ j ≠ 7 ∧ (cand i).p₁ j = v) ∨ (∃ j : Fin 8, j ≠ 0 ∧ j ≠ 7 ∧ (cand i).p₂ j = v)) Finset.univ).card ≤ 12 * X.card := by
    have h_bad_card : (Finset.filter (fun i => ∃ v ∈ X, (∃ j : Fin 8, j ≠ 0 ∧ j ≠ 7 ∧ (cand i).p₁ j = v) ∨ (∃ j : Fin 8, j ≠ 0 ∧ j ≠ 7 ∧ (cand i).p₂ j = v)) Finset.univ).card ≤ ∑ v ∈ X, (Finset.filter (fun i => (∃ j : Fin 8, j ≠ 0 ∧ j ≠ 7 ∧ (cand i).p₁ j = v) ∨ (∃ j : Fin 8, j ≠ 0 ∧ j ≠ 7 ∧ (cand i).p₂ j = v)) Finset.univ).card := by
      convert Finset.card_biUnion_le using 1;
      congr with i ; simp +decide [ Finset.mem_biUnion ];
      exact Classical.decEq ι;
    refine le_trans h_bad_card ?_;
    exact le_trans ( Finset.sum_le_sum fun _ _ => show Finset.card _ ≤ 12 from by simpa [ Fintype.card_subtype ] using hι₂ _ ) ( by simp +decide [ mul_comm ] );
  obtain ⟨i, hi⟩ : ∃ i : ι, ¬∃ v ∈ X, (∃ j : Fin 8, j ≠ 0 ∧ j ≠ 7 ∧ (cand i).p₁ j = v) ∨ (∃ j : Fin 8, j ≠ 0 ∧ j ≠ 7 ∧ (cand i).p₂ j = v) := by
    contrapose! hι₁;
    rw [ Finset.filter_true_of_mem fun i _ => hι₁ i ] at h_bad_card ; norm_num at h_bad_card ; omega;
  use (cand i).D, (cand i).p₁, (cand i).p₂;
  simp_all +decide [ IsFreshLengthSevenPath ];
  have := ( cand i ).D_fresh; simp_all +decide [ Finset.disjoint_left ] ;
  exact ⟨ ( cand i ).D_card, ⟨ fun h => this h |>.1 rfl, fun h => this h |>.2.1 rfl ⟩, ⟨ ( cand i ).p₁_simple, ( cand i ).p₁_start, ( cand i ).p₁_end, fun j hj₁ hj₂ => fun hj₃ => hi _ hj₃ |>.1 _ hj₁ hj₂ rfl ⟩, ⟨ ( cand i ).p₂_simple, ( cand i ).p₂_start, ( cand i ).p₂_end, fun j hj₁ hj₂ => fun hj₃ => hi _ hj₃ |>.2 _ hj₁ hj₂ rfl ⟩, ( cand i ).colours₁, ( cand i ).colours₂ ⟩

end Ringel
