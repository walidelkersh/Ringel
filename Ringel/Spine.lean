/-
Copyright (c) 2026 Walid K. Elkersh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Walid K. Elkersh
-/
import Ringel.Statement
import Ringel.Primitives
import Mathlib.Data.Sym.Sym2
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Data.Set.Card
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Ringel.CaseA
import Ringel.CaseB
import Ringel.CaseC
import Ringel.CaseDivision
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic

/-!
# Proof spine for Ringel's Conjecture (Montgomery–Pokrovskiy–Sudakov)

The top-level architecture of `arXiv:2001.02665`, as a `sorry`-stubbed skeleton. The proof reduces
`Ringel.ringel_conjecture_large` (in `Ringel/Statement.lean`) to the **rainbow-copy** statement
`rainbow_copy_exists` (paper Theorem `Theorem_Ringel_proof`), via the cyclic-shift step
`decomp_of_rainbow_copy`. The rainbow statement is then split by `case_division` into Cases A, B, C.

Each leaf reduces into the per-section lemmas (to live in `Ringel/SectionN.lean`):
* Case A → finishing lemma A (§4),
* Case B → finishing lemma B (§5),
* Case C → `Theorem_case_C` (§6–§7),
* Cases A/B share the randomized near-embedding `nearembedagain` (§6).

**Note (cyclic / Kotzig form).** `decomp_of_rainbow_copy` builds the decomposition out of the
$2n+1$ cyclic shifts of a single rainbow copy. So what is actually proved for large $n$ is the
*cyclic* decomposition (Kotzig's form), which is strictly stronger than plain Ringel; plain Ringel
is the forgetful weakening. See the discussion after Theorem `main` in the paper.
-/

open SimpleGraph

namespace Ringel

/-- **Cyclic-shift step (Kotzig).** A rainbow copy of $T$ in the ND-colouring yields $2n+1$
pairwise edge-disjoint copies of $T$ covering $K_{2n+1}$ — taken as the cyclic shifts of the one
copy. Bridges the rainbow statement to the decomposition in `Statement.lean`. -/
theorem decomp_of_rainbow_copy {n : ℕ} {V : Type*} [Finite V]
    (T : SimpleGraph V) (hT : T.IsTree) (hn : T.edgeSet.ncard = n)
    (h : HasRainbowCopy n T) :
    ∃ f : Fin (2 * n + 1) → (V ↪ Fin (2 * n + 1)),
      Pairwise (fun i j => Disjoint (T.map (f i)).edgeSet (T.map (f j)).edgeSet) ∧
      ⨆ i, T.map (f i) = (⊤ : SimpleGraph (Fin (2 * n + 1))) := by
  rcases h with ⟨f0, h_inj⟩
  let addRightEmb {m : ℕ} (x : Fin (2 * m + 1)) : Fin (2 * m + 1) ↪ Fin (2 * m + 1) :=
    (Equiv.addRight x).toEmbedding
  let f : Fin (2 * n + 1) → V ↪ Fin (2 * n + 1) := fun i => f0.trans (addRightEmb i)
  use f
  cases n with
  | zero =>
    constructor
    · intro i j hij
      rw [Set.disjoint_iff]
      intro e ⟨h1, _⟩
      have : (T.map (f i)).edgeSet.ncard = 0 := by
        rw [SimpleGraph.edgeSet_map, Set.ncard_image_of_injective _ (f i).sym2Map.injective, hn]
      have hemt : (T.map (f i)).edgeSet = ∅ := by rw [← Set.ncard_eq_zero]; exact this
      rw [hemt] at h1
      exact h1
    · rw [← SimpleGraph.edgeSet_inj]
      have edgeSet_iSup : (⨆ i, T.map (f i)).edgeSet = ⋃ i, (T.map (f i)).edgeSet := by
        ext e'
        induction e' using Sym2.ind with | _ u v => simp [SimpleGraph.iSup_adj]
      rw [edgeSet_iSup]
      ext e
      simp only [Set.mem_iUnion, Set.mem_compl_iff, Sym2.mem_diagSet]
      constructor
      · rintro ⟨i, hi⟩
        have : (T.map (f i)).edgeSet.ncard = 0 := by
          rw [SimpleGraph.edgeSet_map, Set.ncard_image_of_injective _ (f i).sym2Map.injective, hn]
        have hemt : (T.map (f i)).edgeSet = ∅ := by rw [← Set.ncard_eq_zero]; exact this
        rw [hemt] at hi
        exact hi.elim
      · intro he
        have : (⊤ : SimpleGraph (Fin (2 * 0 + 1))).edgeSet.ncard = 0 := by
          have hc1 : (⊤ : SimpleGraph (Fin (2 * 0 + 1))).edgeSet.ncard =
              (⊤ : SimpleGraph (Fin (2 * 0 + 1))).edgeFinset.card := by
            simp [Set.ncard_eq_toFinset_card', SimpleGraph.edgeFinset]
          have hc2 : (⊤ : SimpleGraph (Fin (2 * 0 + 1))).edgeFinset.card = Nat.choose (2 * 0 + 1) 2 := by
            have h := SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Fin (2 * 0 + 1))
            have h_card : Fintype.card (Fin (2 * 0 + 1)) = 2 * 0 + 1 := Fintype.card_fin _
            rw [h_card] at h
            exact h
          rw [hc1, hc2]
          rfl
        have hemt : (⊤ : SimpleGraph (Fin 1)).edgeSet = ∅ := by rw [← Set.ncard_eq_zero]; exact this
        rw [hemt] at he
        exact he.elim
  | succ n' =>
    have hn_pos : 0 < n'.succ := Nat.zero_lt_succ _
    have h_inj' := h_inj hn_pos
    have h_pairwise : Pairwise (fun i j => Disjoint (T.map (f i)).edgeSet (T.map (f j)).edgeSet) := by
      intro i j hij
      rw [Set.disjoint_iff]
      rintro e ⟨h1, h2⟩
      rw [SimpleGraph.edgeSet_map] at h1 h2
      rcases h1 with ⟨e1, he1, rfl⟩
      rcases h2 with ⟨e2, he2, heq⟩
      have h_addRight_map : ∀ (e : Sym2 (Fin (2*n'.succ+1))) k,
          ndColouring n'.succ hn_pos (Sym2.map (fun x => x + k) e) = ndColouring n'.succ hn_pos e := by
        intro e k
        induction e using Sym2.ind with
        | _ u v => exact ndColouring_addRight n'.succ hn_pos u v k
      have h_comp1 : (f i).sym2Map e1 = Sym2.map (fun x => x + i) (Sym2.map f0 e1) := by
        change Sym2.map (f i) e1 = _
        rw [Sym2.map_map]; rfl
      have h_comp2 : (f j).sym2Map e2 = Sym2.map (fun x => x + j) (Sym2.map f0 e2) := by
        change Sym2.map (f j) e2 = _
        rw [Sym2.map_map]; rfl
      rw [h_comp1] at heq
      rw [h_comp2] at heq
      have hcol_eq : ndColouring n'.succ hn_pos (Sym2.map (fun x => x + i) (Sym2.map f0 e1)) =
                     ndColouring n'.succ hn_pos (Sym2.map (fun x => x + j) (Sym2.map f0 e2)) := by rw [heq]
      rw [h_addRight_map, h_addRight_map] at hcol_eq
      have he1_mapped : Sym2.map f0 e1 ∈ (T.map f0).edgeSet := by
        rw [SimpleGraph.edgeSet_map]
        exact Set.mem_image_of_mem _ he1
      have he2_mapped : Sym2.map f0 e2 ∈ (T.map f0).edgeSet := by
        rw [SimpleGraph.edgeSet_map]
        exact Set.mem_image_of_mem _ he2
      have h_e_eq : Sym2.map f0 e1 = Sym2.map f0 e2 := h_inj' he1_mapped he2_mapped hcol_eq
      rw [h_e_eq] at heq
      have h_not_diag : ¬(Sym2.map f0 e2).IsDiag := (T.map f0).not_isDiag_of_mem_edgeSet he2_mapped
      revert heq h_not_diag
      generalize Sym2.map f0 e2 = e_base
      intro heq h_not_diag
      induction e_base using Sym2.ind with
      | _ u v =>
        rw [Sym2.map_mk, Sym2.map_mk] at heq
        rw [Sym2.eq_iff] at heq
        rcases heq with ⟨h_u, h_v⟩ | ⟨h_u, h_v⟩
        · have : u + j = u + i := h_u
          have : j = i := add_left_cancel this
          have : i = j := this.symm
          contradiction
        · have h_u_mod : (i.val + i.val) % (2*n'.succ+1) = (j.val + j.val) % (2*n'.succ+1) := by
            have h_sum : (u + i) + (v + i) = (v + j) + (u + j) := by rw [h_u, h_v]
            have h_sum_cancel : i + i = j + j := by
              calc
                i + i = u + v + i + i - (u + v) := by abel
                _ = (u + i) + (v + i) - (u + v) := by abel
                _ = (v + j) + (u + j) - (u + v) := by rw [h_sum]
                _ = j + j := by abel
            exact congrArg Fin.val h_sum_cancel
          have eq2 : (i.val * 2) % (2*n'.succ+1) = (j.val * 2) % (2*n'.succ+1) := by
            have h_i_mul : i.val + i.val = i.val * 2 := by omega
            have h_j_mul : j.val + j.val = j.val * 2 := by omega
            rw [h_i_mul, h_j_mul] at h_u_mod
            exact h_u_mod
          have hc : Nat.gcd (2 * n'.succ + 1) 2 = 1 := by
            have h_coprime : Nat.Coprime (2 * n'.succ + 1) 2 := by rw [Nat.coprime_two_right]; simp
            exact h_coprime
          have h_eq_mod : i.val * 2 ≡ j.val * 2 [MOD 2*n'.succ+1] := eq2
          have h_mod : i.val ≡ j.val [MOD 2*n'.succ+1] := Nat.ModEq.cancel_right_of_coprime hc h_eq_mod
          have : i = j := Fin.ext (Nat.ModEq.eq_of_lt_of_lt h_mod i.isLt j.isLt)
          contradiction
    exact ⟨h_pairwise, by
      have edgeSet_iSup : (⨆ i, T.map (f i)).edgeSet = ⋃ i, (T.map (f i)).edgeSet := by
        ext e
        induction e using Sym2.ind with | _ u v => simp [SimpleGraph.iSup_adj]
      have h_sub : (⨆ i, T.map (f i)).edgeSet ⊆ (⊤ : SimpleGraph (Fin (2 * n'.succ + 1))).edgeSet := 
        SimpleGraph.edgeSet_subset_edgeSet.mpr le_top
      have h_card_top : (⊤ : SimpleGraph (Fin (2 * n'.succ + 1))).edgeSet.ncard = n'.succ * (2 * n'.succ + 1) := by
        have hc1 : (⊤ : SimpleGraph (Fin (2 * n'.succ + 1))).edgeSet.ncard =
            (⊤ : SimpleGraph (Fin (2 * n'.succ + 1))).edgeFinset.card := by
          simp [Set.ncard_eq_toFinset_card', SimpleGraph.edgeFinset]
        have hc2 : (⊤ : SimpleGraph (Fin (2 * n'.succ + 1))).edgeFinset.card = Nat.choose (2 * n'.succ + 1) 2 := by
          have h := SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Fin (2 * n'.succ + 1))
          have h_card : Fintype.card (Fin (2 * n'.succ + 1)) = 2 * n'.succ + 1 := Fintype.card_fin _
          rw [h_card] at h
          exact h
        rw [hc1, hc2]
        rw [Nat.choose_two_right]
        have h1 : 2 * n'.succ + 1 - 1 = 2 * n'.succ := by omega
        rw [h1]
        have h2 : (2 * n'.succ + 1) * (2 * n'.succ) =
            2 * (n'.succ * (2 * n'.succ + 1)) := by ring
        rw [h2]; omega
      have h_card_union : (⋃ i, (T.map (f i)).edgeSet).ncard = n'.succ * (2 * n'.succ + 1) := by
        have h_card_i : ∀ i, (T.map (f i)).edgeSet.ncard = n'.succ := by
          intro i
          rw [SimpleGraph.edgeSet_map, Set.ncard_image_of_injective _ (f i).sym2Map.injective, hn]
        have hs : ∀ i, (T.map (f i)).edgeSet.Finite := fun i => Set.toFinite _
        have h_sum : (⋃ i, (T.map (f i)).edgeSet).ncard = ∑ᶠ i : Fin (2 * n'.succ + 1), n'.succ := by
          have := Set.ncard_iUnion_of_finite hs h_pairwise
          rw [this]
          exact finsum_congr h_card_i
        rw [h_sum]
        have h_sum2 : (∑ᶠ i : Fin (2 * n'.succ + 1), n'.succ) =
            Nat.card (Fin (2 * n'.succ + 1)) * n'.succ := by
          rw [finsum_eq_sum_of_fintype]
          simp [Finset.sum_const, Nat.card_eq_fintype_card,
            Fintype.card_fin]
        have hcard : Nat.card (Fin (2 * n'.succ + 1)) = 2 * n'.succ + 1 := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]
        rw [h_sum2, hcard]; ring
      have hf : (⊤ : SimpleGraph (Fin (2 * n'.succ + 1))).edgeSet.Finite := Set.toFinite _
      have h_card_isup : (⨆ i, T.map (f i)).edgeSet.ncard = n'.succ * (2 * n'.succ + 1) := by
        rw [edgeSet_iSup, h_card_union]
      have h_eq : (⨆ i, T.map (f i)).edgeSet = (⊤ : SimpleGraph (Fin (2 * n'.succ + 1))).edgeSet :=
        Set.eq_of_subset_of_ncard_le h_sub
          (le_of_eq (h_card_top.trans h_card_isup.symm)) hf
      rw [← SimpleGraph.edgeSet_inj]
      exact h_eq⟩




/-- **Theorem `Theorem_Ringel_proof`.** For sufficiently large $n$, the ND-coloured $K_{2n+1}$
contains a rainbow copy of every $n$-edge tree. This is the heart of the MPS proof. -/
theorem rainbow_copy_exists :
    ∀ᶠ (n : ℕ) in Filter.atTop, ∀ {V : Type*} [Finite V] (T : SimpleGraph V),
      T.IsTree → T.edgeSet.ncard = n → HasRainbowCopy n T := by
  have hd : (0 : ℝ) < 1 / 4 := by norm_num
  have hd' : (1 / 4 : ℝ) ≤ 1 / 4 := le_refl _
  filter_upwards [
    case_division (1 / 4) hd hd',
    caseA_rainbow_eventually (1 / 4) hd,
    caseB_rainbow (1 / 4) hd,
    caseC_rainbow (1 / 4) hd
  ] with n hn_div hn_A hn_B hn_C
  intro V _ T hT hcard
  rcases hn_div T hT hcard with hA | hB | hC
  · by_cases hC2 : IsCaseC (1 / 4) n T
    · exact hn_C T hT hcard hC2
    · exact hn_A T hT hcard hA hC2
  · by_cases hC2 : IsCaseC (1 / 4) n T
    · exact hn_C T hT hcard hC2
    · exact hn_B T hT hcard hB hC2
  · exact hn_C T hT hcard hC

/-- `Statement.ringel_conjecture_large` follows from the spine: combine `rainbow_copy_exists` with
`decomp_of_rainbow_copy`. (Demonstrates the wiring; no new `sorry` beyond the two spine lemmas.) -/
theorem ringel_conjecture_large_via_spine :
    ∀ᶠ (n : ℕ) in Filter.atTop, ∀ {V : Type*} [Finite V] (T : SimpleGraph V),
      T.IsTree → T.edgeSet.ncard = n →
      ∃ f : Fin (2 * n + 1) → (V ↪ Fin (2 * n + 1)),
        Pairwise (fun i j => Disjoint (T.map (f i)).edgeSet (T.map (f j)).edgeSet) ∧
        ⨆ i, T.map (f i) = (⊤ : SimpleGraph (Fin (2 * n + 1))) := by
  filter_upwards [rainbow_copy_exists] with n hn
  intro V _ T hT hcard
  exact decomp_of_rainbow_copy T hT hcard (hn T hT hcard)

end Ringel
