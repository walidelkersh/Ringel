/-
Copyright (c) 2026 Walid K. Elkersh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Walid K. Elkersh
-/
import Ringel.Primitives
import Ringel.SmallTree
import Ringel.CaseCAssembly

/-!
# Case C with many high-degree vertices (`Theorem_case_C`, MPS §7)

Main theorem `caseC_many_vertex`: a tree `T` on `n+1` vertices consisting of a small
core (at most `n/100` vertices) with pendant leaves, where every leaf-bearing core
vertex carries at least `t` leaves and at most `2n/3`, has a rainbow copy in the
ND-coloured `K_{2n+1}` — for `t ≥ 4000(2k+1)` where `n < 2^(k-1)` (so `t = O(log n)`;
the paper uses `log⁴ n`, which our sharper doubling invariant improves).

Strategy: embed the core by `small_tree_into_intervals_idx` — leaf-bearing vertices
split into a side `V₁` (colour-heavy, in blocks at `0.7n`) and a side `V₂` (in blocks
at `0.91n`), the rest of the core (`V₀`) in the interval `[0.83n, 0.9n)` — and then
attach the leaves by explicit position arithmetic (`extend_rainbow_leaves`): the
`a`-th leaf of the label-`λ` vertex receives the colour at index `o λ + a` of the
ascending list of colours unused by the core, and sits at `u ∓ (c+1)` (type 1 vertices
attach downwards into `[.., u₁)`, type 2 upwards into `(u_max, 0.82n]`, type 3 upwards
into `[0.96n, 1.92n]`).
-/

open SimpleGraph

namespace Ringel

/-- Non-wrapping cyclic intervals are just ranges of values. -/
lemma mem_cyclicInterval_of_no_wrap {n : ℕ} {a : Fin (2 * n + 1)} {len : ℕ}
    (hnw : a.val + len ≤ 2 * n + 1) {u : Fin (2 * n + 1)} :
    u ∈ cyclicInterval n a len ↔ a.val ≤ u.val ∧ u.val < a.val + len := by
  rw [mem_cyclicInterval]
  constructor
  · rintro ⟨j, hj, rfl⟩
    rw [cyclicShift_val, Nat.mod_eq_of_lt (by omega)]
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨u.val - a.val, by omega, ?_⟩
    apply Fin.ext
    rw [cyclicShift_val, show a.val + (u.val - a.val) = u.val by omega,
      Nat.mod_eq_of_lt u.isLt]

/-- Non-wrapping cyclic intervals with separated ranges are disjoint. -/
lemma disjoint_cyclicInterval_of_no_wrap {n : ℕ} {a b : Fin (2 * n + 1)} {la lb : ℕ}
    (ha : a.val + la ≤ 2 * n + 1) (hb : b.val + lb ≤ 2 * n + 1)
    (hab : a.val + la ≤ b.val ∨ b.val + lb ≤ a.val) :
    Disjoint (cyclicInterval n a la) (cyclicInterval n b lb) := by
  rw [Finset.disjoint_left]
  intro u hua hub
  rw [mem_cyclicInterval_of_no_wrap ha] at hua
  rw [mem_cyclicInterval_of_no_wrap hb] at hub
  omega

/-- Values along the sorted list of a subset `D ⊆ Fin n` exceed their index by at most
the number of missing values: `ds[i] ≤ i + (n - |D|)`.  (Among the `ds[i]` values
`0, …, ds[i]`, exactly `i` smaller ones are in `D`, so at least `ds[i] - i` are
missing.) -/
lemma sort_val_le_index_add {n : ℕ} (D : Finset (Fin n)) {i : ℕ}
    (hi : i < (D.sort (· ≤ ·)).length) :
    ((D.sort (· ≤ ·))[i]'hi).val ≤ i + (n - D.card) := by
  classical
  set ds := D.sort (· ≤ ·) with hds
  have hsorted : ds.Pairwise (· < ·) := (Finset.sortedLT_sort D).pairwise
  set c := ds[i]'hi with hc
  have hDlt : Finset.Iio c ∩ D ⊆ (Finset.range i).image (fun j => ds.getD j c) := by
    intro x hx
    rw [Finset.mem_inter, Finset.mem_Iio] at hx
    obtain ⟨j, hj, hjx⟩ := List.mem_iff_getElem.mp
      ((Finset.mem_sort (r := (· ≤ ·))).mpr hx.2)
    have hxval : (ds[j]'hj).val = x.val := congrArg Fin.val hjx
    have hcval : x.val < c.val := hx.1
    have hji : j < i := by
      by_contra hge
      have hmono := sorted_val_add_index_le hsorted (show i ≤ j by omega) hj
      omega
    refine Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hji, ?_⟩
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact hjx
  have hcard1 : (Finset.Iio c ∩ D).card ≤ i :=
    le_trans (Finset.card_le_card hDlt)
      (le_trans Finset.card_image_le (le_of_eq (Finset.card_range i)))
  have hcard2 : (Finset.Iio c ∩ Dᶜ).card ≤ n - D.card := by
    refine le_trans (Finset.card_le_card Finset.inter_subset_right) ?_
    rw [Finset.card_compl, Fintype.card_fin]
  have hsplit : Finset.Iio c ∩ D ∪ Finset.Iio c ∩ Dᶜ = Finset.Iio c := by
    rw [← Finset.inter_union_distrib_left, Finset.union_compl, Finset.inter_univ]
  have hdisj : Disjoint (Finset.Iio c ∩ D) (Finset.Iio c ∩ Dᶜ) :=
    Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right disjoint_compl_right)
  have hIio : (Finset.Iio c).card = c.val := by
    rw [Fin.card_Iio]
  have hcards : (Finset.Iio c ∩ D).card + (Finset.Iio c ∩ Dᶜ).card = c.val := by
    rw [← Finset.card_union_of_disjoint hdisj, hsplit, hIio]
  omega

/-- The pendant leaves attached to the core vertex `u`. -/
private def leafSet {V : Type*} [Fintype V] [DecidableEq V] (core : Finset V)
    (anchor : V → V) (u : V) : Finset V :=
  Finset.univ.filter (fun v => v ∉ core ∧ anchor v = u)

private lemma mem_leafSet {V : Type*} [Fintype V] [DecidableEq V] {core : Finset V}
    {anchor : V → V} {u v : V} :
    v ∈ leafSet core anchor u ↔ v ∉ core ∧ anchor v = u := by
  simp [leafSet]

/-- The leaves partition the complement of the core (each leaf lies in the fibre of
its anchor). -/
private lemma sum_leafSet_card {V : Type*} [Fintype V] [DecidableEq V]
    (core : Finset V) (anchor : V → V)
    (hanchor : ∀ v, v ∉ core → anchor v ∈ core) :
    (Finset.univ.filter (fun v => v ∉ core)).card
      = ∑ u ∈ core, (leafSet core anchor u).card := by
  rw [Finset.card_eq_sum_card_fiberwise
    (f := anchor) (t := core) (fun v hv => hanchor v (Finset.mem_filter.mp hv).2)]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  congr 1
  ext v
  simp only [leafSet, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Cardinality of a subtype filter: for `S ⊆ core`, the elements of the subtype
`↥core` whose value lies in `S` number exactly `|S|`. -/
private lemma card_filter_subtype_eq {V : Type*} [DecidableEq V]
    (core S : Finset V) (hS : S ⊆ core) :
    (Finset.univ.filter (fun v : (core : Set V) => (v : V) ∈ S)).card = S.card := by
  refine Finset.card_bij (fun a _ => (a : V)) ?_ ?_ ?_
  · intro a ha
    exact (Finset.mem_filter.mp ha).2
  · intro a _ b _ hab
    exact Subtype.ext hab
  · intro b hb
    exact ⟨⟨b, Finset.mem_coe.mpr (hS hb)⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩, rfl⟩

/-- The colours realized by the core edges under the embedding `g`. -/
private def coreCols {n : ℕ} (hn0 : 0 < n) {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (core : Finset V) (g : V → Fin (2 * n + 1)) :
    Finset (Fin n) :=
  (Finset.univ.filter (fun e : Sym2 V => e ∈ T.edgeFinset ∩ core.sym2)).image
    (fun e => ndColouring n hn0 (Sym2.map g e))

/-- The number of core colours is at most `|core| - 1`: each colour comes from a core edge
of the induced forest, and a forest on `core` has at most `|core| - 1` edges. -/
private lemma card_coreCols_le {n : ℕ} (hn0 : 0 < n) {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hac : T.IsAcyclic) (core : Finset V)
    (hne : core.Nonempty) (g : V → Fin (2 * n + 1)) :
    (coreCols hn0 T core g).card + 1 ≤ core.card := by
  have hle : (coreCols hn0 T core g).card ≤ (T.edgeFinset ∩ core.sym2).card := by
    rw [coreCols]
    refine le_trans Finset.card_image_le ?_
    apply le_of_eq
    congr 1
    ext e
    simp
  have hforest := card_edges_in_subset_lt T hac core hne
  omega

/-- The colours **not** used by the core edges — the pool available for the leaf edges. -/
private def freeCols {n : ℕ} (hn0 : 0 < n) {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (core : Finset V) (g : V → Fin (2 * n + 1)) :
    Finset (Fin n) :=
  Finset.univ \ coreCols hn0 T core g

/-- The free-colour pool is large enough to receive one colour per leaf: its size is at
least `n + 1 - |core|`, which equals the number of leaves. -/
private lemma card_freeCols_ge {n : ℕ} (hn0 : 0 < n) {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hac : T.IsAcyclic) (core : Finset V)
    (hne : core.Nonempty) (g : V → Fin (2 * n + 1)) :
    n + 1 ≤ (freeCols hn0 T core g).card + core.card := by
  have hc : (freeCols hn0 T core g).card = n - (coreCols hn0 T core g).card := by
    rw [freeCols, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
  have hb := card_coreCols_le hn0 T hac core hne g
  have hcle : (coreCols hn0 T core g).card ≤ n :=
    le_trans (Finset.card_le_univ _) (le_of_eq (Fintype.card_fin n))
  omega

/-- Every core edge realizes a colour in `coreCols`. -/
private lemma coreCol_mem {n : ℕ} (hn0 : 0 < n) {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (core : Finset V) (g : V → Fin (2 * n + 1))
    {a b : V} (ha : a ∈ core) (hb : b ∈ core) (hadj : T.Adj a b) :
    ndColouring n hn0 (Sym2.map g s(a, b)) ∈ coreCols hn0 T core g := by
  rw [coreCols, Finset.mem_image]
  refine ⟨s(a, b), ?_, rfl⟩
  rw [Finset.mem_filter, Finset.mem_inter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
    Finset.mk_mem_sym2_iff]
  exact ⟨Finset.mem_univ _, hadj, ha, hb⟩

/-- A free colour differs from every core-edge colour. -/
private lemma freeCol_fresh {n : ℕ} (hn0 : 0 < n) {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (core : Finset V) (g : V → Fin (2 * n + 1))
    {c : Fin n} (hc : c ∈ freeCols hn0 T core g)
    {a b : V} (ha : a ∈ core) (hb : b ∈ core) (hadj : T.Adj a b) :
    ndColouring n hn0 (Sym2.map g s(a, b)) ≠ c := by
  intro heq
  rw [freeCols, Finset.mem_sdiff] at hc
  exact hc.2 (heq ▸ coreCol_mem hn0 T core g ha hb hadj)

/-- **Core embedding** for Case C: embed the core forest by `small_tree_into_intervals_idx`
on the subtype `↥core`, then lift to a map `g : V → Fin (2n+1)`.  `V₀ = core ∖ (V₁ ∪ V₂)`
lands in the interval `I₀`; each side vertex lands at `base_p + idx v` with distinct
side vertices in distinct length-`L` blocks. -/
private lemma core_embedding_caseC (n k L : ℕ) (hn0 : 0 < n) (hk : 1 ≤ k) {V : Type*}
    [Fintype V] [DecidableEq V] (T : SimpleGraph V) (hac : T.IsAcyclic)
    (core V₁ V₂ : Finset V) (hV₁c : V₁ ⊆ core) (hV₂c : V₂ ⊆ core)
    (hV₁V₂ : Disjoint V₁ V₂)
    (a₀ ap₁ ap₂ : Fin (2 * n + 1)) (len₀ : ℕ)
    (hlen₀n : len₀ ≤ 2 * n + 1)
    (hnw₀ : a₀.val + len₀ ≤ 2 * n + 1)
    (hnw₁ : ap₁.val + V₁.card * L ≤ 2 * n + 1)
    (hnw₂ : ap₂.val + V₂.card * L ≤ 2 * n + 1)
    (hlen₀ : 6 * (core.card - V₁.card - V₂.card) + 12 ≤ len₀)
    (hQL : 10 ≤ L / (2 * (2 * k + 1)))
    (hpow1 : V₁.card < 2 ^ (k - 1)) (hpow2 : V₂.card < 2 ^ (k - 1))
    (hd01 : a₀.val + len₀ ≤ ap₁.val ∨ ap₁.val + V₁.card * L ≤ a₀.val)
    (hd02 : a₀.val + len₀ ≤ ap₂.val ∨ ap₂.val + V₂.card * L ≤ a₀.val)
    (hd12 : ap₁.val + V₁.card * L ≤ ap₂.val ∨ ap₂.val + V₂.card * L ≤ ap₁.val) :
    ∃ (g : V → Fin (2 * n + 1)) (idx : V → ℕ),
      Set.InjOn g ↑core ∧
      (∀ e₁ ∈ T.edgeSet, ∀ e₂ ∈ T.edgeSet,
        (∀ x, x ∉ core → x ∉ e₁) → (∀ x, x ∉ core → x ∉ e₂) →
        ndColouring n hn0 (Sym2.map g e₁) = ndColouring n hn0 (Sym2.map g e₂) →
        Sym2.map g e₁ = Sym2.map g e₂) ∧
      (∀ v ∈ core, v ∉ V₁ → v ∉ V₂ →
        a₀.val ≤ (g v).val ∧ (g v).val < a₀.val + len₀) ∧
      (∀ v ∈ V₁, (g v).val = ap₁.val + idx v ∧ idx v < V₁.card * L) ∧
      (∀ v ∈ V₂, (g v).val = ap₂.val + idx v ∧ idx v < V₂.card * L) ∧
      (∀ u ∈ V₁, ∀ v ∈ V₁, u ≠ v → idx u / L ≠ idx v / L) ∧
      (∀ u ∈ V₂, ∀ v ∈ V₂, u ≠ v → idx u / L ≠ idx v / L) := by
  classical
  -- Work on the core subtype.
  set part : ↥(core : Set V) → Option (Fin 2) :=
    fun v => if (v : V) ∈ V₁ then some 0 else if (v : V) ∈ V₂ then some 1 else none
    with hpart
  -- Identify the part classes with `V₁`, `V₂`, and the rest.
  have hpc1 : partClass part (some 0)
      = Finset.univ.filter (fun v : ↥(core : Set V) => (v : V) ∈ V₁) := by
    ext v
    simp only [mem_partClass, hpart, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h1 : (v : V) ∈ V₁
    · simp [h1]
    · simp only [if_neg h1]
      by_cases h2 : (v : V) ∈ V₂ <;> simp [h1, h2]
  have hpc2 : partClass part (some 1)
      = Finset.univ.filter (fun v : ↥(core : Set V) => (v : V) ∈ V₂) := by
    ext v
    simp only [mem_partClass, hpart, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h1 : (v : V) ∈ V₁
    · have h2 : (v : V) ∉ V₂ := fun h => Finset.disjoint_left.mp hV₁V₂ h1 h
      simp [h1, h2]
    · simp only [if_neg h1]
      by_cases h2 : (v : V) ∈ V₂ <;> simp [h2]
  have hcard1 : (partClass part (some 0)).card = V₁.card := by
    rw [hpc1]; exact card_filter_subtype_eq core V₁ hV₁c
  have hcard2 : (partClass part (some 1)).card = V₂.card := by
    rw [hpc2]; exact card_filter_subtype_eq core V₂ hV₂c
  have hcardVc : Fintype.card ↥(core : Set V) = core.card := by
    rw [Fintype.card_congr (Equiv.subtypeEquivRight (fun x => Finset.mem_coe))]
    exact Fintype.card_coe core
  have hcard0 : (partClass part none).card = core.card - V₁.card - V₂.card := by
    have hpc0 : partClass part none
        = Finset.univ.filter (fun v : ↥(core : Set V) => ¬ ((v : V) ∈ V₁ ∨ (v : V) ∈ V₂)) := by
      ext v
      simp only [mem_partClass, hpart, Finset.mem_filter, Finset.mem_univ, true_and, not_or]
      by_cases h1 : (v : V) ∈ V₁
      · simp [h1]
      · by_cases h2 : (v : V) ∈ V₂ <;> simp [h1, h2]
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset ↥(core : Set V)))
      (p := fun v : ↥(core : Set V) => (v : V) ∈ V₁ ∨ (v : V) ∈ V₂)
    have hor : (Finset.univ.filter
        (fun v : ↥(core : Set V) => (v : V) ∈ V₁ ∨ (v : V) ∈ V₂)).card
        = V₁.card + V₂.card := by
      rw [Finset.filter_or, Finset.card_union_of_disjoint, card_filter_subtype_eq core V₁ hV₁c,
        card_filter_subtype_eq core V₂ hV₂c]
      rw [Finset.disjoint_filter]
      intro v _ h1 h2
      exact Finset.disjoint_left.mp hV₁V₂ h1 h2
    rw [hpc0]
    rw [hor, Finset.card_univ, hcardVc] at hsplit
    omega
  -- Package the interval data as a `Fin 2`-indexed family.
  set ap : Fin 2 → Fin (2 * n + 1) := ![ap₁, ap₂] with hap
  have hap0 : ap 0 = ap₁ := rfl
  have hap1 : ap 1 = ap₂ := rfl
  have haccc : (T.induce (core : Set V)).IsAcyclic := hac.induce _
  -- Invoke the interval-controlled small-tree embedding on the core.
  obtain ⟨gc, idxc, hgcinj, hgcrb, hgc0, hgcP, hgcblk⟩ :=
    small_tree_into_intervals_idx n hn0 (T.induce (core : Set V)) haccc part k L hk
      a₀ len₀ ap hlen₀n
      (by rw [hcard0]; exact hlen₀)
      hQL
      (Fin.forall_fin_two.mpr ⟨by rw [hcard1]; omega, by rw [hcard2]; omega⟩)
      (Fin.forall_fin_two.mpr ⟨by rw [hcard1]; exact hpow1, by rw [hcard2]; exact hpow2⟩)
      (Fin.forall_fin_two.mpr
        ⟨by rw [hcard1, hap0]; exact disjoint_cyclicInterval_of_no_wrap hnw₀ hnw₁ hd01,
         by rw [hcard2, hap1]; exact disjoint_cyclicInterval_of_no_wrap hnw₀ hnw₂ hd02⟩)
      (Fin.forall_fin_two.mpr
        ⟨Fin.forall_fin_two.mpr ⟨fun h => absurd rfl h, fun _ => by
            rw [hcard1, hcard2, hap0, hap1]
            exact disjoint_cyclicInterval_of_no_wrap hnw₁ hnw₂ hd12⟩,
         Fin.forall_fin_two.mpr ⟨fun _ => by
            rw [hcard1, hcard2, hap0, hap1]
            exact (disjoint_cyclicInterval_of_no_wrap hnw₁ hnw₂ hd12).symm,
          fun h => absurd rfl h⟩⟩)
  -- Lift `gc`, `idxc` from the core subtype to all of `V`.
  set g : V → Fin (2 * n + 1) :=
    fun v => if h : v ∈ core then gc ⟨v, Finset.mem_coe.mpr h⟩ else ⟨0, by omega⟩ with hg
  set idx : V → ℕ := fun v => if h : v ∈ core then idxc ⟨v, Finset.mem_coe.mpr h⟩ else 0 with hidx
  have hgval : ∀ (v : V) (h : v ∈ core), g v = gc ⟨v, Finset.mem_coe.mpr h⟩ := by
    intro v h; simp only [hg, dif_pos h]
  have hidxval : ∀ (v : V) (h : v ∈ core), idx v = idxc ⟨v, Finset.mem_coe.mpr h⟩ := by
    intro v h; simp only [hidx, dif_pos h]
  have hpartnone : ∀ (v : V) (h : v ∈ core), v ∉ V₁ → v ∉ V₂ →
      part ⟨v, Finset.mem_coe.mpr h⟩ = none := by
    intro v h hv1 hv2
    simp only [hpart, if_neg hv1, if_neg hv2]
  have hpart0 : ∀ (v : V) (h : v ∈ core), v ∈ V₁ →
      part ⟨v, Finset.mem_coe.mpr h⟩ = some 0 := by
    intro v h hv1
    simp only [hpart, if_pos hv1]
  have hpart1 : ∀ (v : V) (h : v ∈ core), v ∈ V₂ →
      part ⟨v, Finset.mem_coe.mpr h⟩ = some 1 := by
    intro v h hv2
    have hv1 : v ∉ V₁ := fun hh => Finset.disjoint_left.mp hV₁V₂ hh hv2
    simp only [hpart, if_neg hv1, if_pos hv2]
  refine ⟨g, idx, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- injectivity on core
    intro a ha b hb hab
    rw [Finset.mem_coe] at ha hb
    rw [hgval a ha, hgval b hb] at hab
    exact congrArg Subtype.val (hgcinj hab)
  · -- rainbow on core edges: each mapped core edge of `T` lies in the mapped edge set
    -- of the induced core forest, on which `gc` is rainbow.
    have hmemImg : ∀ a b : V, a ∈ core → b ∈ core → T.Adj a b →
        Sym2.map g s(a, b)
          ∈ (↑((T.induce (core : Set V)).edgeFinset.image (Sym2.map gc)) :
              Set (Sym2 (Fin (2 * n + 1)))) := by
      intro a b ha hb hadj
      rw [Finset.coe_image, Set.mem_image]
      refine ⟨s(⟨a, Finset.mem_coe.mpr ha⟩, ⟨b, Finset.mem_coe.mpr hb⟩), ?_, ?_⟩
      · rw [Finset.mem_coe, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        exact hadj
      · rw [Sym2.map_mk, Sym2.map_mk, hgval a ha, hgval b hb]
    intro e₁ he₁ e₂ he₂ hc₁ hc₂ hcol
    induction e₁ using Sym2.ind with
    | _ a b =>
      induction e₂ using Sym2.ind with
      | _ c d =>
        rw [SimpleGraph.mem_edgeSet] at he₁ he₂
        have ha : a ∈ core := by
          by_contra h; exact hc₁ a h (Sym2.mem_mk_left a b)
        have hb : b ∈ core := by
          by_contra h; exact hc₁ b h (Sym2.mem_mk_right a b)
        have hc : c ∈ core := by
          by_contra h; exact hc₂ c h (Sym2.mem_mk_left c d)
        have hd : d ∈ core := by
          by_contra h; exact hc₂ d h (Sym2.mem_mk_right c d)
        exact hgcrb (hmemImg a b ha hb he₁) (hmemImg c d hc hd he₂) hcol
  · -- V₀ vertices land in I₀
    intro v hv hv1 hv2
    have hmem := hgc0 ⟨v, Finset.mem_coe.mpr hv⟩ (hpartnone v hv hv1 hv2)
    rw [mem_cyclicInterval_of_no_wrap hnw₀] at hmem
    rw [hgval v hv]
    exact hmem
  · -- V₁ positions
    intro v hv
    have hvc := hV₁c hv
    obtain ⟨hidxlt, hshift⟩ := hgcP 0 ⟨v, Finset.mem_coe.mpr hvc⟩ (hpart0 v hvc hv)
    rw [hcard1] at hidxlt
    refine ⟨?_, ?_⟩
    · rw [hgval v hvc, ← hshift, cyclicShift_val, hap0,
        Nat.mod_eq_of_lt (show ap₁.val + idxc ⟨v, Finset.mem_coe.mpr hvc⟩ < 2 * n + 1 by omega),
        hidxval v hvc]
    · rw [hidxval v hvc]; exact hidxlt
  · -- V₂ positions
    intro v hv
    have hvc := hV₂c hv
    obtain ⟨hidxlt, hshift⟩ := hgcP 1 ⟨v, Finset.mem_coe.mpr hvc⟩ (hpart1 v hvc hv)
    rw [hcard2] at hidxlt
    refine ⟨?_, ?_⟩
    · rw [hgval v hvc, ← hshift, cyclicShift_val, hap1,
        Nat.mod_eq_of_lt (show ap₂.val + idxc ⟨v, Finset.mem_coe.mpr hvc⟩ < 2 * n + 1 by omega),
        hidxval v hvc]
    · rw [hidxval v hvc]; exact hidxlt
  · -- V₁ blocks distinct
    intro u hu v hv huv
    have huc := hV₁c hu
    have hvc := hV₁c hv
    have hne : (⟨u, Finset.mem_coe.mpr huc⟩ : ↥(core : Set V)) ≠ ⟨v, Finset.mem_coe.mpr hvc⟩ :=
      fun h => huv (congrArg Subtype.val h)
    have := hgcblk 0 _ (hpart0 u huc hu) _ (hpart0 v hvc hv) hne
    rw [hidxval u huc, hidxval v hvc]
    exact this
  · -- V₂ blocks distinct
    intro u hu v hv huv
    have huc := hV₂c hu
    have hvc := hV₂c hv
    have hne : (⟨u, Finset.mem_coe.mpr huc⟩ : ↥(core : Set V)) ≠ ⟨v, Finset.mem_coe.mpr hvc⟩ :=
      fun h => huv (congrArg Subtype.val h)
    have := hgcblk 1 _ (hpart1 u huc hu) _ (hpart1 v hvc hv) hne
    rw [hidxval u huc, hidxval v hvc]
    exact this

/-- **Embedding trees in Case C, many-vertex branch** (`Theorem_case_C`, MPS §7).
`T` is a tree on `n+1` vertices; `core` is a set of at most `n/100` vertices such that
every vertex outside `core` is a pendant leaf attached (by `anchor`) to a core vertex;
every leaf-bearing core vertex has between `t` and `2n/3` leaves.  For
`t ≥ 4000(2k+1)`, `n < 2^(k-1)` and `n ≥ 10^6`, `T` has a rainbow copy in the
ND-coloured `K_{2n+1}`. -/
theorem caseC_many_vertex (n t k : ℕ) {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsAcyclic)
    (hVcard : Fintype.card V = n + 1)
    (core : Finset V) (anchor : V → V)
    (hcore : core.card ≤ n / 100)
    (hanchor : ∀ v, v ∉ core → anchor v ∈ core ∧ T.Adj v (anchor v)
      ∧ ∀ w, T.Adj v w → w = anchor v)
    (hbig : ∀ u ∈ core,
      (Finset.univ.filter (fun v => v ∉ core ∧ anchor v = u)).Nonempty →
      t ≤ (Finset.univ.filter (fun v => v ∉ core ∧ anchor v = u)).card)
    (hsmalldeg : ∀ u : V,
      (Finset.univ.filter (fun v => v ∉ core ∧ anchor v = u)).card ≤ 2 * n / 3)
    (hkn : n < 2 ^ (k - 1)) (hk : 1 ≤ k)
    (ht : 4000 * (2 * k + 1) ≤ t)
    (hn : 1000000 ≤ n) :
    ∃ f : V ↪ Fin (2 * n + 1),
      Set.InjOn (ndColouring n (by omega)) (T.map f).edgeSet := by
  classical
  have hn0 : 0 < n := by omega
  -- Restate the degree hypotheses through `leafSet`.
  have hbig' : ∀ u ∈ core, (leafSet core anchor u).Nonempty →
      t ≤ (leafSet core anchor u).card := hbig
  have hsmalldeg' : ∀ u : V, (leafSet core anchor u).card ≤ 2 * n / 3 := hsmalldeg
  -- Count the leaves.
  have hncore : (Finset.univ.filter (fun v => v ∉ core)).card + core.card = n + 1 := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset V))
      (p := fun v => v ∉ core)
    have hcc : Finset.univ.filter (fun v => ¬v ∉ core) = core := by
      ext v
      simp
    rw [hcc, Finset.card_univ, hVcard] at h
    exact h
  have hsum : (Finset.univ.filter (fun v => v ∉ core)).card
      = ∑ u ∈ core, (leafSet core anchor u).card :=
    sum_leafSet_card core anchor (fun v hv => (hanchor v hv).1)
  -- The leaf-bearing core vertices.
  set bigs : Finset V := core.filter (fun u => (leafSet core anchor u).Nonempty)
    with hbigsdef
  have hbigs_sub : bigs ⊆ core := Finset.filter_subset _ _
  have hsum_bigs : ∑ u ∈ bigs, (leafSet core anchor u).card
      = ∑ u ∈ core, (leafSet core anchor u).card := by
    refine Finset.sum_subset hbigs_sub (fun u hu hunb => ?_)
    rw [hbigsdef, Finset.mem_filter, not_and] at hunb
    rw [Finset.not_nonempty_iff_eq_empty.mp (hunb hu), Finset.card_empty]
  have hbigs_t : ∀ u ∈ bigs, t ≤ (leafSet core anchor u).card := by
    intro u hu
    rw [hbigsdef, Finset.mem_filter] at hu
    exact hbig' u hu.1 hu.2
  -- Total number of leaves: at least 99n/100.
  have htotal : 99 * n / 100 ≤ ∑ u ∈ bigs, (leafSet core anchor u).card := by
    rw [hsum_bigs, ← hsum]
    have hdiv : core.card ≤ n / 100 := hcore
    omega
  -- Numeric parameters: block length `L`, counting constant `20`.
  set L : ℕ := 40 * (2 * k + 1) with hLdef
  have hQL : L / (2 * (2 * k + 1)) = 20 := by
    rw [hLdef, show 40 * (2 * k + 1) = 20 * (2 * (2 * k + 1)) by ring]
    exact Nat.mul_div_cancel 20 (by omega)
  have htL : 100 * L ≤ t := by
    rw [hLdef]
    omega
  -- Select the colour-heavy side `V₁`: leaf-sum in `(n/20, 2n/3 + n/20]`.
  have hselect : ∃ V₁ ⊆ bigs, n / 20 < ∑ u ∈ V₁, (leafSet core anchor u).card ∧
      ∑ u ∈ V₁, (leafSet core anchor u).card ≤ 2 * n / 3 + n / 20 := by
    by_cases hhuge : ∃ u ∈ bigs, n / 20 < (leafSet core anchor u).card
    · obtain ⟨u₀, hu₀b, hu₀⟩ := hhuge
      refine ⟨{u₀}, Finset.singleton_subset_iff.mpr hu₀b, ?_, ?_⟩
      · rw [Finset.sum_singleton]
        exact hu₀
      · rw [Finset.sum_singleton]
        have := hsmalldeg' u₀
        omega
    · push Not at hhuge
      have hgt0 : n / 20 < ∑ u ∈ bigs, (leafSet core anchor u).card := by omega
      obtain ⟨V₁, hsub, hgt, hle⟩ := exists_subset_sum_between bigs
        (fun u => (leafSet core anchor u).card) (n / 20) hgt0 hhuge
      exact ⟨V₁, hsub, hgt, by omega⟩
  obtain ⟨V₁, hV₁bigs, hV₁gt, hV₁le⟩ := hselect
  set V₂ : Finset V := bigs \ V₁ with hV₂def
  have hV₂bigs : V₂ ⊆ bigs := Finset.sdiff_subset
  have hV₁V₂ : Disjoint V₁ V₂ := Finset.disjoint_sdiff
  have hV₁union : V₁ ∪ V₂ = bigs := Finset.union_sdiff_of_subset hV₁bigs
  have hsplitV : ∑ u ∈ V₁, (leafSet core anchor u).card
      + ∑ u ∈ V₂, (leafSet core anchor u).card
      = ∑ u ∈ bigs, (leafSet core anchor u).card := by
    rw [← Finset.sum_union hV₁V₂, hV₁union]
  have hV₁ne : V₁.Nonempty := by
    rcases Finset.eq_empty_or_nonempty V₁ with rfl | h
    · simp at hV₁gt
    · exact h
  -- Cardinality bounds from the degree lower bound `t`.
  have ht0 : 0 < t := by omega
  have hcard_le_sum : ∀ S : Finset V, S ⊆ bigs →
      S.card * t ≤ ∑ u ∈ S, (leafSet core anchor u).card := by
    intro S hS
    calc S.card * t = ∑ _u ∈ S, t := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ u ∈ S, (leafSet core anchor u).card :=
          Finset.sum_le_sum (fun u hu => hbigs_t u (hS hu))
  have hsum_le_n : ∑ u ∈ bigs, (leafSet core anchor u).card ≤ n + 1 := by
    rw [hsum_bigs, ← hsum]
    omega
  have hV₁L : V₁.card * L ≤ n / 100 := by
    have h1 := hcard_le_sum V₁ hV₁bigs
    have h2 : ∑ u ∈ V₁, (leafSet core anchor u).card
        ≤ ∑ u ∈ bigs, (leafSet core anchor u).card :=
      Finset.sum_le_sum_of_subset hV₁bigs
    rw [Nat.le_div_iff_mul_le (by omega)]
    have h3 : V₁.card * t ≤ n + 1 := by omega
    have h4 : V₁.card * L * 100 = V₁.card * (100 * L) := by ring
    have h5 : V₁.card * (100 * L) ≤ V₁.card * t :=
      Nat.mul_le_mul_left _ htL
    omega
  have hV₂L : V₂.card * L ≤ n / 100 := by
    have h1 := hcard_le_sum V₂ hV₂bigs
    rw [Nat.le_div_iff_mul_le (by omega)]
    have h4 : V₂.card * L * 100 = V₂.card * (100 * L) := by ring
    have h5 : V₂.card * (100 * L) ≤ V₂.card * t :=
      Nat.mul_le_mul_left _ htL
    omega
  have hV₁core : V₁ ⊆ core := hV₁bigs.trans hbigs_sub
  have hV₂core : V₂ ⊆ core := hV₂bigs.trans hbigs_sub
  have hcoren : core.card ≤ n / 100 := hcore
  have hdivn : n / 100 ≤ n := Nat.div_le_self n 100
  have hV₁cardn : V₁.card ≤ n :=
    le_trans (Finset.card_le_card hV₁core) (le_trans hcore hdivn)
  have hV₂cardn : V₂.card ≤ n :=
    le_trans (Finset.card_le_card hV₂core) (le_trans hcore hdivn)
  -- Concrete interval layout (`main.tex`:330), all non-wrapping since `n ≥ 10⁶`.
  set a₀ : Fin (2 * n + 1) := ⟨83 * n / 100, by omega⟩ with ha₀
  set ap₁ : Fin (2 * n + 1) := ⟨70 * n / 100, by omega⟩ with hap₁def
  set ap₂ : Fin (2 * n + 1) := ⟨91 * n / 100, by omega⟩ with hap₂def
  set len₀ : ℕ := 7 * n / 100 with hlen₀def
  have hnw₀ : a₀.val + len₀ ≤ 2 * n + 1 := by simp only [ha₀, hlen₀def]; omega
  have hnw₁ : ap₁.val + V₁.card * L ≤ 2 * n + 1 := by
    simp only [hap₁def]; omega
  have hnw₂ : ap₂.val + V₂.card * L ≤ 2 * n + 1 := by
    simp only [hap₂def]; omega
  obtain ⟨g, idx, hginjcore, hrbcore, hgI₀, hgV₁, hgV₂, hblkV₁, hblkV₂⟩ :=
    core_embedding_caseC n k L hn0 hk T hT core V₁ V₂ hV₁core hV₂core hV₁V₂
      a₀ ap₁ ap₂ len₀ (by simp only [hlen₀def]; omega) hnw₀ hnw₁ hnw₂
      (by simp only [hlen₀def]; omega)
      (by omega)
      (by omega) (by omega)
      (by simp only [ha₀, hap₁def, hlen₀def]; right; omega)
      (by simp only [ha₀, hap₂def, hlen₀def]; left; omega)
      (by simp only [hap₁def, hap₂def]; left; omega)
  -- The leaves and the pendant-edge structure of `T`.
  set leaves : Finset V := Finset.univ.filter (fun v => v ∉ core) with hleavesdef
  have hmem_leaves : ∀ x, x ∈ leaves ↔ x ∉ core := by
    intro x; simp [hleavesdef]
  have hanchor_notmem : ∀ x ∈ leaves, anchor x ∉ leaves := by
    intro x hx
    rw [hmem_leaves] at hx ⊢
    exact fun h => h (hanchor x hx).1
  have hedges : ∀ e ∈ T.edgeSet,
      (∀ x ∈ leaves, x ∉ e) ∨ ∃ x ∈ leaves, e = s(x, anchor x) := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeSet] at he
      by_cases ha : a ∈ core
      · by_cases hb : b ∈ core
        · left
          intro x hx hxe
          rw [hmem_leaves] at hx
          rw [Sym2.mem_iff] at hxe
          rcases hxe with rfl | rfl
          · exact hx ha
          · exact hx hb
        · right
          refine ⟨b, (hmem_leaves b).mpr hb, ?_⟩
          have hba : a = anchor b := (hanchor b hb).2.2 a he.symm
          rw [hba, Sym2.eq_swap]
      · right
        refine ⟨a, (hmem_leaves a).mpr ha, ?_⟩
        have hab : b = anchor a := (hanchor a ha).2.2 b he
        rw [hab]
  have hginj_leaves : Set.InjOn g {v | v ∉ leaves} := by
    intro x hx y hy hxy
    rw [Set.mem_setOf_eq, hmem_leaves, not_not] at hx hy
    exact hginjcore (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hxy
  -- The ascending list of free colours; leaf colours are drawn from it.
  set ds : List (Fin n) := (freeCols hn0 T core g).sort (· ≤ ·) with hdsdef
  have hds_sorted : ds.Pairwise (· < ·) := (Finset.sortedLT_sort _).pairwise
  have hds_nodup : ds.Nodup := hds_sorted.imp (fun h => ne_of_lt h)
  have hds_len : ds.length = (freeCols hn0 T core g).card := Finset.length_sort _
  have hds_mem : ∀ i (hi : i < ds.length), ds[i]'hi ∈ freeCols hn0 T core g :=
    fun i hi => (Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem hi)
  have hcorene : core.Nonempty := by obtain ⟨v, hv⟩ := hV₁ne; exact ⟨v, hV₁core hv⟩
  -- Position rank: each side vertex occupies one length-`L` block; the block index
  -- `idx v / L` is a bijection from the side onto `[0, |side|)`.
  have hrankV₁_lt : ∀ v ∈ V₁, idx v / L < V₁.card := by
    intro v hv
    obtain ⟨_, hlt⟩ := hgV₁ v hv
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hlt)
  have hrankV₂_lt : ∀ v ∈ V₂, idx v / L < V₂.card := by
    intro v hv
    obtain ⟨_, hlt⟩ := hgV₂ v hv
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hlt)
  have hrankV₁_surj : ∀ r < V₁.card, ∃ v ∈ V₁, idx v / L = r :=
    finset_bij_of_injOn_lt V₁ V₁.card rfl (fun v => idx v / L) hrankV₁_lt
      (fun u hu v hv h => by
        by_contra hne
        exact hblkV₁ u (Finset.mem_coe.mp hu) v (Finset.mem_coe.mp hv) hne h)
  have hrankV₂_surj : ∀ r < V₂.card, ∃ v ∈ V₂, idx v / L = r :=
    finset_bij_of_injOn_lt V₂ V₂.card rfl (fun v => idx v / L) hrankV₂_lt
      (fun u hu v hv h => by
        by_contra hne
        exact hblkV₂ u (Finset.mem_coe.mp hu) v (Finset.mem_coe.mp hv) hne h)
  sorry

end Ringel
