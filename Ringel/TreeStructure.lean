import Mathlib
import Ringel.Primitives

set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
/-!
# Structure of trees (MPS §3.3)

Self-contained finite tree combinatorics underpinning the case division
(`Ringel/CaseDivision.lean`, Lemma 2.2). No probability, no external papers.

The headline result is `split` (Montgomery, "Spanning trees in dense directed graphs"-style
folklore): an `n`-vertex tree has either `≥ n/(4k)` leaves or `≥ n/(4k)` vertex-disjoint bare
paths of length `k`. Its first ingredient — that a tree has at least two more leaves than
branch (degree `≥ 3`) vertices — is proved here in full via the degree-sum identity.
-/

open SimpleGraph Finset

namespace Ringel.TreeStructure

/-- Choose one representative from every nonempty fibre of `f` on `s`. -/
theorem exists_injOn_selector {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → β) :
    ∃ t : Finset α, t ⊆ s ∧ Set.InjOn f t ∧ t.image f = s.image f := by
  apply Finset.exists_subset_injOn_image_eq_of_surjOn (s := (s : Set α)) (t := s.image f)
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  exact ⟨x, hx, rfl⟩

/-- A finite set whose fibres under `f` have size at most `b` contains an `m`-element
subset on which `f` is injective whenever `b * m ≤ s.card`. -/
theorem exists_subset_injOn_of_bounded_fibres {α β : Type*}
    [DecidableEq α] [DecidableEq β] (s : Finset α) (f : α → β) (b m : ℕ)
    (hb : 0 < b)
    (hfibre : ∀ y ∈ s.image f, (s.filter fun x => f x = y).card ≤ b)
    (hsize : b * m ≤ s.card) :
    ∃ t : Finset α, t ⊆ s ∧ Set.InjOn f t ∧ t.card = m := by
  obtain ⟨u, hus, huinj, huimage⟩ := exists_injOn_selector s f
  have hsimage : s.card ≤ b * (s.image f).card :=
    Finset.card_le_mul_card_image s b hfibre
  have hmimage : m ≤ (s.image f).card := by
    have : b * m ≤ b * (s.image f).card := hsize.trans hsimage
    exact Nat.le_of_mul_le_mul_left this hb
  have hucard : u.card = (s.image f).card := by
    rw [← Finset.card_image_of_injOn huinj, huimage]
  obtain ⟨t, htu, htcard⟩ := Finset.exists_subset_card_eq (hucard.symm ▸ hmimage)
  exact ⟨t, htu.trans hus, huinj.mono (by
    intro x hx
    exact htu hx), htcard⟩

open Classical in
/-- A pairwise vertex-disjoint family contains at most `A.card` lists that meet `A`. -/
theorem card_paths_meeting_finset_le {α : Type*} [Nonempty α]
    (paths : Finset (List α)) (A : Finset α)
    (hdisjoint : ∀ P ∈ paths, ∀ Q ∈ paths, P ≠ Q →
      Disjoint P.toFinset Q.toFinset) :
    (paths.filter fun P => ∃ x ∈ P, x ∈ A).card ≤ A.card := by
  let bad := paths.filter fun P => ∃ x ∈ P, x ∈ A
  let pick : List α → α := fun P =>
    if h : ∃ x ∈ P, x ∈ A then h.choose else Classical.choice inferInstance
  have hpick : ∀ P ∈ bad, pick P ∈ P ∧ pick P ∈ A := by
    intro P hP
    have h : ∃ x ∈ P, x ∈ A := by
      simpa [bad] using hP
    rw [pick, dif_pos h]
    exact h.choose_spec
  have hinjective : Set.InjOn pick (bad : Set (List α)) := by
    intro P hP Q hQ hpickeq
    by_contra hPQ
    have hPpaths : P ∈ paths := Finset.mem_of_mem_filter hP
    have hQpaths : Q ∈ paths := Finset.mem_of_mem_filter hQ
    have hdisj := hdisjoint P hPpaths Q hQpaths hPQ
    exact Finset.disjoint_left.mp hdisj
      (List.mem_toFinset.mpr (hpick P hP).1)
      (List.mem_toFinset.mpr (by simpa [hpickeq] using (hpick Q hQ).1))
  have himage : bad.image pick ⊆ A := by
    intro x hx
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hx
    exact (hpick P hP).2
  change bad.card ≤ A.card
  rw [← Finset.card_image_of_injOn hinjective]
  exact Finset.card_le_card himage

/-- **Leaves dominate branch vertices.** In a finite tree with at least two vertices, the number
of branch vertices (degree `≥ 3`) is at least two less than the number of leaves (degree `1`).

Proof: `∑_v (2 - deg v) = 2|V| - 2(|V|-1) = 2`. Every vertex has degree `≥ 1` (the tree is
connected with `≥ 2` vertices), so termwise `2 - deg v ≤ 𝟙[deg v = 1] - 𝟙[deg v ≥ 3]`; summing
gives `2 ≤ #leaves - #branch`. -/
theorem card_branch_add_two_le_card_leaves {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree) (hn : 2 ≤ Fintype.card V) :
    {v | 3 ≤ T.degree v}.toFinset.card + 2 ≤ {v | T.degree v = 1}.toFinset.card := by
  classical
  have hdeg : ∑ v, T.degree v = 2 * T.edgeFinset.card :=
    SimpleGraph.sum_degrees_eq_twice_card_edges T
  have hedge : T.edgeFinset.card + 1 = Fintype.card V := hT.card_edgeFinset
  have hZ : ∑ v : V, ((2 : ℤ) - T.degree v) = 2 := by
    have h1 : ∑ v : V, ((2 : ℤ) - T.degree v)
        = 2 * (Fintype.card V : ℤ) - (∑ v, T.degree v : ℕ) := by
      rw [Finset.sum_sub_distrib]; push_cast; simp [Finset.card_univ, mul_comm]
    rw [h1, hdeg]
    have : (T.edgeFinset.card : ℤ) + 1 = Fintype.card V := by exact_mod_cast hedge
    push_cast; omega
  have hpos : ∀ v, 1 ≤ T.degree v := by
    intro v
    rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, SimpleGraph.degree_pos_iff_exists_adj]
    obtain ⟨u, hu⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card V) v
    obtain ⟨p⟩ := hT.isConnected.preconnected v u
    cases p with
    | nil => exact absurd rfl hu
    | cons h _ => exact ⟨_, h⟩
  have hbound : ∀ v : V, ((2 : ℤ) - T.degree v)
      ≤ (if T.degree v = 1 then (1:ℤ) else 0) - (if 3 ≤ T.degree v then (1:ℤ) else 0) := by
    intro v; have := hpos v; split_ifs <;> omega
  have hsum_le : (2 : ℤ) ≤ ∑ v : V, ((if T.degree v = 1 then (1:ℤ) else 0)
      - (if 3 ≤ T.degree v then (1:ℤ) else 0)) := by
    calc (2:ℤ) = ∑ v : V, ((2 : ℤ) - T.degree v) := hZ.symm
      _ ≤ _ := Finset.sum_le_sum (fun v _ => hbound v)
  rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole] at hsum_le
  have e1 : (Finset.univ.filter (fun v => T.degree v = 1)).card
      = {v | T.degree v = 1}.toFinset.card := by congr 1; ext v; simp
  have e2 : (Finset.univ.filter (fun v => 3 ≤ T.degree v)).card
      = {v | 3 ≤ T.degree v}.toFinset.card := by congr 1; ext v; simp
  rw [e1, e2] at hsum_le
  omega

/-- **Degree partition.** In a finite tree with at least two vertices, every vertex has degree
`1`, `2`, or `≥ 3` (no isolated vertices, as the tree is connected), so the vertex count splits as
leaves `+` degree-`2` vertices `+` branch vertices. -/
theorem card_vert_eq_card_leaves_add {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree) (hn : 2 ≤ Fintype.card V) :
    Fintype.card V = {v | T.degree v = 1}.toFinset.card + {v | T.degree v = 2}.toFinset.card
      + {v | 3 ≤ T.degree v}.toFinset.card := by
  classical
  have hpos : ∀ v, 1 ≤ T.degree v := by
    intro v
    rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, SimpleGraph.degree_pos_iff_exists_adj]
    obtain ⟨u, hu⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card V) v
    obtain ⟨p⟩ := hT.isConnected.preconnected v u
    cases p with
    | nil => exact absurd rfl hu
    | cons h _ => exact ⟨_, h⟩
  have hone : ∀ v : V, (if T.degree v = 1 then 1 else 0) + (if T.degree v = 2 then 1 else 0)
      + (if 3 ≤ T.degree v then 1 else 0) = 1 := by
    intro v; have := hpos v; split_ifs <;> omega
  simp only [Set.toFinset_setOf]
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  simp only [hone, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]

/-- **Degree-`2` vertices are abundant.** Combining the leaf/branch bound with the degree
partition: `|V| + 2 ≤ #{deg = 2} + 2·#{deg = 1}`. Hence when a tree has few leaves it has very
many degree-`2` vertices, which is what forces long bare paths in `split`. -/
theorem card_vert_add_two_le_card_deg_two_add {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree) (hn : 2 ≤ Fintype.card V) :
    Fintype.card V + 2 ≤ {v | T.degree v = 2}.toFinset.card + 2 * {v | T.degree v = 1}.toFinset.card := by
  have hpart := card_vert_eq_card_leaves_add T hT hn
  have hbranch := card_branch_add_two_le_card_leaves T hT hn
  omega

/-- **Few leaves force many degree-`2` vertices.** If a tree with `≥ 2` vertices has fewer than
`n/(4k)` leaves (the negation of the left disjunct of `split`), then more than half its vertices
have degree `2`. This is the quantitative input to the bare-path extraction in `split`. -/
theorem card_lt_two_mul_card_deg_two {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree) (hn : 2 ≤ Fintype.card V)
    (k : ℕ) (hk : 1 ≤ k)
    (hfew : {v | T.degree v = 1}.toFinset.card * (4 * k) < Fintype.card V) :
    Fintype.card V < 2 * {v | T.degree v = 2}.toFinset.card := by
  have h := card_vert_add_two_le_card_deg_two_add T hT hn
  nlinarith [Nat.mul_le_mul_left ({v | T.degree v = 1}.toFinset.card * 4) hk]

/-- **Bare-path counting core (arithmetic).** If the maximal bare paths of a tree span edge-counts
`ℓ₁, …, ℓ_M` (summing to the total bare edges `S`), then cutting each into `⌊ℓ_i/k⌋` disjoint
length-`k` subpaths yields `∑ ⌊ℓ_i/k⌋` of them, and `S ≤ k·∑⌊ℓ_i/k⌋ + M·(k−1)`. Hence
`∑⌊ℓ_i/k⌋ ≥ (S − M(k−1))/k`, the bound that closes `split` once the geometric edge-partition
(`#maximal-bare-paths ≤ 2·#leaves − 3`, total bare edges `≥ n − 1 − …`) is supplied. -/
theorem sum_le_mul_sum_div_add (L : List ℕ) (k : ℕ) (hk : 0 < k) :
    L.sum ≤ k * (L.map (· / k)).sum + L.length * (k - 1) := by
  induction L with
  | nil => simp
  | cons a t ih =>
    simp only [List.sum_cons, List.map_cons, List.length_cons]
    have ha : a ≤ k * (a / k) + (k - 1) := by
      have := Nat.div_add_mod a k; have hmod : a % k < k := Nat.mod_lt a hk; omega
    rw [Nat.mul_add, Nat.add_mul, Nat.one_mul]
    omega

/-- **Degree sum over the degree-`2` set.** Every degree-`2` vertex contributes exactly `2` to the
degree sum, so `∑_{deg = 2} deg = 2·#{deg = 2}`. A self-contained ingredient of the `split`
handshake count. -/
theorem sum_degree_deg_two {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] :
    ∑ v ∈ {v | T.degree v = 2}.toFinset, T.degree v
      = 2 * {v | T.degree v = 2}.toFinset.card := by
  have h : ∀ v ∈ {v | T.degree v = 2}.toFinset, T.degree v = 2 := by
    intro v hv; simpa using hv
  calc ∑ v ∈ {v | T.degree v = 2}.toFinset, T.degree v
      = ∑ _v ∈ {v | T.degree v = 2}.toFinset, 2 := Finset.sum_congr rfl h
    _ = 2 * {v | T.degree v = 2}.toFinset.card := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- **Tree degree sum.** A finite tree has `n - 1` edges, so by the handshake identity
(`sum_degrees_eq_twice_card_edges`) the total degree is `2(n - 1)`. -/
theorem sum_degrees_eq_two_mul_card_sub_one {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree) :
    ∑ v, T.degree v = 2 * (Fintype.card V - 1) := by
  have hdeg : ∑ v, T.degree v = 2 * T.edgeFinset.card :=
    SimpleGraph.sum_degrees_eq_twice_card_edges T
  have hedge : T.edgeFinset.card + 1 = Fintype.card V := hT.card_edgeFinset
  omega

/-- **Handshake bound on the non-degree-`2` vertices** (`split` step (c)). Splitting the tree
degree sum across the degree-`2` set `D` and its complement, and using that each degree-`2` vertex
contributes `2`, the degree sum over the leaf-and-branch vertices is `2(L + B - 1)`, where
`L = #{deg = 1}` and `B = #{deg ≥ 3}`. Since this degree sum counts every tree edge incident to
`V \ D` at least once, it bounds from above the number of such edges, hence — combined with the
forest component identity `#segments = |D| - e_D` — the number of maximal bare segments by
`L + B - 1`. -/
theorem sum_degree_compl_deg_two_add_two {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree) (hn : 2 ≤ Fintype.card V) :
    (∑ v ∈ {v | T.degree v = 2}.toFinsetᶜ, T.degree v) + 2
      = 2 * ({v | T.degree v = 1}.toFinset.card + {v | 3 ≤ T.degree v}.toFinset.card) := by
  have hsplit := Finset.sum_add_sum_compl {v | T.degree v = 2}.toFinset (fun v => T.degree v)
  have hD := sum_degree_deg_two T
  have htot := sum_degrees_eq_two_mul_card_sub_one T hT
  have hpart := card_vert_eq_card_leaves_add T hT hn
  simp only at hsplit
  omega

/-- **Split assembly arithmetic.** The final count for `split`: if the maximal bare paths (there are
`M` of them, with `M·k` small relative to `n`) are cut into `pieces` disjoint length-`k` subpaths
satisfying the counting inequality `n − 1 ≤ k·pieces + M·(k−1)` (from `sum_le_mul_sum_div_add`), then
`pieces ≥ n/(4k)`. This isolates the remaining content of `split` to producing the geometric path
count; the arithmetic is closed here. -/
theorem split_piece_count (n k M pieces : ℕ) (hk : 2 < k) (hn : 4 ≤ n)
    (hcount : n - 1 ≤ k * pieces + M * (k - 1)) (hMsmall : 2 * (M * k) < n) :
    n / (4 * k) ≤ pieces := by
  have hcb : M * (k - 1) ≤ M * k := Nat.mul_le_mul_left M (by omega)
  have hle : n ≤ 4 * k * pieces := by
    have h4 : 4 * k * pieces = 4 * (k * pieces) := by ring
    rw [h4]; omega
  exact Nat.div_le_of_le_mul hle

/-- **Split assembly arithmetic, vertex-list variant.** Companion to `split_piece_count` for the
chunking that works on *vertex lists* rather than edge counts. If the `M` maximal bare paths have
vertex-counts summing so that cutting each list of `ℓᵢ + 1` vertices into blocks of `k + 1`
vertices yields `pieces` length-`k` subpaths with `n − 1 ≤ (k + 1)·pieces + M·(k − 1)` (the output
of `sum_le_mul_sum_div_add` applied to the lengths `ℓᵢ + 1` with divisor `k + 1`), and the segment
count is small (`2·M·k < n`, from few leaves), then `pieces ≥ n/(4k)`. -/
theorem split_piece_count_succ (n k M pieces : ℕ) (hk : 2 < k) (hn : 4 ≤ n)
    (hcount : n - 1 ≤ (k + 1) * pieces + M * (k - 1)) (hMsmall : 2 * (M * k) < n) :
    n / (4 * k) ≤ pieces := by
  apply Nat.div_le_of_le_mul
  have f1 : M * (k - 1) ≤ M * k := Nat.mul_le_mul_left M (by omega)
  rcases Nat.eq_zero_or_pos pieces with hp | hp
  · exfalso; subst hp; simp only [Nat.mul_zero, Nat.zero_add] at hcount; omega
  · have e2 : 2 * ((k + 1) * pieces) = (2 * k + 2) * pieces := by ring
    have e4 : 4 * k * pieces = (2 * k - 2) * pieces + (2 * k + 2) * pieces := by
      have h : (2 * k - 2) + (2 * k + 2) = 4 * k := by omega
      rw [← h]; ring
    have hlow : 4 ≤ (2 * k - 2) * pieces := by
      calc 4 ≤ 2 * k - 2 := by omega
        _ = (2 * k - 2) * 1 := (Nat.mul_one _).symm
        _ ≤ (2 * k - 2) * pieces := Nat.mul_le_mul_left _ (by omega)
    have f3 : 2 * ((k + 1) * pieces) + 4 ≤ 4 * k * pieces := by rw [e2, e4]; omega
    omega

/-- **Degree-`2` induced subgraph is a linear forest.** The subgraph of `T` induced on the
degree-`2` vertices `D` is acyclic (sub-forest of the tree) and has maximum degree `≤ 2` (each such
vertex has only its `2` `T`-neighbours available). An acyclic graph of max degree `≤ 2` is a
disjoint union of paths, so the connected components of `T[D]` are exactly the maximal bare
segments of `T` — the objects cut into length-`k` bare paths in `split`. -/
theorem induce_deg_two_linearForest {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree) :
    (T.induce {v | T.degree v = 2}).IsAcyclic ∧
      ∀ w : {v | T.degree v = 2}, (T.induce {v | T.degree v = 2}).degree w ≤ 2 := by
  refine ⟨hT.IsAcyclic.induce _, fun w => ?_⟩
  have hle : (T.induce {v | T.degree v = 2}).degree w ≤ T.degree (w : V) := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
    apply Finset.card_le_card_of_injOn Subtype.val
    · intro x hx
      simp only [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hx ⊢
      exact hx
    · intro a _ b _ h; exact Subtype.ext h
  have hw : T.degree (w : V) = 2 := w.2
  omega

open Classical in
/-- **Vertex partition by connected component.** The vertex count splits as the sum, over connected
components, of the component fibre sizes. This is the vertex half of the forest component identity
`#components + #edges = |V|` used to count the maximal bare segments in `split`. -/
theorem card_eq_sum_card_component_fiber {V : Type*} [Fintype V] (G : SimpleGraph V) :
    Fintype.card V
      = ∑ C : G.ConnectedComponent, (univ.filter (fun v => G.connectedComponentMk v = C)).card := by
  rw [← Finset.card_univ]
  exact Finset.card_eq_sum_card_fiberwise (fun v _ => Finset.mem_univ _)

open Classical in
/-- **Component fibre cardinality.** The number of vertices in a connected component equals the
size of its fibre under `connectedComponentMk` (`v ∈ C` is by definition `connectedComponentMk v = C`).
Bridges the fibre form of `card_eq_sum_card_component_fiber` to the per-component tree identity. -/
theorem card_component_eq_card_fiber {V : Type*} [Fintype V] (G : SimpleGraph V)
    (C : G.ConnectedComponent) :
    Fintype.card C = (univ.filter (fun v => G.connectedComponentMk v = C)).card := by
  rw [← Fintype.card_subtype]
  exact Fintype.card_congr (Equiv.subtypeEquivRight (fun v => ⟨id, id⟩))

/-- **Forest identity, tree-sum form.** For a finite acyclic graph, the vertex count equals the
total edge count *summed over connected components* plus the number of components. Combines the
vertex partition (`card_eq_sum_card_component_fiber`), the fibre cardinality
(`card_component_eq_card_fiber`), and the per-component tree identity (`IsTree.card_edgeFinset` on
each `c.toSimpleGraph`). The closing `congr`/`ext` reconciles the two `Fintype`-instances on the
component edge set (`Finset.card` is instance-independent). -/
theorem card_eq_sum_component_edgeFinset_add {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsAcyclic) :
    Fintype.card V
      = (∑ C : G.ConnectedComponent, (C.toSimpleGraph).edgeFinset.card)
        + Fintype.card G.ConnectedComponent := by
  classical
  rw [← Finset.card_univ (α := V),
      Finset.card_eq_sum_card_fiberwise
        (fun (v : V) _ => Finset.mem_univ (G.connectedComponentMk v)),
      show (Fintype.card G.ConnectedComponent) = ∑ _C : G.ConnectedComponent, 1 by
        simp [Finset.card_univ],
      ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun C _ => ?_)
  have h1 : (univ.filter (fun v => G.connectedComponentMk v = C)).card = Fintype.card C := by
    rw [← Fintype.card_subtype]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun v => ⟨id, id⟩))
  rw [h1, ← (hG.isTree_connectedComponent C).card_edgeFinset]
  congr 2
  ext e
  simp only [SimpleGraph.mem_edgeFinset]

/-- **Edge partition by connected component.** Every edge lies in exactly one component (its
endpoints are adjacent, hence in the same component), so the edge count is the sum of the
per-component edge counts. Combined with `card_eq_sum_component_edgeFinset_add` this yields the full
forest identity `#components + #edges = |V|`. -/
theorem card_edgeFinset_eq_sum_component {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.edgeFinset.card = ∑ C : G.ConnectedComponent, (C.toSimpleGraph).edgeFinset.card := by
  classical
  let emb : ∀ C : G.ConnectedComponent, Sym2 (C : Type _) ↪ Sym2 V :=
    fun _ => ⟨Sym2.map Subtype.val, Sym2.map.injective Subtype.val_injective⟩
  have key : G.edgeFinset
      = Finset.univ.biUnion (fun C : G.ConnectedComponent =>
          (C.toSimpleGraph.edgeFinset).map (emb C)) := by
    ext e
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_map,
      SimpleGraph.mem_edgeFinset]
    constructor
    · induction e using Sym2.ind with
      | _ a b =>
        intro hab
        rw [SimpleGraph.mem_edgeSet] at hab
        have ha : a ∈ G.connectedComponentMk a := rfl
        have hb : b ∈ G.connectedComponentMk a :=
          (G.connectedComponentMk a).mem_supp_of_adj_mem_supp ha hab
        refine ⟨G.connectedComponentMk a, s(⟨a, ha⟩, ⟨b, hb⟩), ?_, ?_⟩
        · rw [SimpleGraph.mem_edgeSet, SimpleGraph.ConnectedComponent.toSimpleGraph_adj]; exact hab
        · simp [emb]
    · rintro ⟨C, e', he', heq⟩
      rw [← heq]
      induction e' using Sym2.ind with
      | _ x y =>
        rw [SimpleGraph.mem_edgeSet, SimpleGraph.ConnectedComponent.toSimpleGraph_adj] at he'
        simp only [emb, Function.Embedding.coeFn_mk, Sym2.map_pair_eq]
        rw [SimpleGraph.mem_edgeSet]; exact he'
  rw [key, Finset.card_biUnion]
  · refine Finset.sum_congr rfl (fun C _ => ?_)
    rw [Finset.card_map]
    congr 1
    ext e
    simp only [SimpleGraph.mem_edgeFinset]
  · intro C _ C' _ hCC'
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    rintro e he he'
    rw [Finset.mem_map] at he he'
    obtain ⟨e1, _, rfl⟩ := he
    obtain ⟨e2, _, he2⟩ := he'
    apply hCC'
    induction e1 using Sym2.ind with
    | _ a b =>
      induction e2 using Sym2.ind with
      | _ x y =>
        simp only [emb, Function.Embedding.coeFn_mk, Sym2.map_pair_eq, Sym2.eq_iff] at he2
        have hCa : G.connectedComponentMk (a : V) = C := a.2
        have hCb : G.connectedComponentMk (b : V) = C := b.2
        have hCx : G.connectedComponentMk (x : V) = C' := x.2
        rcases he2 with ⟨h1, _⟩ | ⟨h1, _⟩
        · rw [← hCa, ← hCx, h1]
        · rw [← hCb, ← hCx, h1]

/-- **Forest component identity.** A finite acyclic graph satisfies
`#components + #edges = #vertices`. (Combines the tree-sum form with the edge partition.) -/
theorem card_connectedComponent_add_card_edgeFinset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsAcyclic) :
    Fintype.card G.ConnectedComponent + G.edgeFinset.card = Fintype.card V := by
  rw [card_eq_sum_component_edgeFinset_add G hG, card_edgeFinset_eq_sum_component G,
    Nat.add_comm]

/-- **Handshake on a subset.** The number of edges incident to a vertex set `W` is at most the sum
of the degrees over `W` (each incident edge has an endpoint in `W`; the edges incident to `W` are
the union of the incidence sets). -/
theorem card_biUnion_incidenceFinset_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) :
    (W.biUnion (fun v => G.incidenceFinset v)).card ≤ ∑ v ∈ W, G.degree v :=
  Finset.card_biUnion_le.trans
    (le_of_eq (Finset.sum_congr rfl (fun v _ => G.card_incidenceFinset_eq_degree v)))

/-- **Component count of the degree-`2` subgraph.** Specialising the forest component identity to
`T[D]` (acyclic, the linear forest on degree-`2` vertices): the number of maximal bare segments
plus the number of degree-`2`-internal edges equals the number of degree-`2` vertices. -/
theorem card_component_induce_deg_two_add {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree) :
    Fintype.card (T.induce {v | T.degree v = 2}).ConnectedComponent
        + (T.induce {v | T.degree v = 2}).edgeFinset.card
      = Fintype.card {v | T.degree v = 2} :=
  card_connectedComponent_add_card_edgeFinset (T.induce {v | T.degree v = 2})
    (hT.IsAcyclic.induce _)

/-- **Bare-segment count bound.** The number of maximal bare segments (connected components of the
degree-`2` induced subgraph) is at most `#leaves + #branch − 1`. Proof: the forest component
identity gives `#segments + e_D = |D|`; every edge of `T` either lies within `D` (contributing to
`e_D`) or is incident to a non-degree-`2` vertex, and the latter number at most `∑_{v∉D} deg v =
2(#leaves+#branch−1)` by the handshake; combined with the vertex partition this bounds `#segments`. -/
theorem card_component_induce_deg_two_le {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree) (hn : 2 ≤ Fintype.card V) :
    Fintype.card (T.induce {v | T.degree v = 2}).ConnectedComponent + 1
      ≤ {v | T.degree v = 1}.toFinset.card + {v | 3 ≤ T.degree v}.toFinset.card := by
  classical
  have hid := card_component_induce_deg_two_add T hT
  have hcardD : Fintype.card {v | T.degree v = 2} = {v | T.degree v = 2}.toFinset.card :=
    (Set.toFinset_card _).symm
  have hpart := card_vert_eq_card_leaves_add T hT hn
  have hedge : T.edgeFinset.card + 1 = Fintype.card V := hT.card_edgeFinset
  have hcompl := sum_degree_compl_deg_two_add_two T hT hn
  let embD : Sym2 ({v | T.degree v = 2} : Set V) ↪ Sym2 V :=
    ⟨Sym2.map Subtype.val, Sym2.map.injective Subtype.val_injective⟩
  have hcover : T.edgeFinset ⊆ ((T.induce {v | T.degree v = 2}).edgeFinset.map embD)
      ∪ ({v | T.degree v = 2}.toFinsetᶜ.biUnion (fun v => T.incidenceFinset v)) := by
    intro e he
    rw [SimpleGraph.mem_edgeFinset] at he
    rw [Finset.mem_union]
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeSet] at he
      by_cases ha : T.degree a = 2
      · by_cases hb : T.degree b = 2
        · refine Or.inl ?_
          rw [Finset.mem_map]
          refine ⟨s(⟨a, ha⟩, ⟨b, hb⟩), ?_, ?_⟩
          · rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]; exact he
          · simp only [embD, Function.Embedding.coeFn_mk, Sym2.map_pair_eq]
        · refine Or.inr ?_
          rw [Finset.mem_biUnion]
          refine ⟨b, ?_, ?_⟩
          · simp only [Finset.mem_compl, Set.mem_toFinset, Set.mem_setOf_eq]; exact hb
          · rw [SimpleGraph.incidenceFinset_eq_filter, Finset.mem_filter]
            exact ⟨by rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]; exact he,
              Sym2.mem_mk_right a b⟩
      · refine Or.inr ?_
        rw [Finset.mem_biUnion]
        refine ⟨a, ?_, ?_⟩
        · simp only [Finset.mem_compl, Set.mem_toFinset, Set.mem_setOf_eq]; exact ha
        · rw [SimpleGraph.incidenceFinset_eq_filter, Finset.mem_filter]
          exact ⟨by rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]; exact he,
            Sym2.mem_mk_left a b⟩
  have htouch : ({v | T.degree v = 2}.toFinsetᶜ.biUnion (fun v => T.incidenceFinset v)).card
      ≤ ∑ v ∈ {v | T.degree v = 2}.toFinsetᶜ, T.degree v :=
    card_biUnion_incidenceFinset_le T _
  have hcov : T.edgeFinset.card
      ≤ (T.induce {v | T.degree v = 2}).edgeFinset.card
        + ({v | T.degree v = 2}.toFinsetᶜ.biUnion (fun v => T.incidenceFinset v)).card := by
    calc T.edgeFinset.card ≤ _ := Finset.card_le_card hcover
      _ ≤ _ := Finset.card_union_le _ _
      _ = _ := by rw [Finset.card_map]
  omega

/-- **Split assembly arithmetic (corrected, vertex-disjoint variant).** The honest count for the
geometric extraction in `split`. Cutting each of the `M` maximal bare segments (vertex lists) into
disjoint blocks of `k + 1` vertices yields `pieces` length-`k` bare paths satisfying
`n ≤ (k+1)·pieces + M·k + s` (from `sum_le_mul_sum_div_add` on the segment vertex-counts, with
`|D| = n − s` and `s = #leaves + #branch`). With the segment count small (`M + 1 ≤ s`) and few
leaves (`2·s·k < n`), this forces `pieces ≥ n/(4k)` for `k ≥ 3`. (The earlier `split_piece_count`
and `split_piece_count_succ` assumed a `(k−1)` segment coefficient, which the disjoint
`(k+1)`-vertex cut does not produce; this lemma carries the correct `k` coefficient.) -/
theorem split_assembly (n k pieces M s : ℕ) (hk : 2 < k)
    (h1 : n ≤ (k + 1) * pieces + M * k + s) (h2 : M + 1 ≤ s) (h4 : 2 * (s * k) < n) :
    n / (4 * k) ≤ pieces := by
  apply Nat.div_le_of_le_mul
  nlinarith [h1, h2, h4, hk, Nat.mul_le_mul h2 (le_refl k),
    Nat.mul_le_mul (show 3 ≤ k by omega) (le_refl (pieces + s))]

/-- **Boundary edge.** A walk from outside a vertex set `S` to inside `S` contains an edge crossing
the boundary: some adjacent pair `u, v` with `u ∉ S` and `v ∈ S`. (Induct on the walk: at the first
step either the second vertex is already in `S` — giving the crossing edge — or recurse.) -/
theorem exists_boundary_edge {V : Type*} {G : SimpleGraph V} {S : Set V}
    {x y : V} (q : G.Walk x y) (hy : y ∈ S) (hx : x ∉ S) :
    ∃ u v, G.Adj u v ∧ u ∉ S ∧ v ∈ S := by
  induction q with
  | nil => exact absurd hy hx
  | @cons x z y h q' ih =>
    by_cases hz : z ∈ S
    · exact ⟨x, z, h, hx, hz⟩
    · exact ih hy hz

/-- **Spanning path from bounded degree.** A finite, connected, acyclic graph of maximum degree
`≤ 2` has a Hamiltonian (spanning) path: its longest path visits every vertex. (Take a longest path;
an off-path vertex reached by connectivity would either force an endpoint extension — contradicting
maximality — or give a path vertex a third neighbour — contradicting `deg ≤ 2`.) The components of
`T.induce {deg = 2}` are exactly such graphs, so this linearises each maximal bare segment into a
`List V` (its `support`) for the cutting step of `split`. -/
theorem exists_spanning_path_of_maxdeg_two {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (hacyc : G.IsAcyclic) (hdeg : ∀ v, G.degree v ≤ 2) :
    ∃ (a b : V) (p : G.Walk a b), p.IsPath ∧ ∀ w, w ∈ p.support := by
  haveI : Nonempty V := hconn.nonempty
  obtain ⟨a, b, p, hp, hmax⟩ := Walk.exists_isPath_forall_isPath_length_le_length G
  refine ⟨a, b, p, hp, fun w => ?_⟩
  by_contra hw
  obtain ⟨q⟩ := hconn.preconnected w a
  obtain ⟨x, y, hxy, hxns, hyns⟩ :=
    exists_boundary_edge q (S := {v | v ∈ p.support}) p.start_mem_support hw
  simp only [Set.mem_setOf_eq] at hxns hyns
  rw [Walk.mem_support_iff_exists_getVert] at hyns
  obtain ⟨i, hyi, hil⟩ := hyns
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · -- `y = a` (start): prepend `x` to get a longer path, contradicting maximality.
    subst hi0
    rw [p.getVert_zero] at hyi
    subst hyi
    have hlong : (Walk.cons hxy p).IsPath := (Walk.cons_isPath_iff hxy p).2 ⟨hp, hxns⟩
    have := hmax x b (Walk.cons hxy p) hlong
    simp only [Walk.length_cons] at this
    omega
  · rcases Nat.lt_or_ge i p.length with hilt | hige
    · -- interior `0 < i < length`: `y` has two path-neighbours plus `x`, so `deg y ≥ 3`.
      have h2 : (p.toSubgraph.neighborSet y).ncard = 2 := by
        have h := hp.ncard_neighborSet_toSubgraph_internal_eq_two (by omega : i ≠ 0) hilt
        rwa [hyi] at h
      have hsub : p.toSubgraph.neighborSet y ⊆ G.neighborSet y := fun z hz =>
        p.toSubgraph.adj_sub hz
      have hxN : x ∈ G.neighborSet y := hxy.symm
      have hxnS : x ∉ p.toSubgraph.neighborSet y := fun hxS =>
        hxns (p.mem_verts_toSubgraph.mp (p.toSubgraph.edge_vert (p.toSubgraph.symm hxS)))
      have h3 : (insert x (p.toSubgraph.neighborSet y)).ncard = 3 := by
        rw [Set.ncard_insert_of_notMem hxnS (Set.toFinite _), h2]
      have hge : 3 ≤ (G.neighborSet y).ncard := by
        rw [← h3]
        exact Set.ncard_le_ncard (Set.insert_subset_iff.mpr ⟨hxN, hsub⟩) (Set.toFinite _)
      have hd : (G.neighborSet y).ncard = G.degree y := by
        rw [Set.ncard_eq_toFinset_card', Set.toFinset_card, card_neighborSet_eq_degree]
      have := hdeg y
      omega
    · -- `i = length`, so `y = b` (end): append `x`, contradicting maximality.
      have hlen : i = p.length := le_antisymm hil hige
      subst hlen
      rw [p.getVert_length] at hyi
      subst hyi
      have hxr : x ∉ p.reverse.support := by rw [Walk.support_reverse, List.mem_reverse]; exact hxns
      have hlong : (Walk.cons hxy p.reverse).IsPath :=
        (Walk.cons_isPath_iff hxy p.reverse).2 ⟨hp.reverse, hxr⟩
      have := hmax x a (Walk.cons hxy p.reverse) hlong
      simp only [Walk.length_cons, Walk.length_reverse] at this
      omega

/-- **Forests have a low-degree vertex.** A nonempty finite acyclic graph has a vertex of degree
`≤ 1`. (Handshake: `∑ deg = 2·#edges = 2(|V| − #components) ≤ 2(|V|−1) < 2|V|`, so the average degree
is below `2`.) The peeling step for the forest vertex-ordering used in the Case C greedy embedding. -/
theorem exists_degree_le_one_of_acyclic {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.IsAcyclic) [Nonempty V] :
    ∃ v, G.degree v ≤ 1 := by
  by_contra h
  push_neg at h
  have hsum : ∑ v, G.degree v = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
  have hid : Fintype.card G.ConnectedComponent + G.edgeFinset.card = Fintype.card V :=
    card_connectedComponent_add_card_edgeFinset G hG
  have hcomp : 1 ≤ Fintype.card G.ConnectedComponent := Fintype.card_pos
  have hge : 2 * Fintype.card V ≤ ∑ v, G.degree v := by
    calc 2 * Fintype.card V = ∑ _v : V, 2 := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
      _ ≤ ∑ v, G.degree v := Finset.sum_le_sum (fun v _ => by have := h v; omega)
  omega


/-- **Forest vertex-ordering.** The vertices of a finite acyclic graph (restricted to any `Finset S`)
can be listed so that every vertex has at most one neighbour earlier in the list. (Strong induction
on `|S|`: peel a degree-`≤1` vertex of the induced subforest off the end.) The order along which the
Case C greedy embedding places vertices — each new vertex has a unique already-placed neighbour. -/
theorem exists_forest_order {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.IsAcyclic) (S : Finset V) :
    ∃ L : List V, L.Nodup ∧ L.toFinset = S ∧
      ∀ j (hj : j < L.length), ((L.take j).filter (fun u => G.Adj u L[j])).length ≤ 1 := by
  induction S using Finset.strongInduction with
  | _ S ih =>
    rcases S.eq_empty_or_nonempty with rfl | hne
    · exact ⟨[], by simp, by simp, by simp⟩
    · haveI : Nonempty (S : Set V) := hne.coe_sort
      obtain ⟨w, hw⟩ := exists_degree_le_one_of_acyclic (G.induce (S : Set V)) (hG.induce _)
      set v : V := (w : V) with hv
      have hvS : v ∈ S := Finset.mem_coe.mp w.2
      have hdeg : (S.filter (fun u => G.Adj v u)).card ≤ 1 := by
        have himg : ((G.induce (S : Set V)).neighborFinset w).image Subtype.val
            = S.filter (fun u => G.Adj v u) := by
          ext u
          simp only [Finset.mem_image, SimpleGraph.mem_neighborFinset, Finset.mem_filter]
          constructor
          · rintro ⟨w', hw', rfl⟩
            exact ⟨Finset.mem_coe.mp w'.2, hw'⟩
          · rintro ⟨huS, hadj⟩
            exact ⟨⟨u, Finset.mem_coe.mpr huS⟩, hadj, rfl⟩
        rw [← himg, Finset.card_image_of_injOn (Set.injOn_of_injective Subtype.val_injective),
          SimpleGraph.card_neighborFinset_eq_degree]
        exact hw
      obtain ⟨L', hL'nd, hL'tf, hL'ord⟩ := ih (S.erase v) (Finset.erase_ssubset hvS)
      refine ⟨L' ++ [v], ?_, ?_, ?_⟩
      · rw [List.nodup_append]
        refine ⟨hL'nd, List.nodup_singleton v, ?_⟩
        intro a ha b hb hab
        rw [List.mem_singleton] at hb
        subst hb; subst hab
        rw [← List.mem_toFinset, hL'tf] at ha
        exact Finset.notMem_erase v S ha
      · rw [List.toFinset_append, hL'tf]
        simp only [List.toFinset_cons, List.toFinset_nil, Finset.union_insert, Finset.union_empty]
        exact Finset.insert_erase hvS
      · intro j hj
        rw [List.length_append, List.length_singleton] at hj
        rcases Nat.lt_or_ge j L'.length with hjl | hjg
        · rw [List.getElem_append_left hjl, List.take_append_of_le_length (le_of_lt hjl)]
          exact hL'ord j hjl
        · have hjeq : j = L'.length := by omega
          subst hjeq
          have hget : (L' ++ [v])[L'.length] = v := by
            rw [List.getElem_append_right (le_refl _)]; simp
          rw [hget, List.take_append_of_le_length (le_refl _), List.take_length]
          calc (L'.filter (fun u => G.Adj u v)).length
              ≤ (S.filter (fun u => G.Adj v u)).card := ?_
            _ ≤ 1 := hdeg
          rw [← List.toFinset_card_of_nodup (hL'nd.filter _)]
          apply Finset.card_le_card
          intro u hu
          simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hu
          simp only [Finset.mem_filter]
          exact ⟨Finset.mem_of_mem_erase (hL'tf ▸ List.mem_toFinset.mpr hu.1),
            (G.adj_comm u v).mp hu.2⟩

/-- **Block decomposition.** A `Nodup`, `R`-chained list of length `ℓ` splits into `⌊ℓ/(m+1)⌋`
consecutive length-`(m+1)` blocks (`blk j = (L.drop (j(m+1))).take (m+1)`), each an `R`-chain whose
elements lie in `L`, pairwise (set-)disjoint. The vertex-disjoint cutting step of `split`. -/
theorem exists_blocks {V : Type*} [DecidableEq V] {R : V → V → Prop} (L : List V)
    (hnd : L.Nodup) (hch : L.IsChain R) (m : ℕ) :
    ∃ B : Finset (List V), B.card = L.length / (m + 1) ∧
      (∀ b ∈ B, b.length = m + 1 ∧ b.IsChain R ∧ b.Nodup ∧ ∀ v ∈ b, v ∈ L) ∧
      (∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → Disjoint b.toFinset b'.toFinset) := by
  classical
  set q := L.length / (m + 1) with hq
  set blk : ℕ → List V := fun j => (L.drop (j * (m + 1))).take (m + 1) with hblk
  have hsub : ∀ j, ∀ v ∈ blk j, v ∈ L := fun j v hv =>
    List.drop_subset _ _ (List.take_subset _ _ hv)
  have hndblk : ∀ j, (blk j).Nodup := fun j =>
    List.Nodup.sublist ((List.take_sublist _ _).trans (List.drop_sublist _ _)) hnd
  have hchain : ∀ j, (blk j).IsChain R := fun j => (hch.drop _).take _
  have hlen : ∀ j, j < q → (blk j).length = m + 1 := by
    intro j hj
    have hmul : (j + 1) * (m + 1) = j * (m + 1) + (m + 1) := by ring
    have hle : (j + 1) * (m + 1) ≤ L.length :=
      (Nat.mul_le_mul (Nat.succ_le_of_lt hj) (le_refl (m + 1))).trans (Nat.div_mul_le_self _ _)
    simp only [hblk, List.length_take, List.length_drop]
    omega
  have hdisjL : ∀ j j', j < j' → (blk j).Disjoint (blk j') := by
    intro j j' hjj' v hvj hvj'
    have hbj : v ∈ L.take ((j + 1) * (m + 1)) := by
      rw [show (j + 1) * (m + 1) = j * (m + 1) + (m + 1) from by ring, List.take_add]
      exact List.mem_append.mpr (Or.inr hvj)
    have hbj' : v ∈ L.drop (j' * (m + 1)) := List.take_subset _ _ hvj'
    have hle : (j + 1) * (m + 1) ≤ j' * (m + 1) := Nat.mul_le_mul (Nat.succ_le_of_lt hjj') (le_refl _)
    exact List.disjoint_take_drop hnd hle hbj hbj'
  have hne : ∀ j, j < q → blk j ≠ [] := fun j hj h0 => by
    have := hlen j hj; rw [h0, List.length_nil] at this; omega
  have hinj : Set.InjOn blk ↑(Finset.range q) := by
    intro j hj j' hj' he
    simp only [Finset.coe_range, Set.mem_Iio] at hj hj'
    by_contra hjj
    rcases Nat.lt_or_ge j j' with h | h
    · obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil _ (hne j hj)
      exact hdisjL j j' h hv (he ▸ hv)
    · obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil _ (hne j' hj')
      exact hdisjL j' j (by omega) hv (he ▸ hv)
  refine ⟨(Finset.range q).image blk, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  · intro b hb
    rw [Finset.mem_image] at hb
    obtain ⟨j, hj, rfl⟩ := hb
    exact ⟨hlen j (Finset.mem_range.mp hj), hchain j, hndblk j, hsub j⟩
  · intro b hb b' hb' hbb'
    rw [Finset.mem_image] at hb hb'
    obtain ⟨j, hj, rfl⟩ := hb
    obtain ⟨j', hj', rfl⟩ := hb'
    rw [Finset.disjoint_left]
    intro v hv hv'
    rw [List.mem_toFinset] at hv hv'
    rcases Nat.lt_trichotomy j j' with h | h | h
    · exact hdisjL j j' h hv hv'
    · exact hbb' (h ▸ rfl)
    · exact hdisjL j' j h hv' hv

open Classical in
/-- **Component as a vertex list.** Each connected component of a finite acyclic graph of maximum
degree `≤ 2` (a path) linearises into a `Nodup`, `G.Adj`-chained `List V` covering exactly that
component's vertices. Obtained from the component's spanning path (`exists_spanning_path_of_maxdeg_two`
applied to `C.toSimpleGraph`) mapped back along `Subtype.val`. -/
theorem exists_component_path {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hacyc : G.IsAcyclic) (hdeg : ∀ v, G.degree v ≤ 2)
    (C : G.ConnectedComponent) :
    ∃ L : List V, L.Nodup ∧ L.IsChain G.Adj ∧ (∀ v ∈ L, G.connectedComponentMk v = C) ∧
      L.length = (Finset.univ.filter (fun v => G.connectedComponentMk v = C)).card := by
  classical
  have hCacyc : C.toSimpleGraph.IsAcyclic := (hacyc.isTree_connectedComponent C).IsAcyclic
  have hCconn : C.toSimpleGraph.Connected := (hacyc.isTree_connectedComponent C).isConnected
  have hCdeg : ∀ w, C.toSimpleGraph.degree w ≤ 2 := by
    intro w
    refine le_trans ?_ (hdeg (w : V))
    rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
    apply Finset.card_le_card_of_injOn Subtype.val
    · intro x hx
      simp only [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hx ⊢
      exact (C.toSimpleGraph_adj w.2 x.2).mp hx
    · intro a _ b _ h; exact Subtype.ext h
  obtain ⟨a, b, p, hp, hcov⟩ :=
    exists_spanning_path_of_maxdeg_two C.toSimpleGraph hCconn hCacyc hCdeg
  refine ⟨p.support.map Subtype.val,
    (List.nodup_map_iff Subtype.val_injective).mpr hp.support_nodup, ?_, ?_, ?_⟩
  · refine List.isChain_map_of_isChain Subtype.val ?_ p.isChain_adj_support
    intro u v huv
    exact (C.toSimpleGraph_adj u.2 v.2).mp huv
  · intro v hv
    rw [List.mem_map] at hv
    obtain ⟨w, _, rfl⟩ := hv
    exact (ConnectedComponent.mem_supp_iff C ↑w).mp w.2
  · rw [List.length_map]
    have htf : p.support.toFinset = Finset.univ := by ext w; simp [hcov w]
    rw [← List.toFinset_card_of_nodup hp.support_nodup, htf, Finset.card_univ,
      card_component_eq_card_fiber G C]

/-- **Finset chunking bound.** Summing `fᵢ ≤ k·(fᵢ/k) + (k−1)` over a finite index set: the
`Finset` analogue of `sum_le_mul_sum_div_add`, used to bound `∑_C |C|` by the per-component block
counts in `split`. -/
theorem finset_sum_le_mul_sum_div_add {ι : Type*} (s : Finset ι) (f : ι → ℕ) (k : ℕ) (hk : 0 < k) :
    ∑ i ∈ s, f i ≤ k * (∑ i ∈ s, f i / k) + s.card * (k - 1) := by
  calc ∑ i ∈ s, f i
      ≤ ∑ i ∈ s, (k * (f i / k) + (k - 1)) := Finset.sum_le_sum (fun i _ => by
        have := Nat.div_add_mod (f i) k; have hmod : f i % k < k := Nat.mod_lt _ hk; omega)
    _ = k * (∑ i ∈ s, f i / k) + s.card * (k - 1) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, smul_eq_mul]

set_option maxHeartbeats 1000000 in
/-- **Split lemma (folklore, montgomery2018spanning).** A tree on $n$ vertices has at least
$n/(4k)$ leaves, or at least $n/(4k)$ vertex-disjoint bare paths of length $k$ (internal vertices of
degree $2$). This underpins the case division (Lemma 2.2). The leaf-vs-branch count is supplied by
`card_branch_add_two_le_card_leaves`; the remaining content is the bare-path extraction: when there
are few leaves, the degree-$2$ vertices (which vastly outnumber the $< 3\cdot\#\text{leaves}$ maximal
bare segments) yield many disjoint length-$k$ subpaths. -/
theorem split {V : Type*} [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj]
    (hT : T.IsTree) (k : ℕ) (hk : 2 < k) :
    (Fintype.card V) / (4 * k) ≤ {v | T.degree v = 1}.toFinset.card
    ∨ ∃ paths : Finset (List V),
        (Fintype.card V) / (4 * k) ≤ paths.card ∧
        (∀ P ∈ paths, P.Chain' T.Adj ∧ P.Nodup ∧ P.length = k + 1 ∧
          (∀ v ∈ P.tail.dropLast, T.degree v = 2)) ∧
        (∀ P ∈ paths, ∀ Q ∈ paths, P ≠ Q → Disjoint P.toFinset Q.toFinset) := by
  -- Case on the left disjunct (few vs. many leaves) is immediate; the right disjunct is the
  -- bare-path construction (MPS §3.3). The arithmetic/counting ingredients are now ALL in place:
  --   • `card_lt_two_mul_card_deg_two`           : few leaves ⟹ `n < 2|D|`  (step (a))
  --   • `card_component_induce_deg_two_le`       : `#maximal-bare-segments + 1 ≤ L + B`,
  --       i.e. `#segments ≤ L + B - 1` — the full forest component identity (step (b)/(c)),
  --       proven in this file via `card_component_induce_deg_two_add` +
  --       `card_connectedComponent_add_card_edgeFinset` (NOT just the `≤` half).
  --   • `sum_degree_compl_deg_two_add_two`       : handshake `∑_{v∉D} deg = 2(L+B-1)` (step (c))
  --   • `sum_le_mul_sum_div_add` / `split_piece_count_succ` : per-segment length-`k` cut count (d)
  -- What remains is ONLY the geometric extraction (step (d)): linearise each connected component of
  -- `T.induce {v | T.degree v = 2}` (an `IsAcyclic` graph of max degree ≤ 2, i.e. a path — see
  -- `induce_deg_two_linearForest`) into a concrete `List V`, cut it into length-`(k+1)` subpaths
  -- with degree-`2` interiors, prove the subpaths are pairwise `Disjoint .toFinset`, and conclude
  -- the count `≥ n/(4k)` via `split_assembly`.
  rcases Nat.lt_or_ge {v | T.degree v = 1}.toFinset.card (Fintype.card V / (4 * k)) with hfew | hmany
  · refine Or.inr ?_
    -- Few leaves: derive `n ≥ 4k ≥ 2` and `#leaves·4k < n`, hence `n < 2|D|` (deg-2 abundance).
    have h4k : 4 * k ≤ Fintype.card V := by
      rcases Nat.eq_zero_or_pos (Fintype.card V / (4 * k)) with h0 | hpos
      · omega
      · have := (Nat.le_div_iff_mul_le (show 0 < 4 * k by omega)).mp hpos; omega
    have hn : 2 ≤ Fintype.card V := by omega
    have hfew' : {v | T.degree v = 1}.toFinset.card * (4 * k) < Fintype.card V := by
      have h1 : {v | T.degree v = 1}.toFinset.card + 1 ≤ Fintype.card V / (4 * k) := hfew
      have h2 := (Nat.le_div_iff_mul_le (show 0 < 4 * k by omega)).mp h1
      have h3 : ({v | T.degree v = 1}.toFinset.card + 1) * (4 * k)
          = {v | T.degree v = 1}.toFinset.card * (4 * k) + 4 * k := by ring
      omega
    have hD2 : Fintype.card V < 2 * {v | T.degree v = 2}.toFinset.card :=
      card_lt_two_mul_card_deg_two T hT hn k (by omega) hfew'
    classical
    obtain ⟨hG'acyc, hG'deg⟩ := induce_deg_two_linearForest T hT
    choose LD hLDnd hLDch hLDmem hLDlen using
      fun C => exists_component_path (T.induce {v | T.degree v = 2}) hG'acyc hG'deg C
    set sC : (T.induce {v | T.degree v = 2}).ConnectedComponent → List V :=
      fun C => (LD C).map Subtype.val with hsCdef
    have hsCnd : ∀ C, (sC C).Nodup := fun C =>
      (List.nodup_map_iff Subtype.val_injective).mpr (hLDnd C)
    have hsCch : ∀ C, (sC C).IsChain T.Adj := fun C =>
      List.isChain_map_of_isChain Subtype.val (fun _ _ hab => hab) (hLDch C)
    have hsCdeg : ∀ C, ∀ v ∈ sC C, T.degree v = 2 := by
      intro C v hv
      rw [hsCdef, List.mem_map] at hv
      obtain ⟨w, _, rfl⟩ := hv; exact w.2
    have hsCdisj : ∀ C C', C ≠ C' → ∀ v, v ∈ sC C → v ∈ sC C' → False := by
      intro C C' hne v hvC hvC'
      rw [hsCdef] at hvC hvC'
      simp only [List.mem_map] at hvC hvC'
      obtain ⟨w, hwC, rfl⟩ := hvC
      obtain ⟨w', hw'C', hww'⟩ := hvC'
      obtain rfl : w = w' := Subtype.val_injective hww'.symm
      exact hne ((hLDmem C w hwC).symm.trans (hLDmem C' w hw'C'))
    have hsClen : ∀ C, (sC C).length
        = (Finset.univ.filter fun v => (T.induce {v | T.degree v = 2}).connectedComponentMk v = C).card := by
      intro C; rw [hsCdef, List.length_map, hLDlen C]
    choose blk hblkcard hblkprop hblkdisj using
      fun C => exists_blocks (sC C) (hsCnd C) (hsCch C) k
    have hblkdisjC : ∀ C ∈ (Finset.univ : Finset _), ∀ C' ∈ (Finset.univ : Finset _),
        C ≠ C' → Disjoint (blk C) (blk C') := by
      intro C _ C' _ hne
      rw [Finset.disjoint_left]
      intro b hbC hbC'
      have hlen := (hblkprop C b hbC).1
      obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil b (by intro h; rw [h] at hlen; simp at hlen)
      exact hsCdisj C C' hne v ((hblkprop C b hbC).2.2.2 v hv) ((hblkprop C' b hbC').2.2.2 v hv)
    refine ⟨Finset.univ.biUnion blk, ?_, ?_, ?_⟩
    · rw [Finset.card_biUnion hblkdisjC]
      simp only [hblkcard]
      refine split_assembly (Fintype.card V) k _
        (Fintype.card (T.induce {v | T.degree v = 2}).ConnectedComponent)
        ({v | T.degree v = 1}.toFinset.card + {v | 3 ≤ T.degree v}.toFinset.card) hk ?_ ?_ ?_
      · have hsum : (∑ C, (sC C).length) = {v | T.degree v = 2}.toFinset.card := by
          rw [Set.toFinset_card, ← Finset.card_univ,
            Finset.card_eq_sum_card_fiberwise (fun (x : ↑{v | T.degree v = 2}) _ =>
              Finset.mem_univ ((T.induce {v | T.degree v = 2}).connectedComponentMk x))]
          refine Finset.sum_congr rfl fun C _ => ?_
          exact hsClen C
        have hfsum := finset_sum_le_mul_sum_div_add Finset.univ (fun C => (sC C).length) (k + 1)
          (by omega)
        rw [Finset.card_univ] at hfsum
        simp only [Nat.add_sub_cancel] at hfsum
        have hpart := card_vert_eq_card_leaves_add T hT hn
        omega
      · exact card_component_induce_deg_two_le T hT hn
      · have hbr := card_branch_add_two_le_card_leaves T hT hn
        have hs2 : {v | T.degree v = 1}.toFinset.card + {v | 3 ≤ T.degree v}.toFinset.card
            ≤ 2 * {v | T.degree v = 1}.toFinset.card := by omega
        have hmul := Nat.mul_le_mul hs2 (le_refl k)
        nlinarith [hfew', hmul]
    · intro P hP
      rw [Finset.mem_biUnion] at hP
      obtain ⟨C, _, hPC⟩ := hP
      obtain ⟨hlen, hch, hnd, hmem⟩ := hblkprop C P hPC
      exact ⟨hch, hnd, hlen, fun v hv =>
        hsCdeg C v (hmem v (List.tail_subset _ (List.dropLast_subset _ hv)))⟩
    · intro P hP Q hQ hPQ
      rw [Finset.mem_biUnion] at hP hQ
      obtain ⟨C, _, hPC⟩ := hP
      obtain ⟨C', _, hQC'⟩ := hQ
      by_cases hCC' : C = C'
      · subst hCC'; exact hblkdisj C P hPC Q hQC' hPQ
      · rw [Finset.disjoint_left]
        intro v hvP hvQ
        rw [List.mem_toFinset] at hvP hvQ
        exact hsCdisj C C' hCC' v ((hblkprop C P hPC).2.2.2 v hvP) ((hblkprop C' Q hQC').2.2.2 v hvQ)
  · exact Or.inl hmany

/-- **Case division via `split` (corrected small-δ form of `Lemma_case_division`).** For `δ ≤ 1/4`,
every finite `n`-edge tree lies in Case A or Case B (a fortiori the A/B/C trichotomy). Apply `split`
with `k = ⌊δ⁻¹⌋ ≥ 4 > 2`: the leaf branch yields Case A (leaves of a tree are pairwise
non-adjacent), the bare-path branch yields Case B. The original `CaseDivision.tree_split` is stated
for all `δ > 0`, which is false for large `δ`; this is its true form. -/
theorem tree_split_via_split (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4) (n : ℕ) {V : Type*} [Finite V]
    (T : SimpleGraph V) (hTree : T.IsTree) (hn : T.edgeSet.ncard = n) :
    Ringel.IsCaseA δ n T ∨ Ringel.IsCaseB δ n T ∨ Ringel.IsCaseC δ n T := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  have hδinv : (4 : ℝ) ≤ δ⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hδ]; rw [inv_eq_one_div]; exact hδ'
  have hk : 2 < ⌊δ⁻¹⌋₊ := by
    have : 4 ≤ ⌊δ⁻¹⌋₊ := Nat.le_floor (by push_cast; exact hδinv)
    omega
  have hcard : Fintype.card V = n + 1 := by
    have h1 := hTree.card_edgeFinset
    have h2 : T.edgeFinset.card = n := by
      rw [← hn, Set.ncard_eq_toFinset_card']; rfl
    omega
  rcases split T hTree ⌊δ⁻¹⌋₊ hk with hleaves | ⟨paths, hpcount, hpprop, hpdisj⟩
  · -- Many leaves ⟹ Case A.
    refine Or.inl ?_
    rcases Nat.lt_or_ge n 2 with hn1 | hn2
    · -- `n ≤ 1`: `⌊δ⁶ n⌋ = 0`, the empty set witnesses Case A.
      refine ⟨∅, by simp, by simp, ?_⟩
      have h0 : ⌊δ ^ 6 * (n : ℝ)⌋₊ = 0 := by
        apply Nat.floor_eq_zero.mpr
        have hn1' : (n : ℝ) ≤ 1 := by exact_mod_cast (by omega : n ≤ 1)
        have hδ6 : δ ^ 6 < 1 := by
          calc δ ^ 6 ≤ (1/4 : ℝ) ^ 6 := by gcongr
            _ < 1 := by norm_num
        have hprod : δ ^ 6 * (n : ℝ) ≤ δ ^ 6 := mul_le_of_le_one_right (by positivity) hn1'
        linarith
      simp [h0]
    · -- `n ≥ 2`: the leaves form an independent set of the required size.
      refine ⟨{v | T.degree v = 1}, ?_, ?_, ?_⟩
      · intro v hv
        simp only [Set.mem_setOf_eq] at hv
        rw [SimpleGraph.degree, Finset.card_eq_one] at hv
        obtain ⟨w, hw⟩ := hv
        refine ⟨w, ?_, fun u hu => ?_⟩
        · have hmem : w ∈ T.neighborFinset v := by rw [hw]; exact Finset.mem_singleton_self w
          rwa [SimpleGraph.mem_neighborFinset] at hmem
        · have hmem : u ∈ T.neighborFinset v := by rw [SimpleGraph.mem_neighborFinset]; exact hu
          rw [hw, Finset.mem_singleton] at hmem; exact hmem
      · intro v hv w hw hvw hadj
        simp only [Set.mem_setOf_eq] at hv hw
        have hNv : T.neighborFinset v = {w} := by
          rw [SimpleGraph.degree, Finset.card_eq_one] at hv
          obtain ⟨a, ha⟩ := hv
          have hm : w ∈ T.neighborFinset v := by rw [SimpleGraph.mem_neighborFinset]; exact hadj
          rw [ha, Finset.mem_singleton] at hm; rw [ha, hm]
        have hNw : T.neighborFinset w = {v} := by
          rw [SimpleGraph.degree, Finset.card_eq_one] at hw
          obtain ⟨a, ha⟩ := hw
          have hm : v ∈ T.neighborFinset w := by rw [SimpleGraph.mem_neighborFinset]; exact hadj.symm
          rw [ha, Finset.mem_singleton] at hm; rw [ha, hm]
        have hclosed : ∀ z y, T.Walk z y → (z = v ∨ z = w) → (y = v ∨ y = w) := by
          intro z y p
          induction p with
          | nil => intro hz; exact hz
          | @cons z b y hab q ih =>
            intro hz
            refine ih ?_
            rcases hz with rfl | rfl
            · right
              have hm : b ∈ T.neighborFinset z := by rw [SimpleGraph.mem_neighborFinset]; exact hab
              rw [hNv, Finset.mem_singleton] at hm; exact hm
            · left
              have hm : b ∈ T.neighborFinset z := by rw [SimpleGraph.mem_neighborFinset]; exact hab
              rw [hNw, Finset.mem_singleton] at hm; exact hm
        obtain ⟨x, hx⟩ : (({v, w} : Finset V)ᶜ).Nonempty := by
          rw [← Finset.card_pos, Finset.card_compl]
          have h2 : ({v, w} : Finset V).card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
          omega
        rw [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hx
        obtain ⟨hxv, hxw⟩ := hx
        obtain ⟨p⟩ := hTree.isConnected.preconnected v x
        rcases hclosed v x p (Or.inl rfl) with h | h
        · exact hxv h
        · exact hxw h
      · have hS : ({v | T.degree v = 1} : Set V).ncard = #{v | T.degree v = 1}.toFinset := by
          rw [Set.ncard_eq_toFinset_card']
        rw [hS]
        refine le_trans ?_ hleaves
        rw [hcard, Nat.le_div_iff_mul_le (by omega)]
        have hb1 : (⌊δ ^ 6 * (n : ℝ)⌋₊ : ℝ) ≤ δ ^ 6 * n := Nat.floor_le (by positivity)
        have hb2 : (⌊δ⁻¹⌋₊ : ℝ) ≤ δ⁻¹ := Nat.floor_le (by positivity)
        have hmain : ((⌊δ ^ 6 * (n : ℝ)⌋₊ * (4 * ⌊δ⁻¹⌋₊) : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
          push_cast
          have key : (⌊δ ^ 6 * (n:ℝ)⌋₊ : ℝ) * (4 * (⌊δ⁻¹⌋₊ : ℝ)) ≤ (δ ^ 6 * n) * (4 * δ⁻¹) :=
            mul_le_mul hb1 (by linarith) (by positivity) (by positivity)
          have hsimp : (δ ^ 6 * (n:ℝ)) * (4 * δ⁻¹) = 4 * δ ^ 5 * n := by field_simp
          have hδ5 : 4 * δ ^ 5 ≤ 1 := by
            have h : δ ^ 5 ≤ (1/4 : ℝ) ^ 5 := by gcongr
            nlinarith [h]
          have hn0 : (0:ℝ) ≤ (n:ℝ) := by positivity
          calc (⌊δ ^ 6 * (n:ℝ)⌋₊ : ℝ) * (4 * (⌊δ⁻¹⌋₊ : ℝ))
              ≤ 4 * δ ^ 5 * n := by rw [← hsimp]; exact key
            _ ≤ 1 * n := mul_le_mul_of_nonneg_right hδ5 hn0
            _ ≤ n + 1 := by linarith
        exact_mod_cast hmain
  · -- Many bare paths ⟹ Case B.
    refine Or.inr (Or.inl ?_)
    refine ⟨paths.toList, ?_, ?_, ?_, ?_⟩
    · intro P hP
      rw [Finset.mem_toList] at hP
      obtain ⟨hch, hnd, _, hint⟩ := hpprop P hP
      refine ⟨hch, hnd, fun v hv => ?_⟩
      have hdeg := hint v hv
      rw [Set.ncard_eq_toFinset_card', Set.toFinset_card, SimpleGraph.card_neighborSet_eq_degree]
      exact hdeg
    · intro P hP
      rw [Finset.mem_toList] at hP
      exact (hpprop P hP).2.2.1
    · intro P hP Q hQ hPQ
      rw [Finset.mem_toList] at hP hQ
      have hd := hpdisj P hP Q hQ hPQ
      have e1 : {v : V | v ∈ P} = (↑P.toFinset : Set V) := by ext v; simp [List.mem_toFinset]
      have e2 : {v : V | v ∈ Q} = (↑Q.toFinset : Set V) := by ext v; simp [List.mem_toFinset]
      rw [e1, e2, Finset.disjoint_coe]; exact hd
    · rw [Finset.length_toList]
      refine le_trans ?_ hpcount
      rw [hcard, Nat.le_div_iff_mul_le (by omega)]
      have hb1 : (⌊δ * (n : ℝ) / 800⌋₊ : ℝ) ≤ δ * n / 800 := Nat.floor_le (by positivity)
      have hb2 : (⌊δ⁻¹⌋₊ : ℝ) ≤ δ⁻¹ := Nat.floor_le (by positivity)
      have hmain : ((⌊δ * (n : ℝ) / 800⌋₊ * (4 * ⌊δ⁻¹⌋₊) : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
        push_cast
        have key : (⌊δ * (n : ℝ) / 800⌋₊ : ℝ) * (4 * (⌊δ⁻¹⌋₊ : ℝ)) ≤ (δ * n / 800) * (4 * δ⁻¹) :=
          mul_le_mul hb1 (by linarith) (by positivity) (by positivity)
        have hsimp : (δ * (n : ℝ) / 800) * (4 * δ⁻¹) = n / 200 := by field_simp; ring
        have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
        calc (⌊δ * (n : ℝ) / 800⌋₊ : ℝ) * (4 * (⌊δ⁻¹⌋₊ : ℝ))
            ≤ n / 200 := by rw [← hsimp]; exact key
          _ ≤ n + 1 := by linarith
      exact_mod_cast hmain

end Ringel.TreeStructure
