import Ringel.NearEmbeddingConcentration
import Ringel.NearEmbeddingSmallTree

/-!
# Finite joint laws for the disjoint reservoir splits in MPS §6

MPS §6 repeatedly asks for disjoint random reservoirs with prescribed Bernoulli
marginals.  Such reservoirs cannot be mutually independent (except in degenerate cases): for one
point `a`, the events `a ∈ R i` and `a ∈ R j` are disjoint, whereas independence would give their
intersection probability `q i * q j`.  The paper-faithful interpretation is therefore a
*categorical product law*: independently for every ground element, choose either one reservoir
label or the unused label.  Reservoirs belonging to independently sampled vertex and colour
splits are genuinely independent.

This file constructs that finite law explicitly.  `categoricalSplit_atom` is its complete joint
mass function, `categoricalSplit_cylinder` is coordinate independence, and
`categoricalSplit_projected_qRandom` proves that every projected reservoir has the exact
product-Bernoulli law used by `NearEmbeddingConclusion` and
`SmallTreeEmbeddingConclusion`.  No probabilistic assumption is an input.
-/

open scoped BigOperators
open Classical

set_option maxHeartbeats 800000

namespace Ringel

section Categorical

variable {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]

/-- Weight of one categorical choice: `none` means that the element is unused. -/
noncomputable def reservoirChoiceWeight (q : ι → ℝ) : Option ι → ℝ
  | none => 1 - ∑ i, q i
  | some i => q i

/-- The finite sample space for independent per-element categorical choices. -/
abbrev ReservoirSample (α ι : Type*) := α → Option ι

/-- The reservoir carrying label `i`.  Distinct labels are disjoint by construction. -/
def projectedReservoir (i : ι) (ω : ReservoirSample α ι) : Set α :=
  {a | ω a = some i}

/-- Explicit mass of an outcome: the product of its per-element categorical weights. -/
noncomputable def categoricalSplitMass (q : ι → ℝ) (ω : ReservoirSample α ι) : ℝ :=
  ∏ a, reservoirChoiceWeight q (ω a)

omit [DecidableEq ι] in
lemma reservoirChoiceWeight_nonneg (q : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hsum : ∑ i, q i ≤ 1) :
    ∀ x, 0 ≤ reservoirChoiceWeight q x := by
  rintro (_ | i)
  · exact sub_nonneg.mpr hsum
  · exact hq i

omit [DecidableEq ι] in
lemma sum_reservoirChoiceWeight (q : ι → ℝ) :
    ∑ x : Option ι, reservoirChoiceWeight q x = 1 := by
  rw [Fintype.sum_option]
  simp only [reservoirChoiceWeight]
  ring

omit [DecidableEq ι] in
lemma sum_categoricalSplitMass (q : ι → ℝ) :
    ∑ ω : ReservoirSample α ι, categoricalSplitMass q ω = 1 := by
  classical
  unfold categoricalSplitMass
  calc
    ∑ ω : α → Option ι, ∏ a, reservoirChoiceWeight q (ω a) =
        ∑ ω ∈ Fintype.piFinset (fun _ : α => (Finset.univ : Finset (Option ι))),
          ∏ a, reservoirChoiceWeight q (ω a) := by simp
    _ = ∏ _a : α, ∑ x : Option ι, reservoirChoiceWeight q x :=
      Finset.sum_prod_piFinset _ _
    _ = 1 := by
      rw [show (∑ x : Option ι, reservoirChoiceWeight q x) = 1 from
        sum_reservoirChoiceWeight q]
      simp

/-- The concrete finite probability law underlying a disjoint reservoir split. -/
noncomputable def categoricalSplitLaw (q : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hsum : ∑ i, q i ≤ 1) :
    FiniteProbabilityLaw (ReservoirSample α ι) where
  mass := categoricalSplitMass q
  mass_nonneg := fun ω => Finset.prod_nonneg fun i _ =>
    reservoirChoiceWeight_nonneg q hq hsum (ω i)
  sum_mass := sum_categoricalSplitMass q

/-- The complete joint atom law.  This is the strongest exact finite statement of the split:
every assignment of all elements to labels has its product mass. -/
lemma categoricalSplit_atom (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i)
    (hsum : ∑ i, q i ≤ 1) (f : ReservoirSample α ι) :
    (categoricalSplitLaw q hq hsum).prob {f} =
      ∏ a, reservoirChoiceWeight q (f a) := by
  rw [FiniteProbabilityLaw.prob]
  simp only [Set.mem_singleton_iff, categoricalSplitLaw, categoricalSplitMass]
  have hf : Finset.univ.filter (fun x : ReservoirSample α ι => x = f) = {f} := by
    ext b
    simp
  rw [hf]
  simp

/-- Product law on every finite cylinder.  Choices at distinct ground elements are mutually
independent, including the unused outcome. -/
lemma categoricalSplit_cylinder (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i)
    (hsum : ∑ i, q i ≤ 1) (s : Finset α) (f : α → Option ι) :
    (categoricalSplitLaw q hq hsum).prob {ω | ∀ a ∈ s, ω a = f a} =
      ∏ a ∈ s, reservoirChoiceWeight q (f a) := by
  classical
  rw [FiniteProbabilityLaw.prob]
  simp only [categoricalSplitLaw, categoricalSplitMass, Set.mem_setOf_eq]
  let t : α → Finset (Option ι) := fun a =>
    if a ∈ s then {f a} else Finset.univ
  have hfilter : Finset.univ.filter (fun ω : ReservoirSample α ι =>
      ∀ a ∈ s, ω a = f a) = Fintype.piFinset t := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, t]
    constructor
    · intro h a
      by_cases ha : a ∈ s
      · simp [ha, h a ha]
      · simp [ha]
    · intro h a ha
      simpa [ha] using h a
  rw [hfilter]
  rw [show (∑ ω ∈ Fintype.piFinset t, ∏ a, reservoirChoiceWeight q (ω a)) =
      ∏ a, ∑ x ∈ t a, reservoirChoiceWeight q x by
        exact (Finset.prod_univ_sum t (fun _a x => reservoirChoiceWeight q x)).symm]
  simp only [t]
  have hu : (∑ x : Option ι, reservoirChoiceWeight q x) = 1 :=
    sum_reservoirChoiceWeight q
  calc
    ∏ a, ∑ x ∈ if a ∈ s then {f a} else Finset.univ, reservoirChoiceWeight q x =
        ∏ a, if a ∈ s then reservoirChoiceWeight q (f a) else 1 := by
      congr 1
      funext a
      by_cases ha : a ∈ s <;> simp [ha, hu]
    _ = _ := by rw [Finset.prod_ite]; simp

/-- Product law for arbitrary coordinatewise allowed-choice sets. -/
lemma categoricalSplit_restriction (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i)
    (hsum : ∑ i, q i ≤ 1) (t : α → Finset (Option ι)) :
    (categoricalSplitLaw q hq hsum).prob {ω | ∀ a, ω a ∈ t a} =
      ∏ a, ∑ x ∈ t a, reservoirChoiceWeight q x := by
  classical
  rw [FiniteProbabilityLaw.prob]
  simp only [categoricalSplitLaw, categoricalSplitMass, Set.mem_setOf_eq]
  have hfilter : Finset.univ.filter (fun ω : ReservoirSample α ι =>
      ∀ a, ω a ∈ t a) = Fintype.piFinset t := by
    ext ω
    simp [Fintype.mem_piFinset]
  rw [hfilter]
  exact (Finset.prod_univ_sum t (fun _a x => reservoirChoiceWeight q x)).symm

/-- Each labelled projection has exactly the required product-Bernoulli law. -/
lemma categoricalSplit_projected_qRandom (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i)
    (hsum : ∑ i, q i ≤ 1) (i : ι) :
    IsQRandomSet (categoricalSplitLaw (α := α) q hq hsum) (q i)
      (projectedReservoir (α := α) i) := by
  classical
  intro A
  let t : α → Finset (Option ι) := fun a =>
    if a ∈ A then {some i} else Finset.univ.erase (some i)
  have hevent : {ω | projectedReservoir i ω = A} = {ω | ∀ a, ω a ∈ t a} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.ext_iff, projectedReservoir, t]
    constructor
    · intro h a
      by_cases ha : a ∈ A
      · simp [ha, (h a).mpr ha]
      · simp [ha]
        intro hw
        exact ha ((h a).mp hw)
    · intro h a
      specialize h a
      by_cases ha : a ∈ A <;> simp [ha] at h ⊢
      · exact h
      · exact h
  rw [hevent, categoricalSplit_restriction]
  calc
    ∏ a, ∑ x ∈ t a, reservoirChoiceWeight q x =
        ∏ a, if a ∈ A then q i else (1 - q i) := by
      congr 1
      funext a
      by_cases ha : a ∈ A
      · simp [t, ha, reservoirChoiceWeight]
      · simp only [t, ha, ↓reduceIte]
        have hs := Finset.sum_erase_add (Finset.univ : Finset (Option ι))
          (fun x => reservoirChoiceWeight q x) (Finset.mem_univ (some i))
        rw [sum_reservoirChoiceWeight] at hs
        simpa only [reservoirChoiceWeight] using (eq_sub_of_add_eq hs)
    _ = q i ^ A.ncard * (1 - q i) ^ ((Set.univ : Set α) \ A).ncard := by
      rw [Finset.prod_ite]
      congr 1
      · simp [Set.ncard_eq_toFinset_card']
      · rw [Finset.prod_const]
        congr 1
        have hset : (Finset.univ.filter (fun x : α => x ∉ A)) =
            ((Set.univ : Set α) \ A).toFinset := by
          ext a
          simp
        rw [Set.ncard_eq_toFinset_card']
        exact congrArg Finset.card hset

omit [Fintype α] [Fintype ι] [DecidableEq ι] in
/-- Distinct projected reservoirs are pointwise disjoint, not independent. -/
lemma categoricalSplit_disjoint (i j : ι) (hij : i ≠ j)
    (ω : ReservoirSample α ι) :
    Disjoint (projectedReservoir i ω) (projectedReservoir j ω) := by
  rw [Set.disjoint_left]
  intro a hai haj
  exact hij (Option.some.inj (hai.symm.trans haj))

/-- The union of all labelled reservoirs is Bernoulli with parameter `∑ i, q i`.
This is the exact law used when §6 says to partition a random dependent reservoir. -/
lemma categoricalSplit_union_qRandom (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i)
    (hsum : ∑ i, q i ≤ 1) :
    IsQRandomSet (categoricalSplitLaw (α := α) q hq hsum) (∑ i, q i)
      (fun ω => ⋃ i, projectedReservoir (α := α) i ω) := by
  classical
  intro A
  let t : α → Finset (Option ι) := fun a =>
    if a ∈ A then Finset.univ.erase none else {none}
  have hevent : {ω | (⋃ i, projectedReservoir i ω) = A} =
      {ω | ∀ a, ω a ∈ t a} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.ext_iff, Set.mem_iUnion, projectedReservoir, t]
    constructor
    · intro h a
      by_cases ha : a ∈ A
      · simp [ha]
        intro hn
        have : ∃ i, ω a = some i := (h a).mpr ha
        rcases this with ⟨i, hi⟩
        simp [hi] at hn
      · simp [ha]
        cases hwa : ω a with
        | none => rfl
        | some i =>
            exfalso
            exact ha ((h a).mp ⟨i, hwa⟩)
    · intro h a
      specialize h a
      by_cases ha : a ∈ A
      · simp [ha] at h
        cases hwa : ω a with
        | none => simp [hwa] at h
        | some i => exact ⟨fun _ => ha, fun _ => ⟨i, rfl⟩⟩
      · simp [ha] at h
        exact ⟨fun hex => by rcases hex with ⟨i, hi⟩; simp [h] at hi,
          fun hmem => (ha hmem).elim⟩
  rw [hevent, categoricalSplit_restriction]
  let r : ℝ := ∑ i, q i
  have hnone : reservoirChoiceWeight q none = 1 - r := rfl
  have hnon : ∑ x ∈ (Finset.univ.erase none : Finset (Option ι)),
      reservoirChoiceWeight q x = r := by
    have hs := Finset.sum_erase_add (Finset.univ : Finset (Option ι))
      (fun x => reservoirChoiceWeight q x) (Finset.mem_univ none)
    rw [sum_reservoirChoiceWeight] at hs
    simp only [reservoirChoiceWeight, r] at hs ⊢
    linarith
  calc
    ∏ a, ∑ x ∈ t a, reservoirChoiceWeight q x =
        ∏ a, if a ∈ A then r else (1 - r) := by
      congr 1
      funext a
      by_cases ha : a ∈ A <;> simp [t, ha, hnon, hnone]
    _ = r ^ A.ncard * (1 - r) ^ ((Set.univ : Set α) \ A).ncard := by
      rw [Finset.prod_ite]
      congr 1
      · simp [Set.ncard_eq_toFinset_card']
      · rw [Finset.prod_const]
        congr 1
        have hset : (Finset.univ.filter (fun x : α => x ∉ A)) =
            ((Set.univ : Set α) \ A).toFinset := by ext a; simp
        rw [Set.ncard_eq_toFinset_card']
        exact congrArg Finset.card hset
    _ = _ := rfl

/-- Exact allocation atom inside a fixed union atom.  This is the division-free form of the
conditional law: given the union, retained elements receive labels independently with weights
proportional to `q`.  It remains meaningful when the conditioning atom has probability zero. -/
lemma categoricalSplit_conditional_partition (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i)
    (hsum : ∑ i, q i ≤ 1) (B : Set α) (f : α → ι) :
    (categoricalSplitLaw q hq hsum).prob
        {ω | (⋃ i, projectedReservoir i ω) = B ∧ ∀ a ∈ B, ω a = some (f a)} =
      (∏ a with a ∈ B, q (f a)) *
        (1 - ∑ i, q i) ^ ((Set.univ : Set α) \ B).ncard := by
  classical
  let t : α → Finset (Option ι) := fun a =>
    if a ∈ B then {some (f a)} else {none}
  have hevent :
      {ω | (⋃ i, projectedReservoir i ω) = B ∧ ∀ a ∈ B, ω a = some (f a)} =
      {ω | ∀ a, ω a ∈ t a} := by
    ext ω
    simp only [Set.mem_setOf_eq, t]
    constructor
    · rintro ⟨hunion, hf⟩ a
      by_cases ha : a ∈ B
      · simp [ha, hf a ha]
      · simp [ha]
        cases hwa : ω a with
        | none => rfl
        | some i =>
            have : a ∈ ⋃ i, projectedReservoir i ω := by
              simp [projectedReservoir, hwa]
            exact (ha (hunion ▸ this)).elim
    · intro h
      constructor
      · ext a
        specialize h a
        by_cases ha : a ∈ B
        · simp [ha] at h
          simp [projectedReservoir, h, ha]
        · simp [ha] at h
          simp [projectedReservoir, h, ha]
      · intro a ha
        simpa [t, ha] using h a
  rw [hevent, categoricalSplit_restriction]
  calc
    ∏ a, ∑ x ∈ t a, reservoirChoiceWeight q x =
        ∏ a, if a ∈ B then q (f a) else (1 - ∑ i, q i) := by
      congr 1
      funext a
      by_cases ha : a ∈ B <;> simp [t, ha, reservoirChoiceWeight]
    _ = _ := by
      rw [Finset.prod_ite, Finset.prod_const]
      congr 1
      have hset : (Finset.univ.filter (fun x : α => x ∉ B)) =
          ((Set.univ : Set α) \ B).toFinset := by ext a; simp
      rw [Set.ncard_eq_toFinset_card']
      exact congrArg (fun n => (1 - ∑ i, q i) ^ n) (congrArg Finset.card hset)

end Categorical

namespace FiniteProbabilityLaw

section Product

variable {Ω Ψ : Type*} [Fintype Ω] [Fintype Ψ]

/-- Product of two transparent finite laws. -/
noncomputable def product (P : FiniteProbabilityLaw Ω) (Q : FiniteProbabilityLaw Ψ) :
    FiniteProbabilityLaw (Ω × Ψ) where
  mass z := P.mass z.1 * Q.mass z.2
  mass_nonneg z := mul_nonneg (P.mass_nonneg z.1) (Q.mass_nonneg z.2)
  sum_mass := by
    rw [Fintype.sum_prod_type]
    calc
      ∑ x, ∑ y, P.mass x * Q.mass y = ∑ x, P.mass x * (∑ y, Q.mass y) := by
        congr 1
        funext x
        rw [Finset.mul_sum]
      _ = 1 := by rw [Q.sum_mass]; simpa using P.sum_mass

lemma product_prob_rectangle (P : FiniteProbabilityLaw Ω) (Q : FiniteProbabilityLaw Ψ)
    (A : Set Ω) (B : Set Ψ) :
    (P.product Q).prob {z | z.1 ∈ A ∧ z.2 ∈ B} = P.prob A * Q.prob B := by
  rw [prob, prob, prob]
  simp only [Set.mem_setOf_eq, product]
  change (∑ z : Ω × Ψ with z.1 ∈ A ∧ z.2 ∈ B, P.mass z.1 * Q.mass z.2) = _
  have hf : Finset.univ.filter (fun z : Ω × Ψ => z.1 ∈ A ∧ z.2 ∈ B) =
      (Finset.univ.filter (fun x : Ω => x ∈ A)).product
        (Finset.univ.filter (fun y : Ψ => y ∈ B)) := by
    ext z
    simp
  rw [hf]
  calc
    ∑ z ∈ (Finset.univ.filter (fun x : Ω => x ∈ A)).product
        (Finset.univ.filter (fun y : Ψ => y ∈ B)), P.mass z.1 * Q.mass z.2 =
      ∑ x with x ∈ A, ∑ y with y ∈ B, P.mass x * Q.mass y := by
        exact Finset.sum_product _ _ _
    _ = ∑ x with x ∈ A, P.mass x * (∑ y with y ∈ B, Q.mass y) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mul_sum]
    _ = _ := by rw [Finset.sum_mul]

lemma product_prob_fst (P : FiniteProbabilityLaw Ω) (Q : FiniteProbabilityLaw Ψ)
    (A : Set Ω) : (P.product Q).prob {z | z.1 ∈ A} = P.prob A := by
  have h := P.product_prob_rectangle Q A Set.univ
  simpa using h

lemma product_prob_snd (P : FiniteProbabilityLaw Ω) (Q : FiniteProbabilityLaw Ψ)
    (B : Set Ψ) : (P.product Q).prob {z | z.2 ∈ B} = Q.prob B := by
  have h := P.product_prob_rectangle Q Set.univ B
  simpa using h

lemma product_fst_snd_independent (P : FiniteProbabilityLaw Ω)
    (Q : FiniteProbabilityLaw Ψ) :
    (P.product Q).Independent Prod.fst Prod.snd := by
  intro x y
  have hxy := P.product_prob_rectangle Q ({x} : Set Ω) ({y} : Set Ψ)
  have hx := P.product_prob_fst Q ({x} : Set Ω)
  have hy := P.product_prob_snd Q ({y} : Set Ψ)
  simpa using hxy.trans (congrArg₂ (· * ·) hx.symm hy.symm)

lemma product_map_independent {X Y : Type*} [Fintype X] [Fintype Y]
    (P : FiniteProbabilityLaw Ω) (Q : FiniteProbabilityLaw Ψ)
    (F : Ω → X) (G : Ψ → Y) :
    (P.product Q).Independent (fun z => F z.1) (fun z => G z.2) := by
  intro x y
  let A : Set Ω := {a | F a = x}
  let B : Set Ψ := {b | G b = y}
  have hxy := P.product_prob_rectangle Q A B
  have hx := P.product_prob_fst Q A
  have hy := P.product_prob_snd Q B
  simpa [A, B] using hxy.trans (congrArg₂ (· * ·) hx.symm hy.symm)

end Product

end FiniteProbabilityLaw

section JointReservoirs

variable {α β ι κ : Type*} [Fintype α] [Fintype β]
  [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- One concrete joint law for the vertex and colour splits in §6.  Each side is internally a
categorical (hence disjoint) split, while the complete vertex split and complete colour split are
independent. -/
noncomputable def jointReservoirLaw (qV : ι → ℝ) (qC : κ → ℝ)
    (hqV : ∀ i, 0 ≤ qV i) (hsumV : ∑ i, qV i ≤ 1)
    (hqC : ∀ i, 0 ≤ qC i) (hsumC : ∑ i, qC i ≤ 1) :
    FiniteProbabilityLaw (ReservoirSample α ι × ReservoirSample β κ) :=
  (categoricalSplitLaw (α := α) qV hqV hsumV).product
    (categoricalSplitLaw (α := β) qC hqC hsumC)

lemma jointReservoir_vertex_colour_independent
    (qV : ι → ℝ) (qC : κ → ℝ)
    (hqV : ∀ i, 0 ≤ qV i) (hsumV : ∑ i, qV i ≤ 1)
    (hqC : ∀ i, 0 ≤ qC i) (hsumC : ∑ i, qC i ≤ 1) (i : ι) (j : κ) :
    (jointReservoirLaw (α := α) (β := β) qV qC hqV hsumV hqC hsumC).Independent
      (fun z => projectedReservoir (α := α) i z.1)
      (fun z => projectedReservoir (α := β) j z.2) := by
  exact FiniteProbabilityLaw.product_map_independent _ _ _ _

end JointReservoirs

end Ringel
