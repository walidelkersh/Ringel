import Ringel.NearEmbeddingSmallTree

/-!
# Finite concentration for q-random sets

This module isolates the bounded concentration input used in MPS §6.  The existing
`IsQRandomSet` predicate specifies the probability of every atom of the random set; it is the
full product-Bernoulli law, not merely a statement about one-point marginals.  We first record
its exact finite marginal laws and expectation, then prove the advertised multiplicative
Chernoff lower tail.
-/

open scoped BigOperators
open Classical

namespace Ringel

namespace FiniteProbabilityLaw

variable {Ω : Type*} [Fintype Ω]

/-- Expectation of a real-valued random variable under a transparent finite law. -/
noncomputable def expect (P : FiniteProbabilityLaw Ω) (Y : Ω → ℝ) : ℝ :=
  ∑ ω, P.mass ω * Y ω

end FiniteProbabilityLaw

variable {Ω α : Type*} [Fintype Ω] [Fintype α]

/-- The exact marginal product law on an arbitrary finite subground set.  In particular, this
records mutual independence of all membership bits, rather than only their one-point marginals. -/
theorem qRandomSet_intersection_atom
    (P : FiniteProbabilityLaw Ω) (X : Ω → Set α) (q : ℝ)
    (hX : IsQRandomSet P q X)
    (A B : Set α) :
    P.prob {ω | A ∩ X ω = B} =
      if B ⊆ A then q ^ B.ncard * (1 - q) ^ (A \ B).ncard else 0 := by
  by_cases hB : B ⊆ A <;> simp_all +decide [FiniteProbabilityLaw.prob]
  · have hIsQRandomSet : ∑ ω ∈ Finset.univ.filter (fun ω => A ∩ X ω = B), P.mass ω =
        ∑ C ∈ Finset.powerset (Set.toFinset (Set.univ \ A)),
          q ^ (B.ncard + C.card) * (1-q)^((Set.univ \ B).ncard-C.card) := by
      have hs : ∑ ω ∈ Finset.univ.filter (fun ω => A ∩ X ω = B), P.mass ω =
          ∑ C ∈ Finset.powerset (Set.toFinset (Set.univ \ A)),
            ∑ ω ∈ Finset.univ.filter (fun ω => X ω = B ∪ (C : Set α)), P.mass ω := by
        rw [← Finset.sum_biUnion]
        · refine Finset.sum_subset ?_ ?_ <;> simp +contextual [Finset.subset_iff, Set.ext_iff]
          · intro ω hω
            use (X ω \ A).toFinset
            simp_all +decide [Set.ext_iff]
            grind
          · grind
        · intros C hC D hD hCD
          simp_all +decide [Finset.disjoint_left]
          contrapose! hCD
          simp_all +decide [Finset.ext_iff, Set.ext_iff]
          intro x
          replace hCD := hCD.2 x
          simp_all +decide [Set.subset_def]
          grind
      convert hs using 2
      convert (hX (B ∪ (↑(show Finset α from ‹Finset α›) : Set α))).symm using 1
      simp +decide [Set.ncard_eq_toFinset_card', Finset.card_sdiff, *]
      rw [Finset.card_union_of_disjoint]
      · simp +decide [Nat.sub_sub, Set.toFinset_card]
      · simp_all +decide [Finset.disjoint_left, Set.subset_def]
        grind
    have hf : ∑ C ∈ Finset.powerset (Set.toFinset (Set.univ \ A)),
          q ^ (B.ncard+C.card) * (1-q)^((Set.univ\B).ncard-C.card) =
        q^B.ncard * (1-q)^((Set.univ\B).ncard-(Set.univ\A).ncard) *
          ∑ C ∈ Finset.powerset (Set.toFinset (Set.univ\A)),
            q^C.card * (1-q)^((Set.univ\A).ncard-C.card) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun C hC => ?_
      rw [show (Set.univ\B).ncard=(Set.univ\A).ncard+(A\B).ncard by
        rw [← Set.ncard_union_eq]
        · congr with x
          by_cases hx:x∈A <;> by_cases hx':x∈B <;> simp +decide [hx,hx']
          exact hx (hB hx')
        · exact Set.disjoint_left.mpr fun x hx₁ hx₂ => hx₁.2 hx₂.1]
      ring_nf
      simp +decide [mul_assoc, ← pow_add,
        Nat.sub_add_comm (show C.card ≤ (Set.univ\A).ncard by
          simpa [← Set.ncard_coe_finset] using Finset.card_le_card (Finset.mem_powerset.mp hC))]
      exact Or.inl (by rw [add_comm])
    have hb : ∑ C ∈ Finset.powerset (Set.toFinset (Set.univ\A)), q^C.card*(1-q)^((Set.univ\A).ncard-C.card) =
        (q+(1-q))^(Set.univ\A).ncard := by
      simpa [Set.ncard_eq_toFinset_card'] using
        (Finset.sum_pow_mul_eq_add_pow q (1-q) (Set.toFinset (Set.univ\A)))
    rw [hIsQRandomSet, hf, hb]
    simp +decide [Set.ncard_eq_toFinset_card', Finset.card_sdiff, *]
    rw [show B.toFinset ∩ A.toFinset = B.toFinset from Finset.inter_eq_left.mpr <| by
      simpa [Finset.subset_iff, Set.subset_def] using hB]
    simp +decide [Nat.sub_sub, add_comm]
    grind
  · simp_all +decide [Set.subset_def, Finset.sum_eq_zero_iff_of_nonneg, P.mass_nonneg]
    grind


/-- Every individual membership bit has the advertised Bernoulli marginal. -/
theorem qRandomSet_mem_prob
    (P : FiniteProbabilityLaw Ω) (X : Ω → Set α) (q : ℝ)
    (hX : IsQRandomSet P q X) (a : α) :
    P.prob {ω | a ∈ X ω} = q := by
  have h := qRandomSet_intersection_atom P X q hX ({a} : Set α) ({a} : Set α)
  simpa [Set.ext_iff] using h

/-- Exact expectation of the number of selected elements in a fixed finite set. -/
theorem qRandomSet_intersection_expect
    (P : FiniteProbabilityLaw Ω) (X : Ω → Set α) (A : Set α) (q : ℝ)
    (hX : IsQRandomSet P q X) :
    P.expect (fun ω => ((A ∩ X ω).ncard : ℝ)) = q * A.ncard := by
  rw [FiniteProbabilityLaw.expect]
  simp_rw [Set.ncard_eq_toFinset_card', Finset.card_eq_sum_ones]
  push_cast
  simp_rw [Set.toFinset_inter, ← Finset.filter_mem_eq_inter]
  simp_rw [Finset.mul_sum]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  simp only [mul_one]
  simp_rw [← Finset.sum_filter]
  simp only [Set.mem_toFinset]
  have hm (i : α) : (∑ a with i ∈ X a, P.mass a) = q := by
    simpa [FiniteProbabilityLaw.prob] using qRandomSet_mem_prob P X q hX i
  simp_rw [hm]

/-
The finite multiplicative Chernoff lower-tail inequality, stated directly for the
product-Bernoulli weights of all subsets of a finite set.
-/
theorem powerset_chernoff_lower_tail {α : Type*} [Fintype α]
    (A : Set α) (q δ : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    (∑ B ∈ A.toFinset.powerset with
        B.card < ⌊(1 - δ) * q * A.ncard⌋₊,
      q ^ B.card * (1 - q) ^ (A.ncard - B.card)) ≤
      Real.exp (-(δ ^ 2 * q * A.ncard) / 2) := by
  by_cases hq : q = 0;
  · aesop;
  · by_cases hq : q = 1;
    · by_cases h : A.ncard = 0 <;> simp_all +decide [ Nat.floor_eq_zero ];
      rw [ Finset.sum_eq_zero ] <;> norm_num;
      · positivity;
      · exact fun x hx hx' => Nat.sub_ne_zero_of_lt ( lt_of_lt_of_le hx' ( Nat.floor_le_of_le ( mul_le_of_le_one_left ( Nat.cast_nonneg _ ) ( sub_le_self _ hδ0 ) ) ) );
    · -- For any $t > 0$, we have
      -- $\mathbb{P}(\sum_{i=1}^m X_i < (1-\delta)qm) \leq \exp(qm(e^{-t} - 1)) \cdot \exp(t(1-\delta)qm)$.
      have h_exp : ∀ t > 0, (∑ B ∈ Finset.powerset (Set.toFinset A), if B.card < Nat.floor ((1 - δ) * q * (Set.ncard A)) then q ^ B.card * (1 - q) ^ ((Set.ncard A) - B.card) else 0) ≤ Real.exp (q * (Set.ncard A) * (Real.exp (-t) - 1)) * Real.exp (t * (1 - δ) * q * (Set.ncard A)) := by
        intro t ht
        have h_exp : (∑ B ∈ Finset.powerset (Set.toFinset A), q ^ B.card * (1 - q) ^ ((Set.ncard A) - B.card) * Real.exp (-t * B.card)) ≤ Real.exp (q * (Set.ncard A) * (Real.exp (-t) - 1)) := by
          have h_exp : (∑ B ∈ Finset.powerset (Set.toFinset A), q ^ B.card * (1 - q) ^ ((Set.ncard A) - B.card) * Real.exp (-t * B.card)) = (q * Real.exp (-t) + (1 - q)) ^ (Set.ncard A) := by
            rw [ add_pow ];
            rw [ Finset.sum_powerset ];
            simp +decide [ mul_pow, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul, Set.ncard_eq_toFinset_card' ];
            refine' Finset.sum_congr rfl fun x hx => _;
            rw [ Finset.sum_congr rfl fun y hy => by rw [ Finset.mem_powersetCard.mp hy |>.2 ] ] ; simp +decide [ ← mul_assoc, ← Real.exp_nat_mul ] ; ring;
          rw [ h_exp, ← Real.rpow_natCast, Real.rpow_def_of_pos ] <;> norm_num;
          · nlinarith [ Real.log_le_sub_one_of_pos ( show 0 < q * Real.exp ( -t ) + ( 1 - q ) by nlinarith [ Real.exp_pos ( -t ), mul_self_pos.2 ‹q ≠ 0›, mul_self_pos.2 ( sub_ne_zero.2 hq ) ] ), show ( 0 : ℝ ) ≤ A.ncard by positivity ];
          · exact add_pos_of_nonneg_of_pos ( mul_nonneg hq0 ( Real.exp_nonneg _ ) ) ( sub_pos.mpr ( lt_of_le_of_ne hq1 hq ) );
        refine' le_trans _ ( mul_le_mul_of_nonneg_right h_exp <| Real.exp_nonneg _ );
        rw [ Finset.sum_mul _ _ _ ];
        gcongr;
        split_ifs <;> simp_all +decide [ mul_assoc, ← Real.exp_add ];
        · exact mul_le_mul_of_nonneg_left ( le_mul_of_one_le_right ( pow_nonneg ( sub_nonneg.2 hq1 ) _ ) ( Real.one_le_exp ( by nlinarith [ show ( ↑‹Finset α›.card : ℝ ) + 1 ≤ ⌊ ( 1 - δ ) * ( q * ↑A.ncard ) ⌋₊ by exact_mod_cast ‹_›, Nat.floor_le ( show 0 ≤ ( 1 - δ ) * ( q * ↑A.ncard ) by exact mul_nonneg ( sub_nonneg.2 hδ1 ) ( mul_nonneg hq0 ( Nat.cast_nonneg _ ) ) ) ] ) ) ) ( pow_nonneg hq0 _ );
        · exact mul_nonneg ( pow_nonneg hq0 _ ) ( mul_nonneg ( pow_nonneg ( sub_nonneg.2 hq1 ) _ ) ( Real.exp_nonneg _ ) );
      -- Choose $t = \delta$.
      have h_choose_t : (∑ B ∈ Finset.powerset (Set.toFinset A), if B.card < Nat.floor ((1 - δ) * q * (Set.ncard A)) then q ^ B.card * (1 - q) ^ ((Set.ncard A) - B.card) else 0) ≤ Real.exp (q * (Set.ncard A) * (Real.exp (-δ) - 1)) * Real.exp (δ * (1 - δ) * q * (Set.ncard A)) := by
        by_cases hδ : δ = 0;
        · simp_all +decide [ Finset.sum_ite ];
          refine' le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => mul_nonneg ( pow_nonneg hq0 _ ) ( pow_nonneg ( sub_nonneg.2 hq1 ) _ ) ) _;
          have h_sum : ∑ B ∈ Finset.powerset (Set.toFinset A), q ^ B.card * (1 - q) ^ ((Set.ncard A) - B.card) = (q + (1 - q)) ^ (Set.ncard A) := by
            rw [ add_pow ];
            rw [ Finset.sum_powerset ];
            simp +decide [ Finset.sum_powersetCard, Set.ncard_eq_toFinset_card' ];
            exact Finset.sum_congr rfl fun i hi => by rw [ Finset.sum_congr rfl fun x hx => by rw [ Finset.mem_powersetCard.mp hx |>.2 ] ] ; simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.card_univ ] ;
          aesop;
        · exact h_exp δ ( lt_of_le_of_ne hδ0 ( Ne.symm hδ ) );
      -- Simplify the exponent.
      have h_simplify_exp : Real.exp (q * (Set.ncard A) * (Real.exp (-δ) - 1)) * Real.exp (δ * (1 - δ) * q * (Set.ncard A)) ≤ Real.exp (-(δ ^ 2 * q * (Set.ncard A)) / 2) := by
        rw [ ← Real.exp_add ];
        -- We'll use the fact that $e^{-\delta} \leq 1 - \delta + \frac{\delta^2}{2}$ for $\delta \in [0, 1]$.
        have h_exp_bound : Real.exp (-δ) ≤ 1 - δ + δ^2 / 2 := by
          -- We'll use the fact that $e^{-\delta} \leq 1 - \delta + \frac{\delta^2}{2}$ for $\delta \in [0, 1]$. This follows from the Taylor series expansion of $e^{-\delta}$.
          have h_exp_bound : ∀ δ ∈ Set.Icc (0 : ℝ) 1, Real.exp (-δ) ≤ 1 - δ + δ^2 / 2 := by
            intro δ hδ
            have h_taylor : ∀ x ∈ Set.Icc (0 : ℝ) 1, deriv (fun x => Real.exp (-x) - (1 - x + x^2 / 2)) x ≤ 0 := by
              intro x hx
              have he : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
                convert (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg using 1 <;> ring
              have hi : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
              have hp : HasDerivAt (fun y : ℝ => 1 - y + y ^ 2 / 2) (-1 + x) x := by
                convert ((hasDerivAt_const x 1).sub hi).add ((hi.pow 2).div_const 2) using 1 <;> ring
              have hd : deriv (fun y : ℝ => Real.exp (-y) - (1 - y + y ^ 2 / 2)) x =
                  -Real.exp (-x) - (-1 + x) := by
                exact (he.sub hp).deriv
              rw [hd]
              nlinarith [Real.add_one_le_exp (-x)]
            by_contra h_contra;
            have := exists_deriv_eq_slope ( f := fun x => Real.exp ( -x ) - ( 1 - x + x ^ 2 / 2 ) ) ( show δ > 0 from hδ.1.lt_of_ne ( by rintro rfl; norm_num at h_contra ) ) ; norm_num at *;
            exact absurd ( this ( Continuous.continuousOn <| by exact Continuous.sub ( Real.continuous_exp.comp <| ContinuousNeg.continuous_neg ) <| by continuity ) ( Differentiable.differentiableOn <| by exact Differentiable.sub ( Differentiable.exp <| differentiable_id.neg ) <| by exact Differentiable.add ( differentiable_id.const_sub _ ) <| by exact Differentiable.div_const ( differentiable_pow 2 ) _ ) ) ( by rintro ⟨ c, ⟨ hc0, hcδ ⟩, hcd ⟩ ; rw [ eq_div_iff ] at hcd <;> nlinarith [ h_taylor c ( by linarith ) ( by linarith ) ] );
          exact h_exp_bound δ ⟨ hδ0, hδ1 ⟩;
        exact Real.exp_le_exp.mpr ( by nlinarith [ show 0 ≤ q * A.ncard by positivity ] );
      simpa [ Finset.sum_ite ] using h_choose_t.trans h_simplify_exp

/-- The law of every cardinality event is the corresponding sum of product-Bernoulli weights. -/
theorem qRandomSet_intersection_card_lt_prob
    (P : FiniteProbabilityLaw Ω) (X : Ω → Set α) (A : Set α) (q : ℝ)
    (hX : IsQRandomSet P q X) (r : ℕ) :
    P.prob {ω | (A ∩ X ω).ncard < r} =
      ∑ B ∈ A.toFinset.powerset with B.card < r,
        q ^ B.card * (1 - q) ^ (A.ncard - B.card) := by
  rw [FiniteProbabilityLaw.prob]
  have hpart :
      (∑ ω with (A ∩ X ω).ncard < r, P.mass ω) =
        ∑ B ∈ A.toFinset.powerset with B.card < r,
          ∑ ω with A ∩ X ω = (B : Set α), P.mass ω := by
    rw [← Finset.sum_biUnion]
    · refine Finset.sum_congr ?_ fun _ _ => rfl
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
        Finset.mem_powerset]
      constructor
      · intro hr
        refine ⟨(A ∩ X ω).toFinset, ?_, ?_⟩
        · exact ⟨by simp, by simpa [Set.ncard_eq_toFinset_card'] using hr⟩
        · simp
      · rintro ⟨B, ⟨hBA, hBr⟩, hEq⟩
        simpa [hEq, Set.ncard_eq_toFinset_card'] using hBr
    · intro B hB C hC hne
      simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and]
      intro ω hωB hωC
      apply hne
      ext x
      have hs := Set.ext_iff.mp (hωB.symm.trans hωC) x
      simpa using hs
  simp only [Set.mem_setOf_eq]
  change (∑ ω with (A ∩ X ω).ncard < r, P.mass ω) = _
  rw [hpart]
  refine Finset.sum_congr rfl fun B hB => ?_
  simp only [Finset.mem_filter, Finset.mem_powerset] at hB
  have hatom := qRandomSet_intersection_atom P X q hX A (B : Set α)
  rw [FiniteProbabilityLaw.prob] at hatom
  simp only [Set.mem_setOf_eq] at hatom
  rw [hatom, if_pos]
  · have hinter : B ∩ A.toFinset = B := Finset.inter_eq_left.mpr hB.1
    simp [Set.ncard_eq_toFinset_card', Finset.card_sdiff, hinter]
  · simpa using hB.1

/-- Multiplicative lower-tail bound for the cardinality of a product-Bernoulli subset, in the
finite probability language used by the near-embedding development. -/
theorem qRandomSet_lower_tail
    (P : FiniteProbabilityLaw Ω) (X : Ω → Set α) (A : Set α)
    (q δ : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hX : IsQRandomSet P q X) :
    1 - Real.exp (-(δ ^ 2 * q * A.ncard) / 2) ≤
      P.prob {ω | ⌊(1 - δ) * q * A.ncard⌋₊ ≤ (A ∩ X ω).ncard} := by
  let r : ℕ := ⌊(1 - δ) * q * A.ncard⌋₊
  have hbad : P.prob {ω | (A ∩ X ω).ncard < r} ≤
      Real.exp (-(δ ^ 2 * q * A.ncard) / 2) := by
    rw [qRandomSet_intersection_card_lt_prob P X A q hX r]
    exact powerset_chernoff_lower_tail A q δ hq0 hq1 hδ0 hδ1
  have hcomp := P.prob_add_prob_compl {ω | (A ∩ X ω).ncard < r}
  have heq : {ω | r ≤ (A ∩ X ω).ncard} = {ω | (A ∩ X ω).ncard < r}ᶜ := by
    ext ω
    simp
  rw [heq, ← hcomp]
  linarith

end Ringel
