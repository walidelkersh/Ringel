/-
Copyright (c) 2026 Walid Elkersh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Walid Elkersh
-/
import Mathlib.Data.Sym.Sym2
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Data.Set.Card
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Nat.Log

/-!
# Primitives for the Montgomery–Pokrovskiy–Sudakov proof of Ringel's Conjecture

This file collects the combinatorial primitives the MPS proof is built on. None of these has a
direct mathlib equivalent, so they are the genuine foundation layer: every lemma signature in the
proof (`Ringel/Spine.lean` and the per-section files to come) elaborates against the definitions
here.

-/

open SimpleGraph

namespace Ringel

/-- Directed colour from $i$ to $j$: the forward distance $(j - i) \bmod (2n+1)$, mapped to
`Fin n`.  Real edges have `d ≠ 0`; the `d = 0` branch is an unreachable junk value. -/
private def ndColour (n : ℕ) (hn : 0 < n) (i j : Fin (2 * n + 1)) : Fin n :=
  let d := (j.val + (2 * n + 1) - i.val) % (2 * n + 1)
  if hd : 0 < d ∧ d ≤ n then ⟨d - 1, by omega⟩
  else if _ : n < d      then ⟨2 * n - d, by omega⟩
  else ⟨0, hn⟩

/-- `ndColour` is symmetric.
Forward distance $d_i = (j-i) \bmod (2n+1)$ and backward $d_j = (i-j) \bmod (2n+1)$ satisfy
$d_i + d_j \in \{0, 2n+1\}$ (both zero iff $i = j$; else complementary → same colour). -/
private theorem ndColour_symm (n : ℕ) (hn : 0 < n) (i j : Fin (2 * n + 1)) :
    ndColour n hn i j = ndColour n hn j i := by
  simp only [ndColour]
  -- Use ↑ coercion notation to match the goal after simp unfolds ndColour
  set d₁ := (↑j + (2 * n + 1) - ↑i) % (2 * n + 1)
  set d₂ := (↑i + (2 * n + 1) - ↑j) % (2 * n + 1)
  have hi := i.isLt; have hj := j.isLt
  have hd₁_lt : d₁ < 2 * n + 1 := Nat.mod_lt _ (by omega)
  have hd₂_lt : d₂ < 2 * n + 1 := Nat.mod_lt _ (by omega)
  have hmod : (d₁ + d₂) % (2 * n + 1) = 0 := by
    show ((↑j + (2*n+1) - ↑i) % (2*n+1) + (↑i + (2*n+1) - ↑j) % (2*n+1)) % (2*n+1) = 0
    rw [← Nat.add_mod, show ↑j + (2*n+1) - ↑i + (↑i + (2*n+1) - ↑j) = (2*n+1) * 2 from by omega]
    exact Nat.mul_mod_right _ _
  have hsum : d₁ = 0 ∧ d₂ = 0 ∨ d₁ + d₂ = 2 * n + 1 := by
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hmod
    have hklt : k < 2 :=
      lt_of_mul_lt_mul_left (show (2 * n + 1) * k < (2 * n + 1) * 2 by linarith) (Nat.zero_le _)
    interval_cases k
    · left; omega
    · right; linarith
  -- d₁/d₂ are set-defined locals, can't use rfl pattern; bind them
  rcases hsum with ⟨h1, h2⟩ | hsum
  · split_ifs <;> simp_all [Fin.ext_iff] <;> omega
  · split_ifs <;> simp_all [Fin.ext_iff] <;> omega

/-- The **near-distance (ND-) colouring** of $K_{2n+1}$. Edge $\{i,j\}$ receives colour
$k \in \{0,\ldots,n-1\}$ where $k + 1 = \min((j-i) \bmod (2n+1),\, (i-j) \bmod (2n+1))$. (§1.) -/
def ndColouring (n : ℕ) (hn : 0 < n) : Sym2 (Fin (2 * n + 1)) → Fin n :=
  Sym2.lift ⟨ndColour n hn, ndColour_symm n hn⟩

lemma ndColour_val_eq_sub (n : ℕ) (u v : Fin (2 * n + 1)) :
    (v.val + (2 * n + 1) - u.val) % (2 * n + 1) = (v - u).val := by
  rw [Fin.sub_def]
  have h1 : v.val + (2 * n + 1) - u.val = 2 * n + 1 - u.val + v.val := by
    have := u.isLt
    omega
  rw [h1]

lemma ndColouring_addRight (n : ℕ) (hn : 0 < n) (u v i : Fin (2 * n + 1)) :
    ndColouring n hn s(u + i, v + i) = ndColouring n hn s(u, v) := by
  have h_eq : ((v + i).val + (2 * n + 1) - (u + i).val) % (2 * n + 1) =
              (v.val + (2 * n + 1) - u.val) % (2 * n + 1) := by
    rw [ndColour_val_eq_sub, ndColour_val_eq_sub]
    have : v + i - (u + i) = v - u := by abel
    rw [this]
  dsimp only [ndColouring, Sym2.lift_mk]
  unfold ndColour
  dsimp only
  simp only [h_eq]

/-- If the endpoints `x` and `x + δ` differ by `δ` with `δ.val = c+1` or `δ.val = 2n+1-(c+1)`,
then the ND-colour of the edge `s(x, x+δ)` is `c`. This is the arithmetic core behind the Case A
embedding: a `±(c+1)` step in `Fin (2n+1)` realizes colour `c`. -/
lemma ndColouring_step (n : ℕ) (hn : 0 < n) (x δ : Fin (2 * n + 1)) (c : Fin n)
    (h : δ.val = c.val + 1 ∨ δ.val = 2 * n + 1 - (c.val + 1)) :
    ndColouring n hn s(x, x + δ) = c := by
  have hd : ((x + δ).val + (2 * n + 1) - x.val) % (2 * n + 1) = δ.val := by
    rw [ndColour_val_eq_sub]; congr 1; abel
  change ndColour n hn x (x + δ) = c
  have hc := c.isLt
  simp only [ndColour, hd]
  rcases h with h | h
  · rw [dif_pos ⟨by omega, by omega⟩]; apply Fin.ext; simp; omega
  · rw [dif_neg (by omega), dif_pos (by omega)]; apply Fin.ext; simp; omega

/-- A colouring is a **2-factorization** if every vertex is incident to exactly two edges of each
colour. The ND-colouring is the running example. (§2.) -/
def IsTwoFactorization (n : ℕ) (c : Sym2 (Fin (2 * n + 1)) → Fin n) : Prop :=
  ∀ (v : Fin (2 * n + 1)) (col : Fin n),
    {e : Sym2 (Fin (2 * n + 1)) | v ∈ e ∧ ¬e.IsDiag ∧ c e = col}.ncard = 2

set_option maxHeartbeats 400000 in
theorem ndColouring_isTwoFactorization (n : ℕ) (hn : 0 < n) :
    IsTwoFactorization n (ndColouring n hn) := by
  intro v col
  have hv := v.isLt
  have hc := col.isLt
  set d := col.val + 1 with hd_def
  have hd1 : 1 ≤ d := by omega
  have hdn : d ≤ n := by omega
  have hd_lt : d < 2*n+1 := by omega
  set w₁ : Fin (2*n+1) := ⟨(v.val + d) % (2*n+1), Nat.mod_lt _ (by omega)⟩ with hw1_def
  set w₂ : Fin (2*n+1) := ⟨(v.val + (2*n+1) - d) % (2*n+1), Nat.mod_lt _ (by omega)⟩ with hw2_def
  
  have hfd1 : (w₁.val + (2*n+1) - v.val) % (2*n+1) = d := by
    have hw1v : w₁.val = (v.val + d) % (2*n+1) := rfl
    rcases Nat.lt_or_ge (v.val + d) (2*n+1) with hlt | hge
    · have : w₁.val = v.val + d := by rw [hw1v, Nat.mod_eq_of_lt hlt]
      rw [this]
      rw [show v.val + d + (2*n+1) - v.val = d + (2*n+1) by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    · have : w₁.val = v.val + d - (2*n+1) := by
        rw [hw1v, Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
      rw [this, show v.val + d - (2*n+1) + (2*n+1) - v.val = d by omega, Nat.mod_eq_of_lt (by omega)]
      
  have hfd2 : (w₂.val + (2*n+1) - v.val) % (2*n+1) = 2*n+1 - d := by
    have hw2v : w₂.val = (v.val + (2*n+1) - d) % (2*n+1) := rfl
    rcases Nat.lt_or_ge (v.val + (2*n+1) - d) (2*n+1) with hlt | hge
    · have : w₂.val = v.val + (2*n+1) - d := by rw [hw2v, Nat.mod_eq_of_lt hlt]
      rw [this, show v.val + (2*n+1) - d + (2*n+1) - v.val = (2*n+1 - d) + (2*n+1) by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · have : w₂.val = v.val + (2*n+1) - d - (2*n+1) := by
        rw [hw2v, Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
      rw [this, show v.val + (2*n+1) - d - (2*n+1) + (2*n+1) - v.val = 2*n+1 - d by omega,
        Nat.mod_eq_of_lt (by omega)]
        
  have hw1v_ne : w₁ ≠ v := by
    intro h; rw [h] at hfd1
    rw [show v.val + (2*n+1) - v.val = 2*n+1 by omega, Nat.mod_self] at hfd1; omega
  have hw2v_ne : w₂ ≠ v := by
    intro h; rw [h] at hfd2
    rw [show v.val + (2*n+1) - v.val = 2*n+1 by omega, Nat.mod_self] at hfd2; omega
  have hw12_ne : w₁ ≠ w₂ := by
    intro h; rw [h] at hfd1; rw [hfd1] at hfd2; omega

  have hset : {e : Sym2 (Fin (2 * n + 1)) | v ∈ e ∧ ¬e.IsDiag ∧ ndColouring n hn e = col}
      = {s(v, w₁), s(v, w₂)} := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
        Sym2.mem_iff, Sym2.mk_isDiag_iff]
      constructor
      · rintro ⟨hve, hdiag, hcol⟩
        have huniq : ∀ w : Fin (2*n+1), ∀ t : ℕ, t < 2*n+1 →
            (w.val + (2*n+1) - v.val) % (2*n+1) = t → w.val = (v.val + t) % (2*n+1) := by
          intro w t ht hwt
          have hwlt := w.isLt
          rcases Nat.lt_or_ge (w.val + (2*n+1) - v.val) (2*n+1) with hlt | hge
          · have : w.val + (2*n+1) - v.val = t := by rw [← hwt, Nat.mod_eq_of_lt hlt]
            rcases Nat.lt_or_ge (v.val + t) (2*n+1) with h2 | h2
            · rw [Nat.mod_eq_of_lt h2]; omega
            · rw [Nat.mod_eq_sub_mod h2, Nat.mod_eq_of_lt (by omega)]; omega
          · have : w.val + (2*n+1) - v.val - (2*n+1) = t := by
              rw [← hwt, Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
            rcases Nat.lt_or_ge (v.val + t) (2*n+1) with h2 | h2
            · rw [Nat.mod_eq_of_lt h2]; omega
            · rw [Nat.mod_eq_sub_mod h2, Nat.mod_eq_of_lt (by omega)]; omega
        have key : ∀ w : Fin (2*n+1), w ≠ v → ndColour n hn v w = col →
            s(v, w) = s(v, w₁) ∨ s(v, w) = s(v, w₂) := by
          intro w hwv hcw
          have hd_w : (w.val + (2*n+1) - v.val) % (2*n+1) = col.val + 1 ∨
                      (w.val + (2*n+1) - v.val) % (2*n+1) = 2*n+1 - (col.val + 1) := by
            have hcw2 : ndColour n hn v w = col := hcw
            simp only [ndColour] at hcw2
            set dw := (w.val + (2 * n + 1) - v.val) % (2 * n + 1)
            have hdw_lt : dw < 2 * n + 1 := Nat.mod_lt _ (by omega)
            have hc_lt : col.val < n := col.isLt
            split_ifs at hcw2 with h1 h2
            · left; rw [Fin.ext_iff] at hcw2; simp at hcw2; omega
            · right; rw [Fin.ext_iff] at hcw2; simp at hcw2
              have h_sub : 2 * n + 1 - (col.val + 1) = 2 * n - col.val := by omega
              rw [h_sub]
              omega
            · have hv_lt := v.isLt
              have hw_lt := w.isLt
              have h_dw_0 : dw = 0 := by omega
              have h_mod : (w.val + (2*n+1) - v.val) % (2*n+1) = 0 := h_dw_0
              obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h_mod
              have h_k : k = 1 := by
                have h_upper : (w.val + (2*n+1) - v.val) < (2*n+1) * 2 := by omega
                have h_lower : (w.val + (2*n+1) - v.val) > 0 := by omega
                nlinarith
              rw [h_k] at hk
              have h_eq : w.val = v.val := by omega
              have : w = v := Fin.ext h_eq
              contradiction
          rcases hd_w with hd_w | hd_w
          · left; rw [Sym2.eq_iff]; left; refine ⟨rfl, Fin.ext ?_⟩
            have := huniq w d hd_lt hd_w
            rw [this]
          · right; rw [Sym2.eq_iff]; left; refine ⟨rfl, Fin.ext ?_⟩
            have := huniq w (2*n+1-d) (by omega) hd_w
            rw [this]
            have hw2v : w₂.val = (v.val + (2*n+1) - d) % (2*n+1) := rfl
            rw [hw2v]
            congr 1; omega
        rcases hve with h_va | h_vb
        · have hbv : b ≠ v := fun h => hdiag (by rw [← h_va, h])
          have hcol' : ndColour n hn v b = col := by
            rw [← h_va] at hcol; exact hcol
          have hk := key b hbv hcol'
          rw [← h_va]
          exact hk
        · have hav : a ≠ v := fun h => hdiag (by rw [← h_vb, h])
          have hcol' : ndColour n hn v a = col := by
            rw [← h_vb] at hcol
            have h1 : ndColouring n hn s(a, v) = ndColour n hn a v := rfl
            rw [h1, ndColour_symm] at hcol; exact hcol
          have hk := key a hav hcol'
          rw [← h_vb, Sym2.eq_swap]
          exact hk
      · have hcw1 : ndColour n hn v w₁ = col := by
          simp only [ndColour]
          simp only [hfd1]
          rw [dif_pos ⟨by omega, by omega⟩]
          rw [Fin.ext_iff]
          simp; omega
        have hcw2 : ndColour n hn v w₂ = col := by
          simp only [ndColour]
          simp only [hfd2]
          have h2 : ¬(0 < 2 * n + 1 - (col.val + 1) ∧ 2 * n + 1 - (col.val + 1) ≤ n) := by omega
          rw [dif_neg h2, dif_pos (by omega)]
          rw [Fin.ext_iff]
          simp; omega
        rintro (heq | heq)
        · rw [Sym2.eq_iff] at heq
          rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨Or.inl rfl, fun hd => hw1v_ne hd.symm, hcw1⟩
          · exact ⟨Or.inr rfl, fun hd => hw1v_ne hd, by rw [Sym2.eq_swap]; exact hcw1⟩
        · rw [Sym2.eq_iff] at heq
          rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨Or.inl rfl, fun hd => hw2v_ne hd.symm, hcw2⟩
          · exact ⟨Or.inr rfl, fun hd => hw2v_ne hd, by rw [Sym2.eq_swap]; exact hcw2⟩
  rw [hset, Set.ncard_pair (by
    intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨_, h⟩ | ⟨_, h⟩
    · exact hw12_ne h
    · exact hw1v_ne h)]

/-- A colouring is **locally $k$-bounded** if every vertex meets at most $k$ edges of any one
colour. (A 2-factorization is locally $2$-bounded.) (§3.) -/
def IsLocallyBounded (n k : ℕ) (c : Sym2 (Fin (2 * n + 1)) → Fin n) : Prop :=
  ∀ (v : Fin (2 * n + 1)) (col : Fin n),
    {e : Sym2 (Fin (2 * n + 1)) | v ∈ e ∧ ¬e.IsDiag ∧ c e = col}.ncard ≤ k

/-- `HasRainbowCopy n T` holds when the ND-coloured $K_{2n+1}$ contains a **rainbow copy** of the
tree $T$: an embedding of $T$ whose edge images all receive distinct ND-colours. This is the object
Theorem `Theorem_Ringel_proof` produces. (§1–§2.) -/
def HasRainbowCopy (n : ℕ) {V : Type*} (T : SimpleGraph V) : Prop :=
  ∃ f : V ↪ Fin (2 * n + 1),
    ∀ (hn : 0 < n), Set.InjOn (ndColouring n hn) (T.map f).edgeSet

/-- A subset $S$ of vertices (or colours) is **$q$-random** if each element is included
independently with probability $q$. Requires measure-theoretic probability infrastructure. (§3.) -/
def IsRandomSubset {α : Type*} (_q : ℝ) (_S : Set α) : Prop := True

/-- $(X, A)$ is **$r$-replete** when every $x \in X$ has at least $r$ neighbours in $A$ inside
$K_{2n+1}$. Used in the absorption arguments. (§4.) -/
def IsReplete (n : ℕ) (X A : Set (Fin (2 * n + 1))) (r : ℕ) : Prop :=
  ∀ x ∈ X, r ≤ (A \ {x}).ncard

/-- A **bare path** of a tree: a simple path whose internal vertices all have degree $2$ in $T$.
Used by the Case A/B/C division. (§2–§3.) -/
def IsBarePath {V : Type*} (T : SimpleGraph V) (P : List V) : Prop :=
  P.IsChain T.Adj ∧ P.Nodup ∧ ∀ v ∈ P.tail.dropLast, (T.neighborSet v).ncard = 2

/-- Vertex $v$ is a **leaf** of $T$: it has a unique neighbour. -/
def IsLeaf {V : Type*} (T : SimpleGraph V) (v : V) : Prop :=
  ∃! w : V, T.Adj v w

/-- **Case A** (§2): $T$ with $n$ edges has $\geq \lfloor \delta^6 n \rfloor$ pairwise non-adjacent leaves. -/
def IsCaseA (δ : ℝ) (n : ℕ) {V : Type*} (T : SimpleGraph V) : Prop :=
  ∃ S : Set V,
    (∀ v ∈ S, IsLeaf T v) ∧
    (∀ v ∈ S, ∀ w ∈ S, v ≠ w → ¬T.Adj v w) ∧
    ⌊δ ^ 6 * (n : ℝ)⌋₊ ≤ S.ncard

/-- **Case B** (§2): $T$ with $n$ edges has $\geq \lfloor \delta n/800 \rfloor$ vertex-disjoint bare paths each of
length $\lfloor \delta^{-1} \rfloor$ edges. Paths are vertex-disjoint (full vertex sets pairwise disjoint).
A bare path $P$ is a list of vertices forming a simple path whose internal vertices have degree $2$ in $T$. -/
def IsCaseB (δ : ℝ) (n : ℕ) {V : Type*} (T : SimpleGraph V) : Prop :=
  ∃ paths : List (List V),
    (∀ P ∈ paths, IsBarePath T P) ∧
    (∀ P ∈ paths, P.length = ⌊(δ : ℝ)⁻¹⌋₊ + 1) ∧
    (∀ P ∈ paths, ∀ Q ∈ paths, P ≠ Q →
      Disjoint ({v : V | v ∈ P} : Set V) {v : V | v ∈ Q}) ∧
    ⌊δ * (n : ℝ) / 800⌋₊ ≤ paths.length

/-- The Case C leaf-degree threshold. A core vertex counts as *high leaf degree* when it has at
least `caseCThreshold n` pendant-leaf neighbours. The paper uses a `log⁴ n` threshold; the value
here is `8000·⌊log₂ n⌋ + 20000`, chosen so that a high-leaf-degree vertex carries enough leaves
(`≥ 4000·(2k+1)` with `n < 2^(k-1)`) for the many-high-degree-vertex embedding
`caseC_many_vertex` to apply. It is `Θ(log n)`, which the sharper doubling invariant of
`caseC_many_vertex` improves over the paper's `log⁴ n`. -/
def caseCThreshold (n : ℕ) : ℕ := 8000 * Nat.log 2 n + 20000

/-- **Case C** (§2): deleting leaves adjacent to vertices with $\geq$ `caseCThreshold n`
leaf-neighbours leaves $\leq n/100$ vertices. -/
def IsCaseC (_δ : ℝ) (n : ℕ) {V : Type*} (T : SimpleGraph V) : Prop :=
  let highLeafDeg : Set V :=
    {v | caseCThreshold n ≤ {w | T.Adj v w ∧ IsLeaf T w}.ncard}
  let removedLeaves : Set V :=
    {v | IsLeaf T v ∧ ∃ w, T.Adj v w ∧ w ∈ highLeafDeg}
  (Set.univ \ removedLeaves).ncard ≤ n / 100

end Ringel
