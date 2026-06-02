# 🌳 Ringel's Conjecture in Lean 4

<p align="center">
  <b>A Lean 4 formalization of the Montgomery–Pokrovskiy–Sudakov proof of Ringel's Conjecture.</b><br/>
  <i>Every tree with n edges packs 2n+1 times into the complete graph K₂ₙ₊₁.</i>
</p>

<p align="center">
  <img src="https://img.shields.io/badge/status-statement%20only-orange" alt="status">
  <img src="https://img.shields.io/badge/Lean-4.30.0-blue" alt="Lean Version">
  <img src="https://img.shields.io/badge/Mathlib-v4.30.0-purple" alt="Mathlib Version">
</p>

---

Ringel's Conjecture (1963): for every tree `T` with `n` edges, the complete graph `K_{2n+1}` on
`2n+1` vertices decomposes into `2n+1` edge-disjoint copies of `T`. It was proved for all
sufficiently large `n` by R. Montgomery, A. Pokrovskiy and B. Sudakov (arXiv:2001.02665). This
repository formalizes that proof in Lean 4.

The statement lives in [`Ringel/Statement.lean`](Ringel/Statement.lean) as `Ringel.ringel_conjecture`
and currently compiles with a single `sorry` standing in for the full proof.

```lean
theorem ringel_conjecture {V : Type*} [Fintype V]
    (T : SimpleGraph V) (hT : T.IsTree)
    (n : ℕ) (hn : T.edgeSet.ncard = n) :
    ∃ f : Fin (2 * n + 1) → (V ↪ Fin (2 * n + 1)),
      Pairwise (fun i j => Disjoint (T.map (f i)).edgeSet (T.map (f j)).edgeSet) ∧
      ⨆ i, T.map (f i) = (⊤ : SimpleGraph (Fin (2 * n + 1)))
```

---

## Status

- [x] Project scaffold
- [x] Statement formalized & reviewed (`Ringel/Statement.lean`)
- [ ] Statement contributed to [formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
- [ ] Blueprint (lemma DAG from the paper)
- [ ] Supporting infrastructure (graph decomposition, absorption, randomized embedding)
- [ ] Full proof

---

## Build

```bash
git clone https://github.com/Doublew08/Ringel.git && cd Ringel
lake exe cache get   # download precompiled dependencies (recommended)
lake build
```

Requires [Lean 4 (elan)](https://leanprover.github.io/lean4/doc/setup.html); the toolchain is
pinned by `lean-toolchain`.

---

## References

- R. Montgomery, A. Pokrovskiy, B. Sudakov (2020).
  [*A proof of Ringel's Conjecture*](https://arxiv.org/abs/2001.02665).
  J. Eur. Math. Soc. **22**, 3101–3132.

License: Apache 2.0.
