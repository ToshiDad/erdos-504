# Erdős Problem 504 — Blumenthal's minimax angle problem

Lean 4 formalisation of the Szekeres (1941) bounds and the Erdős–Szekeres
(1960) theorem on the minimax angle problem
([Erdős Problem #504](https://www.erdosproblems.com/504)).

Single file `Erdos504.lean`, sorry-free, using only the standard axioms
`propext`, `Classical.choice`, `Quot.sound`.

## Formalised theorems

All three results are stated in the same vocabulary: finite sets
`S : Finset ℂ` of points in the plane (modelled as `ℂ`), and the unsigned
vertex angle `EuclideanGeometry.angle p q r` at `q`, valued in `[0, π]`.
The statements below are quoted verbatim from `Erdos504.lean`.

**1. Szekeres (1941), lower bound.** More than `2^n` points determine an
angle strictly greater than `(1 - 1/n)·π`:

```lean
theorem exists_angle_gt {n : ℕ} (hn : 0 < n) (S : Finset ℂ)
    (hcard : 2 ^ n < S.card) :
    ∃ p ∈ S, ∃ q ∈ S, ∃ r ∈ S, p ≠ q ∧ r ≠ q ∧
      (1 - 1 / (n : ℝ)) * π < EuclideanGeometry.angle p q r
```

**2. Szekeres (1941), upper-bound construction (ε-relaxed form).** For
every `ε > 0` there is a set of exactly `2^t` points all of whose angles
are below `(1 - 1/t)·π + ε`:

```lean
theorem exists_config_angle_lt {t : ℕ} (ht : 0 < t) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset ℂ, S.card = 2 ^ t ∧
      ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
        EuclideanGeometry.angle p q r < (1 - 1 / (t : ℝ)) * π + ε
```

Note this is deliberately the ε-relaxed form: no finite configuration
attains all angles `≤ (1 - 1/t)·π` (see Theorem 3), so the supremum is
approached but not attained, and the ε-family is the correct formal
counterpart of Szekeres' construction.

**3. Erdős–Szekeres (1960), Theorem 1.** Already `2^n` points (no general
position hypothesis) determine an angle strictly greater than
`(1 - 1/n)·π`:

```lean
theorem erdos_szekeres_1960 {n : ℕ} (hn : 3 ≤ n) (S : Finset ℂ)
    (hcard : S.card = 2 ^ n) :
    ∃ p ∈ S, ∃ q ∈ S, ∃ r ∈ S, p ≠ q ∧ r ≠ q ∧
      (1 - 1 / (n : ℝ)) * π < EuclideanGeometry.angle p q r
```

The witnesses satisfy `p ≠ q` and `r ≠ q` (angle at the vertex `q`); a
witness with `p = r` is impossible since its angle is `0`, so the three
points are automatically pairwise distinct.

A key intermediate result is formalised independently and may be of
separate interest:

```lean
lemma regular_ngon_interior_sees_wide
```

(Lemma 6: an interior point of a regular n-gon distinct from the centre
sees some pair of vertices at an angle exceeding `(1 - 1/n)·π`.)

## Scope

Writing `α(N)` for the minimax angle (the supremum of the angles
guaranteed in every `N`-point set), Theorems 2 and 3 together determine

```
α(2^n) = (1 - 1/n) · π   for n ≥ 3,
```

as an informal corollary: Theorem 3 gives the lower bound and Theorem 2
shows it is sharp. The supremum-based quantity `α` itself is not defined
in Lean in this repository; only the two bounds above are formalised.

Not formalised (future work): the endpoint `α(2^n - 1)` from
Erdős–Szekeres (1960), and Sendov's complete determination of `α(N)`
(Acta Math. Hungar. 69 (1995), 27–46).

## Verification

Toolchain is pinned by `lean-toolchain` (Lean 4.33.0) and
`lake-manifest.json` (Mathlib commit fixed).

```
lake exe cache get
lake env lean Erdos504.lean
```

Axiom check (append to the file or run in a scratch copy):

```
#print axioms Erdos504.exists_angle_gt
#print axioms Erdos504.exists_config_angle_lt
#print axioms Erdos504.erdos_szekeres_1960
-- each: [propext, Classical.choice, Quot.sound]
```

## References

- G. Szekeres, On an extremum problem in the plane, Amer. J. Math. 63
  (1941), 208–210.
- P. Erdős and G. Szekeres, On some extremum problems in elementary
  geometry, Ann. Univ. Sci. Budapest. Eötvös Sect. Math. 3–4 (1960–61),
  53–62.
- T. F. Bloom, Erdős Problem #504, https://www.erdosproblems.com/504.
