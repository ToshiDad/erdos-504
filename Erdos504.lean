import Mathlib

/-!
# Erdős Problem 504 — the minimax angle problem

Formalisation of results of Szekeres (1941) and Erdős–Szekeres (1960) on the
minimax angle problem of Blumenthal (Erdős Problem 504).

Contents so far:

* **M1** `card_le_two_pow_of_side` — the colouring bound (Lemma 2 of
  Erdős–Szekeres 1960, by the product/side-vector argument).
* **M2a** `dirIndex`, `IsPos` — sector index (mod `π`) of a direction, and
  the positive half-turn predicate, with their basic properties.
* **M2b** `lt_angle_of_isPos_of_dirIndex_eq` — if two edges meeting at `q`
  point in positive directions lying in the same sector, then the angle at
  `q` exceeds `(1 - 1/n)·π`.
-/

namespace Erdos504

open Complex Real ComplexConjugate

/-! ## M1: the colouring bound -/

/-- **Colouring bound** (Erdős–Szekeres 1960, Lemma 2, product-argument form).
If every pair of distinct vertices has a colour, and a side assignment
separates the endpoints of every edge within its colour, then there are at
most `2 ^ n` vertices. -/
theorem card_le_two_pow_of_side {V : Type*} [Fintype V] {n : ℕ}
    (color : V → V → Fin n) (side : Fin n → V → Bool)
    (hside : ∀ u v : V, u ≠ v → side (color u v) u ≠ side (color u v) v) :
    Fintype.card V ≤ 2 ^ n := by
  have hinj : Function.Injective (fun v : V => fun i : Fin n => side i v) := by
    intro u v huv
    by_contra hne
    exact hside u v hne (by simpa using congrFun huv (color u v))
  calc
    Fintype.card V ≤ Fintype.card (Fin n → Bool) :=
      Fintype.card_le_of_injective _ hinj
    _ = 2 ^ n := by simp

/-! ## M2a: directions and bins -/

/-- The sector index (modulo `π`) of the direction of `z`: the integer part of
`n · fract (arg z / π)`.  Takes values in `{0, …, n-1}` when `0 < n`. -/
noncomputable def dirIndex (n : ℕ) (z : ℂ) : ℕ :=
  (⌊(n : ℝ) * Int.fract (Complex.arg z / π)⌋).toNat

lemma dirIndex_lt {n : ℕ} (hn : 0 < n) (z : ℂ) : dirIndex n z < n := by
  have h1 : Int.fract (Complex.arg z / π) < 1 := Int.fract_lt_one _
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlt : (n : ℝ) * Int.fract (Complex.arg z / π) < ((n : ℤ) : ℝ) := by
    push_cast
    nlinarith [Int.fract_nonneg (Complex.arg z / π)]
  have hfl : ⌊(n : ℝ) * Int.fract (Complex.arg z / π)⌋ < (n : ℤ) :=
    Int.floor_lt.mpr hlt
  unfold dirIndex
  omega

lemma fract_div_pi_arg_neg (z : ℂ) :
    Int.fract (Complex.arg (-z) / π) = Int.fract (Complex.arg z / π) := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  rcases lt_trichotomy z.im 0 with him | him | him
  · rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg him, add_div,
      div_self Real.pi_ne_zero]
    exact Int.fract_eq_fract.mpr ⟨1, by push_cast; ring⟩
  · -- real axis: z.im = 0, z ≠ 0
    have hre : z.re ≠ 0 := by
      intro h
      apply hz
      apply Complex.ext <;> simp [h, him]
    rcases lt_or_gt_of_ne hre with hre' | hre'
    · have h1 : Complex.arg z = π := Complex.arg_eq_pi_iff.mpr ⟨hre', him⟩
      have h2 : Complex.arg (-z) = 0 := by
        rw [Complex.arg_eq_zero_iff]
        constructor
        · simpa using hre'.le
        · simpa using him
      rw [h1, h2, div_self Real.pi_ne_zero, zero_div, Int.fract_one,
        Int.fract_zero]
    · have h1 : Complex.arg z = 0 := by
        rw [Complex.arg_eq_zero_iff]
        exact ⟨hre'.le, him⟩
      have h2 : Complex.arg (-z) = π := by
        rw [Complex.arg_eq_pi_iff]
        constructor
        · simpa using hre'
        · simpa using him
      rw [h1, h2, div_self Real.pi_ne_zero, zero_div, Int.fract_one,
        Int.fract_zero]
  · rw [Complex.arg_neg_eq_arg_sub_pi_of_im_pos him, sub_div,
      div_self Real.pi_ne_zero]
    exact Int.fract_eq_fract.mpr ⟨-1, by push_cast; ring⟩

/-- The sector index is invariant under negation, hence well defined on
unordered pairs of points. -/
lemma dirIndex_neg (n : ℕ) (z : ℂ) : dirIndex n (-z) = dirIndex n z := by
  unfold dirIndex
  rw [fract_div_pi_arg_neg]

/-- The direction of `z` lies in the upper half-turn `[0, π)`. -/
def IsPos (z : ℂ) : Prop := 0 ≤ Complex.arg z ∧ Complex.arg z < π

lemma isPos_iff {z : ℂ} :
    IsPos z ↔ 0 ≤ z.im ∧ (0 ≤ z.re ∨ z.im ≠ 0) := by
  unfold IsPos
  rw [Complex.arg_nonneg_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rcases lt_or_ge z.re 0 with hre | hre
    · rcases eq_or_ne z.im 0 with him | him
      · exact absurd (Complex.arg_eq_pi_iff.mpr ⟨hre, him⟩) (ne_of_lt h2)
      · exact Or.inr him
    · exact Or.inl hre
  · rintro ⟨h1, h2⟩
    refine ⟨h1, lt_of_le_of_ne (Complex.arg_le_pi z) ?_⟩
    intro h
    rcases Complex.arg_eq_pi_iff.mp h with ⟨hre, him⟩
    rcases h2 with h2 | h2
    · exact absurd hre (not_lt.mpr h2)
    · exact h2 him

/-- For a nonzero vector exactly one of the two orientations is positive. -/
lemma isPos_neg_iff {z : ℂ} (hz : z ≠ 0) : IsPos (-z) ↔ ¬ IsPos z := by
  rw [isPos_iff, isPos_iff]
  simp only [Complex.neg_im, Complex.neg_re, neg_nonneg, ne_eq, neg_eq_zero]
  rcases lt_trichotomy z.im 0 with him | him | him
  · constructor
    · intro _ h
      exact absurd h.1 (not_le.mpr him)
    · intro _
      exact ⟨him.le, Or.inr him.ne⟩
  · have hre : z.re ≠ 0 := by
      intro h
      apply hz
      apply Complex.ext <;> simp [h, him]
    constructor
    · rintro ⟨-, h2⟩ ⟨-, h4⟩
      rcases h2 with h2 | h2
      · rcases h4 with h4 | h4
        · rcases lt_or_gt_of_ne hre with h | h
          · exact absurd h4 (not_le.mpr h)
          · exact absurd h2 (not_le.mpr h)
        · exact h4 him
      · exact h2 him
    · intro h
      rcases lt_or_gt_of_ne hre with h5 | h5
      · exact ⟨him.le, Or.inl h5.le⟩
      · exact absurd ⟨him.ge, Or.inl h5.le⟩ h
  · constructor
    · intro h
      exact absurd him (not_lt.mpr h.1)
    · intro h
      exact absurd ⟨him.le, Or.inr him.ne'⟩ h

/-! ## M2b: the key angle estimate -/

lemma fract_eq_self_of_isPos {z : ℂ} (hz : IsPos z) :
    Int.fract (Complex.arg z / π) = Complex.arg z / π := by
  rw [Int.fract_eq_self]
  constructor
  · exact div_nonneg hz.1 Real.pi_pos.le
  · rw [div_lt_one Real.pi_pos]
    exact hz.2

/-- Two positive directions in the same sector differ by less than `π / n`. -/
lemma abs_arg_sub_lt_of_dirIndex_eq {n : ℕ} (hn : 0 < n) {u w : ℂ}
    (hu : IsPos u) (hw : IsPos w) (h : dirIndex n u = dirIndex n w) :
    |Complex.arg u - Complex.arg w| < π / n := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hn'
  unfold dirIndex at h
  rw [fract_eq_self_of_isPos hu, fract_eq_self_of_isPos hw] at h
  have hx0 : (0 : ℝ) ≤ (n : ℝ) * (Complex.arg u / π) :=
    mul_nonneg hn'.le (div_nonneg hu.1 hπ.le)
  have hy0 : (0 : ℝ) ≤ (n : ℝ) * (Complex.arg w / π) :=
    mul_nonneg hn'.le (div_nonneg hw.1 hπ.le)
  have hfx : 0 ≤ ⌊(n : ℝ) * (Complex.arg u / π)⌋ := Int.floor_nonneg.mpr hx0
  have hfy : 0 ≤ ⌊(n : ℝ) * (Complex.arg w / π)⌋ := Int.floor_nonneg.mpr hy0
  have hfeq : ⌊(n : ℝ) * (Complex.arg u / π)⌋
      = ⌊(n : ℝ) * (Complex.arg w / π)⌋ := by omega
  have hfeqR : ((⌊(n : ℝ) * (Complex.arg u / π)⌋ : ℤ) : ℝ)
      = ((⌊(n : ℝ) * (Complex.arg w / π)⌋ : ℤ) : ℝ) := by
    exact_mod_cast hfeq
  have hb1 := Int.floor_le ((n : ℝ) * (Complex.arg u / π))
  have hb2 := Int.lt_floor_add_one ((n : ℝ) * (Complex.arg u / π))
  have hb3 := Int.floor_le ((n : ℝ) * (Complex.arg w / π))
  have hb4 := Int.lt_floor_add_one ((n : ℝ) * (Complex.arg w / π))
  have habs : |(n : ℝ) * (Complex.arg u / π) - (n : ℝ) * (Complex.arg w / π)|
      < 1 := by
    rw [abs_sub_lt_iff]
    constructor <;> linarith
  have hrw : ((n : ℝ) * (Complex.arg u / π) - (n : ℝ) * (Complex.arg w / π))
      * (π / n) = Complex.arg u - Complex.arg w := by
    field_simp
  have habs' : |Complex.arg u - Complex.arg w|
      = |(n : ℝ) * (Complex.arg u / π) - (n : ℝ) * (Complex.arg w / π)|
        * (π / n) := by
    rw [← hrw, abs_mul, abs_of_pos (div_pos hπ hn')]
  rw [habs']
  calc |(n : ℝ) * (Complex.arg u / π) - (n : ℝ) * (Complex.arg w / π)|
        * (π / n)
      < 1 * (π / n) := by
        exact mul_lt_mul_of_pos_right habs (div_pos hπ hn')
    _ = π / n := one_mul _

/-- The unoriented angle between two nonzero complex vectors equals the
absolute value of `arg (conj u * w)`. -/
lemma angle_eq_abs_arg {u w : ℂ} (hu0 : u ≠ 0) (hw0 : w ≠ 0) :
    InnerProductGeometry.angle u w = |Complex.arg (conj u * w)| := by
  have : Fact (Module.finrank ℝ ℂ = 2) := ⟨Complex.finrank_real_complex⟩
  rw [Complex.orientation.angle_eq_abs_oangle_toReal hu0 hw0, Complex.oangle]
  congr 1
  exact Real.Angle.toReal_coe_eq_self_iff_mem_Ioc.mpr
    ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩

/-- For positive directions the argument of `conj u * w` is the actual
difference of arguments. -/
lemma arg_conj_mul_of_isPos {u w : ℂ} (hu0 : u ≠ 0) (hw0 : w ≠ 0)
    (hu : IsPos u) (hw : IsPos w) :
    Complex.arg (conj u * w) = Complex.arg w - Complex.arg u := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hcu : conj u ≠ 0 := by simpa using hu0
  have h1 : (Complex.arg (conj u * w) : Real.Angle)
      = (Complex.arg (conj u) : Real.Angle) + (Complex.arg w : Real.Angle) :=
    Complex.arg_mul_coe_angle hcu hw0
  have h2 : (Complex.arg (conj u) : Real.Angle)
      = -(Complex.arg u : Real.Angle) := Complex.arg_conj_coe_angle u
  have h3 : (Complex.arg (conj u * w) : Real.Angle)
      = ((Complex.arg w - Complex.arg u : ℝ) : Real.Angle) := by
    rw [h1, h2, Real.Angle.coe_sub]
    abel
  have hmem : Complex.arg w - Complex.arg u ∈ Set.Ioc (-π) π := by
    constructor
    · linarith [hu.2, hw.1]
    · linarith [hu.1, hw.2]
  have harg : Complex.arg (conj u * w) ∈ Set.Ioc (-π) π :=
    ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩
  calc Complex.arg (conj u * w)
      = ((Complex.arg (conj u * w) : Real.Angle)).toReal :=
        (Real.Angle.toReal_coe_eq_self_iff_mem_Ioc.mpr harg).symm
    _ = (((Complex.arg w - Complex.arg u : ℝ)) : Real.Angle).toReal := by
        rw [h3]
    _ = Complex.arg w - Complex.arg u :=
        Real.Angle.toReal_coe_eq_self_iff_mem_Ioc.mpr hmem

/-- **Key angle estimate.**  If the edge from `p` to `q` and the edge from
`q` to `r` both point in positive directions lying in the same sector (of
angular width `π / n`), then the angle at `q` in the triple `p, q, r`
exceeds `(1 - 1/n) · π`. -/
theorem lt_angle_of_isPos_of_dirIndex_eq {n : ℕ} (hn : 0 < n) {p q r : ℂ}
    (hpq : q - p ≠ 0) (hqr : r - q ≠ 0)
    (h1 : IsPos (q - p)) (h2 : IsPos (r - q))
    (hcol : dirIndex n (q - p) = dirIndex n (r - q)) :
    (1 - 1 / (n : ℝ)) * π < EuclideanGeometry.angle p q r := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hbridge : EuclideanGeometry.angle p q r
      = InnerProductGeometry.angle (p - q) (r - q) := by
    simp [EuclideanGeometry.angle, vsub_eq_sub]
  have hneg : p - q = -(q - p) := by ring
  rw [hbridge, hneg, InnerProductGeometry.angle_neg_left]
  have hA : InnerProductGeometry.angle (q - p) (r - q) < π / n := by
    rw [angle_eq_abs_arg hpq hqr, arg_conj_mul_of_isPos hpq hqr h1 h2]
    exact abs_arg_sub_lt_of_dirIndex_eq hn h2 h1 hcol.symm
  have hid : (1 - 1 / (n : ℝ)) * π = π - π / n := by ring
  linarith

/-! ## M2c: the sector colouring and the `2 ^ n` bound -/

/-- **Sector-colouring bound** (Szekeres 1941 / Erdős–Szekeres 1960).
If all angles determined by a finite set of points in the plane are at most
`(1 - 1/n) · π`, then the set has at most `2 ^ n` points. -/
theorem card_le_two_pow_of_angle_le {n : ℕ} (hn : 0 < n) (S : Finset ℂ)
    (hangle : ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
      EuclideanGeometry.angle p q r ≤ (1 - 1 / (n : ℝ)) * π) :
    S.card ≤ 2 ^ n := by
  classical
  rw [← Fintype.card_coe S]
  -- If the edge `u → v` is positively oriented, then `v` has no positive
  -- outgoing edge in the sector of `u → v`.
  have key : ∀ u v : {x // x ∈ S}, (u : ℂ) ≠ (v : ℂ) →
      IsPos ((v : ℂ) - (u : ℂ)) →
      ¬ ∃ w : {x // x ∈ S}, (w : ℂ) ≠ (v : ℂ) ∧ IsPos ((w : ℂ) - (v : ℂ)) ∧
        dirIndex n ((w : ℂ) - (v : ℂ)) = dirIndex n ((v : ℂ) - (u : ℂ)) := by
    rintro u v huv hpos ⟨w, hwv, hwpos, hwcol⟩
    have hpq : (v : ℂ) - (u : ℂ) ≠ 0 := sub_ne_zero.mpr huv.symm
    have hqr : (w : ℂ) - (v : ℂ) ≠ 0 := sub_ne_zero.mpr hwv
    have hbig := lt_angle_of_isPos_of_dirIndex_eq hn hpq hqr hpos hwpos
      hwcol.symm
    have hle := hangle (u : ℂ) u.2 (v : ℂ) v.2 (w : ℂ) w.2 huv hwv
    linarith
  refine card_le_two_pow_of_side
    (fun u v => ⟨dirIndex n ((v : ℂ) - (u : ℂ)), dirIndex_lt hn _⟩)
    (fun i v => decide (∃ w : {x // x ∈ S},
      (w : ℂ) ≠ (v : ℂ) ∧ IsPos ((w : ℂ) - (v : ℂ)) ∧
        dirIndex n ((w : ℂ) - (v : ℂ)) = (i : ℕ))) ?_
  intro u v huv
  have huv' : (u : ℂ) ≠ (v : ℂ) := fun h => huv (Subtype.ext h)
  have hz : (v : ℂ) - (u : ℂ) ≠ 0 := sub_ne_zero.mpr huv'.symm
  have hdi : dirIndex n ((u : ℂ) - (v : ℂ)) = dirIndex n ((v : ℂ) - (u : ℂ)) := by
    rw [show ((u : ℂ) - (v : ℂ)) = -((v : ℂ) - (u : ℂ)) by ring, dirIndex_neg]
  dsimp only
  by_cases hpos : IsPos ((v : ℂ) - (u : ℂ))
  · -- `u` has a positive outgoing edge (to `v`); `v` has none, by `key`.
    have hPu : ∃ w : {x // x ∈ S}, (w : ℂ) ≠ (u : ℂ) ∧
        IsPos ((w : ℂ) - (u : ℂ)) ∧
        dirIndex n ((w : ℂ) - (u : ℂ)) = dirIndex n ((v : ℂ) - (u : ℂ)) :=
      ⟨v, huv'.symm, hpos, rfl⟩
    have hPv : ¬ ∃ w : {x // x ∈ S}, (w : ℂ) ≠ (v : ℂ) ∧
        IsPos ((w : ℂ) - (v : ℂ)) ∧
        dirIndex n ((w : ℂ) - (v : ℂ)) = dirIndex n ((v : ℂ) - (u : ℂ)) :=
      key u v huv' hpos
    have h1 := decide_eq_true hPu
    have h2 := decide_eq_false hPv
    rw [h1, h2]
    simp
  · -- Otherwise `u → v` is negatively oriented, so the roles swap.
    have hpos' : IsPos ((u : ℂ) - (v : ℂ)) := by
      rw [show ((u : ℂ) - (v : ℂ)) = -((v : ℂ) - (u : ℂ)) by ring]
      exact (isPos_neg_iff hz).mpr hpos
    have hPv : ∃ w : {x // x ∈ S}, (w : ℂ) ≠ (v : ℂ) ∧
        IsPos ((w : ℂ) - (v : ℂ)) ∧
        dirIndex n ((w : ℂ) - (v : ℂ)) = dirIndex n ((v : ℂ) - (u : ℂ)) :=
      ⟨u, huv', hpos', hdi⟩
    have hPu : ¬ ∃ w : {x // x ∈ S}, (w : ℂ) ≠ (u : ℂ) ∧
        IsPos ((w : ℂ) - (u : ℂ)) ∧
        dirIndex n ((w : ℂ) - (u : ℂ)) = dirIndex n ((v : ℂ) - (u : ℂ)) := by
      rintro ⟨w, hwu, hwpos, hwcol⟩
      exact key v u huv'.symm hpos' ⟨w, hwu, hwpos, hwcol.trans hdi.symm⟩
    have h1 := decide_eq_false hPu
    have h2 := decide_eq_true hPv
    rw [h1, h2]
    simp
/-- **Szekeres (1941).**  Any set of more than `2 ^ n` points in the plane
determines an angle greater than `(1 - 1/n) · π`. -/
theorem exists_angle_gt {n : ℕ} (hn : 0 < n) (S : Finset ℂ)
    (hcard : 2 ^ n < S.card) :
    ∃ p ∈ S, ∃ q ∈ S, ∃ r ∈ S, p ≠ q ∧ r ≠ q ∧
      (1 - 1 / (n : ℝ)) * π < EuclideanGeometry.angle p q r := by
  by_contra hcon
  push_neg at hcon
  exact absurd (card_le_two_pow_of_angle_le hn S hcon)
    (not_le.mpr hcard)

end Erdos504
