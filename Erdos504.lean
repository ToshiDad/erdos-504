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

/-! ## M3a: a perturbation bound for `arg` -/

lemma abs_self_le_abs_tan {x : ℝ} (h : |x| < π / 2) : |x| ≤ |Real.tan x| := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have h1 : (0 : ℝ) < -x := by linarith
    have h2 : -x < π / 2 := by
      have := abs_of_neg hx
      linarith [le_abs_self (-x), neg_le_abs x, this ▸ h]
    have h3 := Real.lt_tan h1 h2
    rw [Real.tan_neg] at h3
    calc |x| = -x := abs_of_neg hx
      _ ≤ -Real.tan x := le_of_lt h3
      _ ≤ |Real.tan x| := neg_le_abs _
  · simp
  · have h2 : x < π / 2 := lt_of_le_of_lt (le_abs_self x) h
    have h3 := Real.lt_tan hx h2
    calc |x| = x := abs_of_pos hx
      _ ≤ Real.tan x := le_of_lt h3
      _ ≤ |Real.tan x| := le_abs_self _

/-- If `w` lies within `δ < 1` of `1`, then `|arg w| ≤ δ / (1 - δ)`. -/
lemma abs_arg_le_of_norm_sub_one_le {w : ℂ} {δ : ℝ} (hδ : δ < 1)
    (h : ‖w - 1‖ ≤ δ) : |Complex.arg w| ≤ δ / (1 - δ) := by
  have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) h
  have h1δ : (0 : ℝ) < 1 - δ := by linarith
  have hre : 1 - δ ≤ w.re := by
    have h1 : |(w - 1).re| ≤ ‖w - 1‖ := Complex.abs_re_le_norm _
    have h2 : (w - 1).re = w.re - 1 := by simp
    rw [h2] at h1
    have := abs_le.mp (le_trans h1 h)
    linarith [this.1]
  have hrepos : 0 < w.re := by linarith
  have him : |w.im| ≤ δ := by
    have h1 : |(w - 1).im| ≤ ‖w - 1‖ := Complex.abs_im_le_norm _
    have h2 : (w - 1).im = w.im := by simp
    rw [h2] at h1
    exact le_trans h1 h
  have harg2 : |Complex.arg w| < π / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hrepos)
  have htan : |Real.tan (Complex.arg w)| ≤ δ / (1 - δ) := by
    rw [Complex.tan_arg, abs_div, abs_of_pos hrepos]
    rw [div_le_div_iff₀ hrepos h1δ]
    nlinarith [abs_nonneg w.im]
  exact le_trans (abs_self_le_abs_tan harg2) htan

/-! ## M3b: invariance of the angle under complex scaling -/

/-- Multiplying both vectors by a nonzero complex scalar preserves the
(unoriented) angle: complex multiplication is a similarity of the plane. -/
lemma angle_const_mul {c z w : ℂ} (hc : c ≠ 0) (hz : z ≠ 0) (hw : w ≠ 0) :
    InnerProductGeometry.angle (c * z) (c * w)
      = InnerProductGeometry.angle z w := by
  rw [angle_eq_abs_arg (mul_ne_zero hc hz) (mul_ne_zero hc hw),
    angle_eq_abs_arg hz hw]
  congr 1
  have hkey : conj (c * z) * (c * w) = (Complex.normSq c : ℂ) * (conj z * w) := by
    rw [map_mul]
    calc conj c * conj z * (c * w) = c * conj c * (conj z * w) := by ring
      _ = (Complex.normSq c : ℂ) * (conj z * w) := by rw [Complex.mul_conj]
  rw [hkey, Complex.arg_real_mul _ (Complex.normSq_pos.mpr hc)]

/-! ## M3c: perturbed angles -/

lemma one_add_ne_zero_of_norm_lt_one {w : ℂ} (h : ‖w‖ < 1) : 1 + w ≠ 0 := by
  intro hw
  have hw' : w = -1 := by linear_combination hw
  rw [hw'] at h
  simp at h

/-- Scaling `c` by a factor within `δ` of `1` tilts its direction by at most
`δ / (1 - δ)`. -/
lemma angle_one_add_le {c w : ℂ} {δ : ℝ} (hc : c ≠ 0) (hδ : δ < 1)
    (hw : ‖w‖ ≤ δ) :
    InnerProductGeometry.angle c (c * (1 + w)) ≤ δ / (1 - δ) := by
  have h1 : ‖w‖ < 1 := lt_of_le_of_lt hw hδ
  have h1w : (1 : ℂ) + w ≠ 0 := one_add_ne_zero_of_norm_lt_one h1
  have hstep : InnerProductGeometry.angle c (c * (1 + w))
      = InnerProductGeometry.angle 1 (1 + w) := by
    have := angle_const_mul hc one_ne_zero h1w
    simpa using this
  rw [hstep, angle_eq_abs_arg one_ne_zero h1w]
  have hone : conj (1 : ℂ) * (1 + w) = 1 + w := by simp
  rw [hone]
  apply abs_arg_le_of_norm_sub_one_le hδ
  simpa using hw

/-- **Perturbation sandwich.**  The angle between two perturbed vectors
`c₁ (1 + w₁)` and `c₂ (1 + w₂)` exceeds the ideal angle between `c₁` and
`c₂` by at most `2 δ / (1 - δ)`, provided `‖wᵢ‖ ≤ δ < 1`. -/
lemma angle_perturb_le {c₁ c₂ w₁ w₂ : ℂ} {δ : ℝ} (hc₁ : c₁ ≠ 0)
    (hc₂ : c₂ ≠ 0) (hδ : δ < 1) (hw₁ : ‖w₁‖ ≤ δ) (hw₂ : ‖w₂‖ ≤ δ) :
    InnerProductGeometry.angle (c₁ * (1 + w₁)) (c₂ * (1 + w₂))
      ≤ InnerProductGeometry.angle c₁ c₂ + 2 * (δ / (1 - δ)) := by
  have t1 := InnerProductGeometry.angle_le_angle_add_angle
    (c₁ * (1 + w₁)) c₁ (c₂ * (1 + w₂))
  have t2 := InnerProductGeometry.angle_le_angle_add_angle
    c₁ c₂ (c₂ * (1 + w₂))
  have a1 : InnerProductGeometry.angle (c₁ * (1 + w₁)) c₁ ≤ δ / (1 - δ) := by
    rw [InnerProductGeometry.angle_comm]
    exact angle_one_add_le hc₁ hδ hw₁
  have a2 : InnerProductGeometry.angle c₂ (c₂ * (1 + w₂)) ≤ δ / (1 - δ) :=
    angle_one_add_le hc₂ hδ hw₂
  linarith

/-! ## M3d1: the Szekeres configuration and its dominant-term decomposition -/

/-- The `j`-th sector direction `e^{iπj/t}`. -/
noncomputable def szDir (t : ℕ) (j : ℕ) : ℂ :=
  Complex.exp ((Real.pi * j / t : ℝ) * Complex.I)

lemma norm_szDir (t j : ℕ) : ‖szDir t j‖ = 1 := by
  unfold szDir
  exact Complex.norm_exp_ofReal_mul_I _

lemma szDir_ne_zero (t j : ℕ) : szDir t j ≠ 0 := by
  unfold szDir
  exact Complex.exp_ne_zero _

/-- The Szekeres point indexed by a binary vector `v : Fin t → Bool`. -/
noncomputable def szPoint (t : ℕ) (R : ℝ) (v : Fin t → Bool) : ℂ :=
  ∑ j : Fin t,
    ((if v j then 1 else 0 : ℂ)) * (R : ℂ) ^ (j : ℕ) * szDir t (j : ℕ)

/-- **Dominant-term decomposition.**  For `u ≠ v` the difference of Szekeres
points is a signed dominant term `σ · R^J · e^{iπJ/t}` times `1 + w` with
`‖w‖ ≤ t / R`, where `J` is the highest differing bit. -/
lemma szPoint_sub_decomp {t : ℕ} {R : ℝ} (hR : 1 ≤ R) {u v : Fin t → Bool}
    (huv : u ≠ v) :
    ∃ (J : Fin t) (σ w : ℂ), u J ≠ v J ∧
      σ = ((if v J then 1 else 0) - (if u J then 1 else 0) : ℂ) ∧
      (σ = 1 ∨ σ = -1) ∧
      ‖w‖ ≤ (t : ℝ) / R ∧
      szPoint t R v - szPoint t R u
        = σ * (R : ℂ) ^ (J : ℕ) * szDir t (J : ℕ) * (1 + w) := by
  classical
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR
  set D : Finset (Fin t) := Finset.univ.filter (fun j => u j ≠ v j) with hD
  have hDne : D.Nonempty := by
    rcases Function.ne_iff.mp huv with ⟨j, hj⟩
    exact ⟨j, by simp [hD, hj]⟩
  set J := D.max' hDne with hJdef
  have hJD : J ∈ D := D.max'_mem hDne
  have hJuv : u J ≠ v J := by simpa [hD] using hJD
  set f : Fin t → ℂ := fun j =>
    (((if v j then 1 else 0) - (if u j then 1 else 0) : ℂ))
      * (R : ℂ) ^ (j : ℕ) * szDir t (j : ℕ) with hf
  -- the difference is the sum of `f` over the differing indices
  have hsub : szPoint t R v - szPoint t R u = ∑ j ∈ D, f j := by
    have h1 : ∀ j ∈ Finset.univ, j ∉ D → f j = 0 := by
      intro j _ hj
      have huj : u j = v j := by
        by_contra hne
        exact hj (by simp [hD, hne])
      simp [hf, huj]
    calc szPoint t R v - szPoint t R u
        = ∑ j : Fin t, f j := by
          rw [szPoint, szPoint, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro j _
          simp only [hf]
          ring
      _ = ∑ j ∈ D, f j := (Finset.sum_subset (Finset.subset_univ D) h1).symm
  set σ : ℂ := ((if v J then 1 else 0) - (if u J then 1 else 0) : ℂ) with hσdef
  have hσ : σ = 1 ∨ σ = -1 := by
    rcases Bool.eq_false_or_eq_true (v J) with hv | hv <;>
      rcases Bool.eq_false_or_eq_true (u J) with hu | hu <;>
        simp_all
  have hσnorm : ‖σ‖ = 1 := by
    rcases hσ with h | h <;> simp [h]
  have hσ0 : σ ≠ 0 := by
    rcases hσ with h | h <;> simp [h]
  have hnormpow : ∀ k : ℕ, ‖(R : ℂ) ^ k‖ = R ^ k := by
    intro k
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0]
  have hfJ : f J = σ * (R : ℂ) ^ (J : ℕ) * szDir t (J : ℕ) := by
    simp only [hf, hσdef]
  have hcnorm : ‖f J‖ = R ^ (J : ℕ) := by
    rw [hfJ, norm_mul, norm_mul, hσnorm, hnormpow, norm_szDir]
    ring
  have hc0 : f J ≠ 0 := by
    intro h
    rw [h, norm_zero] at hcnorm
    have hpos : (0 : ℝ) < R ^ (J : ℕ) := pow_pos hR0 _
    rw [← hcnorm] at hpos
    exact lt_irrefl 0 hpos
  set rest : ℂ := ∑ j ∈ D.erase J, f j with hrest_def
  have hsplit : ∑ j ∈ D, f j = f J + rest := (Finset.add_sum_erase D f hJD).symm
  set w : ℂ := (f J)⁻¹ * rest with hwdef
  have hfactor : f J * (1 + w) = f J + rest := by
    rw [hwdef, mul_add, mul_one, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
  -- norm bound on the remainder
  have hcoef : ∀ j : Fin t,
      ‖((if v j then 1 else 0) - (if u j then 1 else 0) : ℂ)‖ ≤ 1 := by
    intro j
    rcases Bool.eq_false_or_eq_true (v j) with hv | hv <;>
      rcases Bool.eq_false_or_eq_true (u j) with hu | hu <;>
        simp [hv, hu]
  have hwnorm : ‖w‖ ≤ (t : ℝ) / R := by
    rcases Nat.eq_zero_or_pos (J : ℕ) with hJ0 | hJ0
    · -- highest bit is bit 0: no lower-order terms at all
      have herase : D.erase J = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro j hj
        have hjD : j ∈ D := Finset.mem_of_mem_erase hj
        have hjne : j ≠ J := Finset.ne_of_mem_erase hj
        have hle : j ≤ J := Finset.le_max' D j hjD
        have hlev : (j : ℕ) ≤ (J : ℕ) := Fin.le_def.mp hle
        have hval : (j : ℕ) = 0 := by omega
        exact hjne (Fin.ext (by omega))
      have hrz : rest = 0 := by rw [hrest_def, herase, Finset.sum_empty]
      rw [hwdef, hrz, mul_zero, norm_zero]
      positivity
    · have hbound : ∀ j ∈ D.erase J, ‖f j‖ ≤ R ^ ((J : ℕ) - 1) := by
        intro j hj
        have hjD : j ∈ D := Finset.mem_of_mem_erase hj
        have hjne : j ≠ J := Finset.ne_of_mem_erase hj
        have hle : j ≤ J := Finset.le_max' D j hjD
        have hjlt : (j : ℕ) < (J : ℕ) := by
          have hlev : (j : ℕ) ≤ (J : ℕ) := Fin.le_def.mp hle
          have hne : (j : ℕ) ≠ (J : ℕ) := fun h => hjne (Fin.ext h)
          omega
        have h1 : ‖f j‖ ≤ R ^ (j : ℕ) := by
          simp only [hf]
          rw [norm_mul, norm_mul, hnormpow, norm_szDir, mul_one]
          nlinarith [hcoef j,
            norm_nonneg (((if v j then 1 else 0) - (if u j then 1 else 0) : ℂ)),
            pow_pos hR0 (j : ℕ)]
        calc ‖f j‖ ≤ R ^ (j : ℕ) := h1
          _ ≤ R ^ ((J : ℕ) - 1) := by
              gcongr <;> first | exact hR | exact hR0.le | omega
      have hsum : ‖rest‖ ≤ ((D.erase J).card : ℝ) * R ^ ((J : ℕ) - 1) := by
        calc ‖rest‖ ≤ ∑ j ∈ D.erase J, ‖f j‖ := norm_sum_le _ _
          _ ≤ (D.erase J).card • (R ^ ((J : ℕ) - 1)) :=
              Finset.sum_le_card_nsmul _ _ _ hbound
          _ = ((D.erase J).card : ℝ) * R ^ ((J : ℕ) - 1) := by
              rw [nsmul_eq_mul]
      have hcard : ((D.erase J).card : ℝ) ≤ (t : ℝ) := by
        have h1 : (D.erase J).card ≤ Fintype.card (Fin t) :=
          Finset.card_le_univ _
        have h2 : Fintype.card (Fin t) = t := Fintype.card_fin t
        exact_mod_cast h1.trans_eq h2
      have hpow : R ^ (J : ℕ) = R ^ ((J : ℕ) - 1) * R := by
        rw [← pow_succ]
        congr 1
        omega
      have hRpow : (0 : ℝ) < R ^ ((J : ℕ) - 1) := pow_pos hR0 _
      have hrest2 : ‖rest‖ ≤ (t : ℝ) * R ^ ((J : ℕ) - 1) := by
        calc ‖rest‖ ≤ ((D.erase J).card : ℝ) * R ^ ((J : ℕ) - 1) := hsum
          _ ≤ (t : ℝ) * R ^ ((J : ℕ) - 1) := by nlinarith [hRpow]
      have hinv : (0 : ℝ) ≤ (R ^ (J : ℕ))⁻¹ := by positivity
      rw [hwdef, norm_mul, norm_inv, hcnorm]
      calc (R ^ (J : ℕ))⁻¹ * ‖rest‖
          ≤ (R ^ (J : ℕ))⁻¹ * ((t : ℝ) * R ^ ((J : ℕ) - 1)) := by
            nlinarith [norm_nonneg rest]
        _ = (t : ℝ) / R := by
            rw [hpow]
            field_simp
  refine ⟨J, σ, w, hJuv, rfl, hσ, hwnorm, ?_⟩
  rw [hsub, hsplit, ← hfactor, hfJ]

/-! ## M3d2: arguments of signed unit directions -/

lemma arg_exp_of_mem {φ : ℝ} (hφ : φ ∈ Set.Ioc (-π) π) :
    Complex.arg (Complex.exp ((φ : ℂ) * Complex.I)) = φ := by
  rw [Complex.exp_mul_I]
  exact Complex.arg_cos_add_sin_mul_I hφ

lemma neg_exp_eq (φ : ℝ) :
    -Complex.exp ((φ : ℂ) * Complex.I)
      = Complex.exp (((φ + π : ℝ) : ℂ) * Complex.I) := by
  have h : ((φ + π : ℝ) : ℂ) * Complex.I
      = (φ : ℂ) * Complex.I + (π : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_add, Complex.exp_pi_mul_I]
  ring

lemma abs_arg_neg_exp {φ : ℝ} (hlo : -π < φ) (hhi : φ < π) :
    |Complex.arg (-Complex.exp ((φ : ℂ) * Complex.I))| = π - |φ| := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  rcases lt_or_ge 0 φ with hφ | hφ
  · have hshift : -Complex.exp ((φ : ℂ) * Complex.I)
        = Complex.exp (((φ - π : ℝ) : ℂ) * Complex.I) := by
      rw [neg_exp_eq]
      have h2 : ((φ + π : ℝ) : ℂ) * Complex.I
          = ((φ - π : ℝ) : ℂ) * Complex.I
            + (π : ℂ) * Complex.I + (π : ℂ) * Complex.I := by
        push_cast
        ring
      rw [h2, Complex.exp_add, Complex.exp_add, Complex.exp_pi_mul_I]
      ring
    rw [hshift, arg_exp_of_mem ⟨by linarith, by linarith⟩,
      abs_of_neg (by linarith : φ - π < 0), abs_of_pos hφ]
    ring
  · rw [neg_exp_eq, arg_exp_of_mem ⟨by linarith, by linarith⟩,
      abs_of_pos (by linarith : (0 : ℝ) < φ + π), abs_of_nonpos hφ]
    ring

lemma conj_szDir_mul_szDir (t j k : ℕ) :
    conj (szDir t j) * szDir t k
      = Complex.exp (((Real.pi * k / t - Real.pi * j / t : ℝ) : ℂ)
          * Complex.I) := by
  unfold szDir
  have hconj : conj (Complex.exp (((Real.pi * j / t : ℝ) : ℂ) * Complex.I))
      = Complex.exp (-(((Real.pi * j / t : ℝ) : ℂ) * Complex.I)) := by
    rw [← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [hconj, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **Ideal angle bound.**  The angle between two signed sector directions
`σᵢ R^{Jᵢ} e^{iπJᵢ/t}` is at most `(1 - 1/t)·π`, provided the signs can
only disagree when the sectors differ. -/
lemma ideal_angle_le {t : ℕ} (ht : 0 < t) {R : ℝ} (hR : 1 ≤ R)
    {J₁ J₂ : Fin t} {σ₁ σ₂ : ℂ}
    (h₁ : σ₁ = 1 ∨ σ₁ = -1) (h₂ : σ₂ = 1 ∨ σ₂ = -1)
    (hJ : σ₁ * σ₂ = -1 → J₁ ≠ J₂) :
    InnerProductGeometry.angle
        (σ₁ * (R : ℂ) ^ (J₁ : ℕ) * szDir t (J₁ : ℕ))
        (σ₂ * (R : ℂ) ^ (J₂ : ℕ) * szDir t (J₂ : ℕ))
      ≤ (1 - 1 / (t : ℝ)) * π := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR
  have ht0 : (t : ℝ) ≠ 0 := by positivity
  have ht0' : (0 : ℝ) < t := by exact_mod_cast ht
  have hσ₁0 : σ₁ ≠ 0 := by rcases h₁ with h | h <;> simp [h]
  have hσ₂0 : σ₂ ≠ 0 := by rcases h₂ with h | h <;> simp [h]
  have hc₁ : σ₁ * (R : ℂ) ^ (J₁ : ℕ) * szDir t (J₁ : ℕ) ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero hσ₁0 _) (szDir_ne_zero t _)
    exact pow_ne_zero _ (by exact_mod_cast hR0.ne')
  have hc₂ : σ₂ * (R : ℂ) ^ (J₂ : ℕ) * szDir t (J₂ : ℕ) ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero hσ₂0 _) (szDir_ne_zero t _)
    exact pow_ne_zero _ (by exact_mod_cast hR0.ne')
  set φ : ℝ := Real.pi * (J₂ : ℕ) / t - Real.pi * (J₁ : ℕ) / t with hφdef
  -- bounds on φ
  have hJ₁t : ((J₁ : ℕ) : ℝ) ≤ (t : ℝ) - 1 := by
    have := J₁.isLt
    have h1 : (J₁ : ℕ) + 1 ≤ t := this
    have : (((J₁ : ℕ) + 1 : ℕ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast h1
    push_cast at this
    linarith
  have hJ₂t : ((J₂ : ℕ) : ℝ) ≤ (t : ℝ) - 1 := by
    have := J₂.isLt
    have h1 : (J₂ : ℕ) + 1 ≤ t := this
    have : (((J₂ : ℕ) + 1 : ℕ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast h1
    push_cast at this
    linarith
  have hJ₁0 : (0 : ℝ) ≤ ((J₁ : ℕ) : ℝ) := by positivity
  have hJ₂0 : (0 : ℝ) ≤ ((J₂ : ℕ) : ℝ) := by positivity
  have hpt : (0 : ℝ) < Real.pi / t := by positivity
  have hφeq : φ = Real.pi / (t : ℝ) * (((J₂ : ℕ) : ℝ) - ((J₁ : ℕ) : ℝ)) := by
    rw [hφdef]
    ring
  have hkey2 : (1 - 1 / (t : ℝ)) * π
      = Real.pi / (t : ℝ) * ((t : ℝ) - 1) := by
    field_simp <;> ring
  have hφub : φ ≤ (1 - 1 / (t : ℝ)) * π := by
    rw [hφeq, hkey2]
    nlinarith [mul_nonneg hpt.le (by linarith :
      (0 : ℝ) ≤ ((t : ℝ) - 1) - (((J₂ : ℕ) : ℝ) - ((J₁ : ℕ) : ℝ)))]
  have hφlb : -((1 - 1 / (t : ℝ)) * π) ≤ φ := by
    rw [hφeq, hkey2]
    nlinarith [mul_nonneg hpt.le (by linarith :
      (0 : ℝ) ≤ (((J₂ : ℕ) : ℝ) - ((J₁ : ℕ) : ℝ)) + ((t : ℝ) - 1))]
  have hfrac : (1 - 1 / (t : ℝ)) * π < π := by
    have h1 : (0 : ℝ) < 1 / (t : ℝ) := by positivity
    nlinarith
  have hφlo : -π < φ := by linarith
  have hφhi : φ < π := by linarith
  -- reduce the angle to `|arg (σ₁ σ₂ · e^{iφ})|`
  rw [angle_eq_abs_arg hc₁ hc₂]
  have hconjσ : conj σ₁ = σ₁ := by rcases h₁ with h | h <;> simp [h]
  have hgather : conj (σ₁ * (R : ℂ) ^ (J₁ : ℕ) * szDir t (J₁ : ℕ))
      * (σ₂ * (R : ℂ) ^ (J₂ : ℕ) * szDir t (J₂ : ℕ))
      = ((R ^ (J₁ : ℕ) * R ^ (J₂ : ℕ) : ℝ) : ℂ)
        * ((σ₁ * σ₂) * Complex.exp ((φ : ℂ) * Complex.I)) := by
    rw [map_mul, map_mul, hconjσ, map_pow, Complex.conj_ofReal]
    have h1 : conj (szDir t (J₁ : ℕ)) * szDir t (J₂ : ℕ)
        = Complex.exp ((φ : ℂ) * Complex.I) := by
      rw [conj_szDir_mul_szDir]
    rw [← h1]
    push_cast
    ring
  rw [hgather, Complex.arg_real_mul _ (by positivity)]
  have hprod : σ₁ * σ₂ = 1 ∨ σ₁ * σ₂ = -1 := by
    rcases h₁ with h | h <;> rcases h₂ with h' | h' <;> simp [h, h']
  rcases hprod with hp | hp
  · rw [hp, one_mul, arg_exp_of_mem ⟨hφlo, hφhi.le⟩]
    rw [abs_le]
    exact ⟨hφlb, hφub⟩
  · rw [hp]
    have hneg : (-1 : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)
        = -Complex.exp ((φ : ℂ) * Complex.I) := by ring
    rw [hneg, abs_arg_neg_exp hφlo hφhi]
    -- the sectors differ, so `|φ| ≥ π / t`
    have hJne : J₁ ≠ J₂ := hJ hp
    have hvalne : ((J₁ : ℕ) : ℝ) ≠ ((J₂ : ℕ) : ℝ) := by
      intro h
      have : (J₁ : ℕ) = (J₂ : ℕ) := by exact_mod_cast h
      exact hJne (Fin.ext this)
    have hgap : 1 ≤ |((J₂ : ℕ) : ℝ) - ((J₁ : ℕ) : ℝ)| := by
      rcases lt_or_gt_of_ne hvalne with h | h
      · have h1 : (J₁ : ℕ) < (J₂ : ℕ) := by exact_mod_cast h
        have h2 : (J₁ : ℕ) + 1 ≤ (J₂ : ℕ) := h1
        have h3 : (((J₁ : ℕ) + 1 : ℕ) : ℝ) ≤ ((J₂ : ℕ) : ℝ) := by
          exact_mod_cast h2
        push_cast at h3
        rw [abs_of_pos (by linarith)]
        linarith
      · have h1 : (J₂ : ℕ) < (J₁ : ℕ) := by exact_mod_cast h
        have h2 : (J₂ : ℕ) + 1 ≤ (J₁ : ℕ) := h1
        have h3 : (((J₂ : ℕ) + 1 : ℕ) : ℝ) ≤ ((J₁ : ℕ) : ℝ) := by
          exact_mod_cast h2
        push_cast at h3
        rw [abs_of_neg (by linarith)]
        linarith
    have hφgap : π / t ≤ |φ| := by
      rw [hφeq, abs_mul, abs_of_pos hpt]
      nlinarith [mul_nonneg hpt.le (by linarith :
        (0 : ℝ) ≤ |((J₂ : ℕ) : ℝ) - ((J₁ : ℕ) : ℝ)| - 1)]
    have hgoal : π - π / (t : ℝ) = (1 - 1 / (t : ℝ)) * π := by
      ring
    linarith

/-! ## M3d3: the final assembly -/

/-- For `R` large enough that `t / R < 1`, distinct binary vectors give
distinct Szekeres points. -/
lemma szPoint_injective {t : ℕ} {R : ℝ} (hR : 1 ≤ R) (hRt : (t : ℝ) / R < 1) :
    Function.Injective (szPoint t R) := by
  intro u v huv
  by_contra hne
  obtain ⟨J, σ, w, -, -, hσ, hw, hdec⟩ := szPoint_sub_decomp hR hne
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR
  have hσ0 : σ ≠ 0 := by rcases hσ with h | h <;> simp [h]
  have hpow : ((R : ℂ)) ^ (J : ℕ) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast hR0.ne')
  have hw1 : ‖w‖ < 1 := lt_of_le_of_lt hw hRt
  have hne0 : szPoint t R v - szPoint t R u ≠ 0 := by
    rw [hdec]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hσ0 hpow) (szDir_ne_zero t _))
      (one_add_ne_zero_of_norm_lt_one hw1)
  exact hne0 (by rw [huv]; ring)

/-- **Erdős–Szekeres (1960) upper bound.**  For every `t ≥ 1` and every
`ε > 0` there is a configuration of `2 ^ t` points in the plane all of whose
angles are smaller than `(1 - 1/t) · π + ε`. -/
theorem exists_config_angle_lt {t : ℕ} (ht : 0 < t) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset ℂ, S.card = 2 ^ t ∧
      ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
        EuclideanGeometry.angle p q r < (1 - 1 / (t : ℝ)) * π + ε := by
  classical
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  set d : ℝ := min (1 / 2 : ℝ) (ε / 8) with hd_def
  have hd0 : 0 < d := lt_min (by norm_num) (by linarith)
  have hd_half : d ≤ 1 / 2 := min_le_left _ _
  have hd_eps : d ≤ ε / 8 := min_le_right _ _
  have hd1 : d < 1 := by linarith
  set R : ℝ := (t : ℝ) / d with hR_def
  have hR0 : (0 : ℝ) < R := div_pos ht' hd0
  have hR1 : (1 : ℝ) ≤ R := by
    have hdt : d ≤ (t : ℝ) := by linarith
    calc (1 : ℝ) = d / d := by field_simp
      _ ≤ (t : ℝ) / d := by gcongr
  have hRt : (t : ℝ) / R = d := by
    rw [hR_def]
    field_simp
  have hRt1 : (t : ℝ) / R < 1 := by rw [hRt]; exact hd1
  have hinj : Function.Injective (szPoint t R) := szPoint_injective hR1 hRt1
  -- the numeric slack
  have hdd : d / (1 - d) ≤ 2 * d := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - d)]
    nlinarith
  have hslack : 2 * (d / (1 - d)) < ε := by linarith
  refine ⟨Finset.univ.image (szPoint t R), ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
    simp
  · intro p hp q hq r hr hpq hrq
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hp hq hr
    obtain ⟨u, rfl⟩ := hp
    obtain ⟨v, rfl⟩ := hq
    obtain ⟨w', rfl⟩ := hr
    have hvu : v ≠ u := fun h => hpq (by rw [h])
    have hvw : v ≠ w' := fun h => hrq (by rw [h])
    obtain ⟨J₁, σ₁, w₁, hJ₁ne, hσ₁eq, hσ₁, hw₁, hdec₁⟩ :=
      szPoint_sub_decomp hR1 hvu
    obtain ⟨J₂, σ₂, w₂, hJ₂ne, hσ₂eq, hσ₂, hw₂, hdec₂⟩ :=
      szPoint_sub_decomp hR1 hvw
    have hw₁' : ‖w₁‖ ≤ d := by rw [← hRt]; exact hw₁
    have hw₂' : ‖w₂‖ ≤ d := by rw [← hRt]; exact hw₂
    have hσ₁0 : σ₁ ≠ 0 := by rcases hσ₁ with h | h <;> simp [h]
    have hσ₂0 : σ₂ ≠ 0 := by rcases hσ₂ with h | h <;> simp [h]
    have hpowne : ∀ J : ℕ, ((R : ℂ)) ^ J ≠ 0 := fun J =>
      pow_ne_zero _ (by exact_mod_cast hR0.ne')
    have hc₁ : σ₁ * (R : ℂ) ^ (J₁ : ℕ) * szDir t (J₁ : ℕ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hσ₁0 (hpowne _)) (szDir_ne_zero t _)
    have hc₂ : σ₂ * (R : ℂ) ^ (J₂ : ℕ) * szDir t (J₂ : ℕ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hσ₂0 (hpowne _)) (szDir_ne_zero t _)
    -- opposite signs force distinct dominant directions
    have hbool : ∀ a b c : Bool, a ≠ b → a ≠ c → b = c := by decide
    have hJ : σ₁ * σ₂ = -1 → J₁ ≠ J₂ := by
      intro hprod hJeq
      have hJ₂ne' : v J₁ ≠ w' J₁ := by rw [hJeq]; exact hJ₂ne
      have huw : u J₁ = w' J₁ := hbool _ _ _ hJ₁ne hJ₂ne'
      have hσeq : σ₁ = σ₂ := by rw [hσ₁eq, hσ₂eq, ← hJeq, huw]
      rw [← hσeq] at hprod
      rcases hσ₁ with h | h <;> rw [h] at hprod <;> norm_num at hprod
    have hbridge : EuclideanGeometry.angle (szPoint t R u) (szPoint t R v)
          (szPoint t R w')
        = InnerProductGeometry.angle (szPoint t R u - szPoint t R v)
            (szPoint t R w' - szPoint t R v) := by
      simp [EuclideanGeometry.angle, vsub_eq_sub]
    rw [hbridge, hdec₁, hdec₂]
    have hperturb := angle_perturb_le hc₁ hc₂ hd1 hw₁' hw₂'
    have hideal := ideal_angle_le ht hR1 hσ₁ hσ₂ hJ
    linarith

end Erdos504
