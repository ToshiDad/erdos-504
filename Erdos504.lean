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

/-! ## M4a: rigidity of the colouring at N = 2^n -/

/-- When `Fintype.card V = 2 ^ n`, the side-vector map `v ↦ (i ↦ side i v)` of a
colouring is not merely injective (as in `card_le_two_pow_of_side`) but
bijective, since `Fin n → Bool` also has `2 ^ n` elements. -/
theorem sideVector_bijective {V : Type*} [Fintype V] {n : ℕ}
    (color : V → V → Fin n) (side : Fin n → V → Bool)
    (hside : ∀ u v : V, u ≠ v → side (color u v) u ≠ side (color u v) v)
    (hcard : Fintype.card V = 2 ^ n) :
    Function.Bijective (fun (v : V) (i : Fin n) => side i v) := by
  have hinj : Function.Injective (fun (v : V) (i : Fin n) => side i v) := by
    intro u v huv
    by_contra hne
    exact hside u v hne (by simpa using congrFun huv (color u v))
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, ?_⟩
  simp [hcard]

/-- Every prescribed side vector is realised by some vertex when
`Fintype.card V = 2 ^ n`. -/
theorem exists_side_eq {V : Type*} [Fintype V] {n : ℕ}
    (color : V → V → Fin n) (side : Fin n → V → Bool)
    (hside : ∀ u v : V, u ≠ v → side (color u v) u ≠ side (color u v) v)
    (hcard : Fintype.card V = 2 ^ n) (b : Fin n → Bool) :
    ∃ u : V, ∀ j : Fin n, side j u = b j := by
  obtain ⟨-, hsurj⟩ := sideVector_bijective color side hside hcard
  obtain ⟨u, hu⟩ := hsurj b
  exact ⟨u, fun j => congrFun hu j⟩

/-- If the side vectors of `u` and `v` agree off the single coordinate `i`,
then the colour of the edge `u v` must be `i`. -/
theorem color_eq_of_agree_off_one {V : Type*} {n : ℕ}
    (color : V → V → Fin n) (side : Fin n → V → Bool)
    (hside : ∀ u v : V, u ≠ v → side (color u v) u ≠ side (color u v) v)
    {u v : V} (huv : u ≠ v) {i : Fin n}
    (h : ∀ j : Fin n, j ≠ i → side j u = side j v) : color u v = i := by
  by_contra hc
  exact hside u v huv (h _ hc)

/-- If the side vectors of `u` and `v` agree off the two coordinates `i`, `i'`,
then the colour of the edge `u v` is one of them. -/
theorem color_mem_of_agree_off_two {V : Type*} {n : ℕ}
    (color : V → V → Fin n) (side : Fin n → V → Bool)
    (hside : ∀ u v : V, u ≠ v → side (color u v) u ≠ side (color u v) v)
    {u v : V} (huv : u ≠ v) {i i' : Fin n}
    (h : ∀ j : Fin n, j ≠ i → j ≠ i' → side j u = side j v) :
    color u v = i ∨ color u v = i' := by
  by_contra hc
  rw [not_or] at hc
  exact hside u v huv (h _ hc.1 hc.2)

/-- **Rigidity, first form.**  At the extremal cardinality `2 ^ n`, every
vertex `v` and every colour `i` occur together: some edge at `v` has colour
`i`.  (Replaces Lemma 3.1 of Erdős–Szekeres 1960.) -/
theorem exists_edge_of_card_eq {V : Type*} [Fintype V] {n : ℕ}
    (color : V → V → Fin n) (side : Fin n → V → Bool)
    (hside : ∀ u v : V, u ≠ v → side (color u v) u ≠ side (color u v) v)
    (hcard : Fintype.card V = 2 ^ n) (v : V) (i : Fin n) :
    ∃ u : V, u ≠ v ∧ color u v = i := by
  obtain ⟨u, hu⟩ := exists_side_eq color side hside hcard
    (Function.update (fun j : Fin n => side j v) i (!(side i v)))
  have hui : side i u = !(side i v) := by
    rw [hu i, Function.update_self]
  have hoff : ∀ j : Fin n, j ≠ i → side j u = side j v := by
    intro j hj
    rw [hu j, Function.update_of_ne hj]
  have huv : u ≠ v := by
    intro h
    rw [h] at hui
    exact Bool.not_ne_self (side i v) hui.symm
  exact ⟨u, huv, color_eq_of_agree_off_one color side hside huv hoff⟩

/-- **Rigidity, second form.**  At the extremal cardinality `2 ^ n`, for any two
distinct colours `i ≠ i'` and any vertex `v`, at least three edges at `v` carry
a colour in `{i, i'}`.  (Replaces Lemma 3 (case `i = 2`) of
Erdős–Szekeres 1960.) -/
theorem three_le_card_edges_of_card_eq {V : Type*} [Fintype V] {n : ℕ}
    [DecidableEq V]
    (color : V → V → Fin n) (side : Fin n → V → Bool)
    (hside : ∀ u v : V, u ≠ v → side (color u v) u ≠ side (color u v) v)
    (hcard : Fintype.card V = 2 ^ n) (v : V) {i i' : Fin n} (hii : i ≠ i') :
    3 ≤ (Finset.univ.filter
      (fun u => u ≠ v ∧ (color u v = i ∨ color u v = i'))).card := by
  -- three vertices whose side vectors differ from that of `v` in the
  -- coordinate `i`, in the coordinate `i'`, and in both, respectively
  obtain ⟨u₁, h1⟩ := exists_side_eq color side hside hcard
    (Function.update (fun j : Fin n => side j v) i (!(side i v)))
  obtain ⟨u₂, h2⟩ := exists_side_eq color side hside hcard
    (Function.update (fun j : Fin n => side j v) i' (!(side i' v)))
  obtain ⟨u₃, h3⟩ := exists_side_eq color side hside hcard
    (Function.update (Function.update (fun j : Fin n => side j v) i (!(side i v)))
      i' (!(side i' v)))
  have hii' : i' ≠ i := hii.symm
  -- coordinatewise evaluations
  have h1i : side i u₁ = !(side i v) := by rw [h1 i, Function.update_self]
  have h1i' : side i' u₁ = side i' v := by
    rw [h1 i', Function.update_of_ne hii']
  have h1off : ∀ j : Fin n, j ≠ i → side j u₁ = side j v := by
    intro j hj; rw [h1 j, Function.update_of_ne hj]
  have h2i' : side i' u₂ = !(side i' v) := by rw [h2 i', Function.update_self]
  have h2i : side i u₂ = side i v := by rw [h2 i, Function.update_of_ne hii]
  have h2off : ∀ j : Fin n, j ≠ i' → side j u₂ = side j v := by
    intro j hj; rw [h2 j, Function.update_of_ne hj]
  have h3i' : side i' u₃ = !(side i' v) := by rw [h3 i', Function.update_self]
  have h3i : side i u₃ = !(side i v) := by
    rw [h3 i, Function.update_of_ne hii, Function.update_self]
  have h3off : ∀ j : Fin n, j ≠ i → j ≠ i' → side j u₃ = side j v := by
    intro j hj hj'
    rw [h3 j, Function.update_of_ne hj', Function.update_of_ne hj]
  -- each of them is distinct from `v`
  have h1v : u₁ ≠ v := by
    intro h; rw [h] at h1i; exact Bool.not_ne_self (side i v) h1i.symm
  have h2v : u₂ ≠ v := by
    intro h; rw [h] at h2i'; exact Bool.not_ne_self (side i' v) h2i'.symm
  have h3v : u₃ ≠ v := by
    intro h; rw [h] at h3i'; exact Bool.not_ne_self (side i' v) h3i'.symm
  -- their colours
  have hc₁ : color u₁ v = i := color_eq_of_agree_off_one color side hside h1v h1off
  have hc₂ : color u₂ v = i' := color_eq_of_agree_off_one color side hside h2v h2off
  have hc₃ : color u₃ v = i ∨ color u₃ v = i' :=
    color_mem_of_agree_off_two color side hside h3v h3off
  -- they are pairwise distinct
  have h12 : u₁ ≠ u₂ := by
    intro h
    rw [h, hc₂] at hc₁
    exact hii hc₁.symm
  have h13 : u₁ ≠ u₃ := by
    intro h
    have hx : side i' u₁ = side i' u₃ := by rw [h]
    rw [h1i', h3i'] at hx
    exact Bool.not_ne_self (side i' v) hx.symm
  have h23 : u₂ ≠ u₃ := by
    intro h
    have hx : side i u₂ = side i u₃ := by rw [h]
    rw [h2i, h3i] at hx
    exact Bool.not_ne_self (side i v) hx.symm
  have hsub : ({u₁, u₂, u₃} : Finset V) ⊆ Finset.univ.filter
      (fun u => u ≠ v ∧ (color u v = i ∨ color u v = i')) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · exact ⟨h1v, Or.inl hc₁⟩
    · exact ⟨h2v, Or.inr hc₂⟩
    · exact ⟨h3v, hc₃⟩
  have hcard3 : ({u₁, u₂, u₃} : Finset V).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [h12, h13]),
      Finset.card_insert_of_notMem (by simp [h23]), Finset.card_singleton]
  calc (3 : ℕ) = ({u₁, u₂, u₃} : Finset V).card := hcard3.symm
    _ ≤ _ := Finset.card_le_card hsub

/-! ## M4b: the empty-sector argument -/

/-- **Rigidity in geometric form.**  If a set of exactly `2 ^ n` points has all
its angles bounded by `(1 - 1/n) · π`, then at every point `p` of the set and in
every sector `i` there is an edge of `S` at `p` with that direction index. -/
theorem exists_dir_edge_of_angle_le {n : ℕ} (hn : 0 < n) (S : Finset ℂ)
    (hcard : S.card = 2 ^ n)
    (hangle : ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
      EuclideanGeometry.angle p q r ≤ (1 - 1 / (n : ℝ)) * π)
    {p : ℂ} (hp : p ∈ S) (i : Fin n) :
    ∃ q ∈ S, q ≠ p ∧ dirIndex n (q - p) = (i : ℕ) := by
  classical
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
  have hside : ∀ u v : {x // x ∈ S}, u ≠ v →
      (decide (∃ w : {x // x ∈ S}, (w : ℂ) ≠ (u : ℂ) ∧
          IsPos ((w : ℂ) - (u : ℂ)) ∧
          dirIndex n ((w : ℂ) - (u : ℂ)) = dirIndex n ((v : ℂ) - (u : ℂ))))
        ≠ (decide (∃ w : {x // x ∈ S}, (w : ℂ) ≠ (v : ℂ) ∧
          IsPos ((w : ℂ) - (v : ℂ)) ∧
          dirIndex n ((w : ℂ) - (v : ℂ)) = dirIndex n ((v : ℂ) - (u : ℂ)))) := by
    intro u v huv
    have huv' : (u : ℂ) ≠ (v : ℂ) := fun h => huv (Subtype.ext h)
    have hz : (v : ℂ) - (u : ℂ) ≠ 0 := sub_ne_zero.mpr huv'.symm
    have hdi : dirIndex n ((u : ℂ) - (v : ℂ))
        = dirIndex n ((v : ℂ) - (u : ℂ)) := by
      rw [show ((u : ℂ) - (v : ℂ)) = -((v : ℂ) - (u : ℂ)) by ring, dirIndex_neg]
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
      rw [decide_eq_true hPu, decide_eq_false hPv]
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
      rw [decide_eq_false hPu, decide_eq_true hPv]
      simp
  have hcard' : Fintype.card {x // x ∈ S} = 2 ^ n := by
    rw [Fintype.card_coe]; exact hcard
  obtain ⟨u, hune, hcolor⟩ := exists_edge_of_card_eq
    (fun u v : {x // x ∈ S} =>
      (⟨dirIndex n ((v : ℂ) - (u : ℂ)), dirIndex_lt hn _⟩ : Fin n))
    (fun (j : Fin n) (v : {x // x ∈ S}) => decide (∃ w : {x // x ∈ S},
      (w : ℂ) ≠ (v : ℂ) ∧ IsPos ((w : ℂ) - (v : ℂ)) ∧
        dirIndex n ((w : ℂ) - (v : ℂ)) = (j : ℕ)))
    hside hcard' ⟨p, hp⟩ i
  have hval : dirIndex n (p - (u : ℂ)) = (i : ℕ) := congrArg Fin.val hcolor
  refine ⟨(u : ℂ), u.2, fun h => hune (Subtype.ext h), ?_⟩
  rw [show ((u : ℂ) - p) = -(p - (u : ℂ)) by ring, dirIndex_neg]
  exact hval

/-- A direction whose argument is nonnegative and bounded by some
`A < (1 - 1/n) · π` cannot lie in the top sector. -/
lemma dirIndex_ne_last_of_arg_le {n : ℕ} (hn : 0 < n) {z : ℂ} {A : ℝ}
    (hA : A < (1 - 1 / (n : ℝ)) * π)
    (h0 : 0 ≤ Complex.arg z) (hA' : Complex.arg z ≤ A) :
    dirIndex n z ≠ n - 1 := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · -- `n = 1`: the bound `A` is negative, contradicting `0 ≤ arg z ≤ A`.
    have hn1 : n = 1 := by omega
    subst hn1
    have hzero : (1 - 1 / ((1 : ℕ) : ℝ)) * π = 0 := by norm_num
    rw [hzero] at hA
    linarith
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hn'
    have hone : (0 : ℝ) < 1 / (n : ℝ) := by positivity
    have harg : Complex.arg z < (1 - 1 / (n : ℝ)) * π := lt_of_le_of_lt hA' hA
    have hprod : (0 : ℝ) < (1 / (n : ℝ)) * π := mul_pos hone hπ
    have harglt : Complex.arg z < π := by nlinarith [harg, hprod]
    have hpos : IsPos z := ⟨h0, harglt⟩
    have hmul : (n : ℝ) * Complex.arg z
        < (n : ℝ) * ((1 - 1 / (n : ℝ)) * π) :=
      mul_lt_mul_of_pos_left harg hn'
    have hexp : (n : ℝ) * ((1 - 1 / (n : ℝ)) * π) = ((n : ℝ) - 1) * π := by
      field_simp
    rw [hexp] at hmul
    have hlt : (n : ℝ) * (Complex.arg z / π) < (n : ℝ) - 1 := by
      rw [← mul_div_assoc, div_lt_iff₀ hπ]
      linarith
    have hfr : Int.fract (Complex.arg z / π) = Complex.arg z / π :=
      fract_eq_self_of_isPos hpos
    have hfl : ⌊(n : ℝ) * Int.fract (Complex.arg z / π)⌋ < (n : ℤ) - 1 := by
      apply Int.floor_lt.mpr
      rw [hfr]
      push_cast
      linarith
    unfold dirIndex
    omega

/-- **The empty-sector argument** (Case 1 of Erdős–Szekeres 1960, in a form
free of any cyclic ordering).  At the extremal cardinality `2 ^ n`, no point of
`S` can see all the other points inside a cone of opening `< (1 - 1/n) · π`
starting at direction `0`. -/
theorem no_small_cone {n : ℕ} (hn : 0 < n) {S : Finset ℂ}
    (hcard : S.card = 2 ^ n)
    (hangle : ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
      EuclideanGeometry.angle p q r ≤ (1 - 1 / (n : ℝ)) * π)
    {p : ℂ} (hp : p ∈ S) {A : ℝ} (hA : A < (1 - 1 / (n : ℝ)) * π)
    (hdir : ∀ q ∈ S, q ≠ p →
      0 ≤ Complex.arg (q - p) ∧ Complex.arg (q - p) ≤ A) :
    False := by
  obtain ⟨q, hq, hqp, hqi⟩ :=
    exists_dir_edge_of_angle_le hn S hcard hangle hp ⟨n - 1, by omega⟩
  obtain ⟨h0, hle⟩ := hdir q hq hqp
  exact dirIndex_ne_last_of_arg_le hn hA h0 hle hqi

/-- The Euclidean angle at a vertex is invariant under multiplication of all
three points by a nonzero complex number (a spiral similarity of the plane). -/
lemma euclidean_angle_const_mul {c : ℂ} (hc : c ≠ 0) (p q r : ℂ) :
    EuclideanGeometry.angle (c * p) (c * q) (c * r)
      = EuclideanGeometry.angle p q r := by
  have hbridge : ∀ a b d : ℂ, EuclideanGeometry.angle a b d
      = InnerProductGeometry.angle (a - b) (d - b) := by
    intro a b d
    simp [EuclideanGeometry.angle, vsub_eq_sub]
  rw [hbridge, hbridge, ← mul_sub, ← mul_sub]
  rcases eq_or_ne (p - q) 0 with h | h
  · rw [h, mul_zero]
    simp
  rcases eq_or_ne (r - q) 0 with h' | h'
  · rw [h', mul_zero]
    simp
  exact angle_const_mul hc h h'

/-! ## M4c0: collinear triples and interior points of triangles -/

/-- Three distinct collinear points always determine a straight angle: one of
them lies strictly between the other two. -/
theorem exists_angle_eq_pi_of_collinear {a b c : ℂ} (hab : a ≠ b)
    (hbc : b ≠ c) (hac : a ≠ c)
    (h : Collinear ℝ ({a, b, c} : Set ℂ)) :
    EuclideanGeometry.angle a b c = π ∨ EuclideanGeometry.angle b a c = π ∨
      EuclideanGeometry.angle a c b = π := by
  rcases h.wbtw_or_wbtw_or_wbtw with hw | hw | hw
  · -- `b` lies between `a` and `c`
    exact Or.inl (Sbtw.angle₁₂₃_eq_pi ⟨hw, hab.symm, hbc⟩)
  · -- `c` lies between `b` and `a`
    refine Or.inr (Or.inr ?_)
    have h' : EuclideanGeometry.angle b c a = π :=
      Sbtw.angle₁₂₃_eq_pi ⟨hw, hbc.symm, hac.symm⟩
    rwa [EuclideanGeometry.angle_comm] at h'
  · -- `a` lies between `c` and `b`
    refine Or.inr (Or.inl ?_)
    have h' : EuclideanGeometry.angle c a b = π :=
      Sbtw.angle₁₂₃_eq_pi ⟨hw, hac, hab⟩
    rwa [EuclideanGeometry.angle_comm] at h'

/-- **An interior point of a triangle sees the opposite side under a strictly
larger angle than the vertex does.**  Here `x = α·a + β·b + γ·c` with positive
barycentric coordinates summing to `1`. -/
theorem angle_lt_angle_of_interior {a b c x : ℂ} {α β γ : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hsum : α + β + γ = 1)
    (hx : x = α • a + β • b + γ • c)
    (hnc : ¬ Collinear ℝ ({a, b, c} : Set ℂ)) :
    EuclideanGeometry.angle a b c < EuclideanGeometry.angle a x c := by
  have hβeq : β = 1 - α - γ := by linarith
  subst hβeq
  have hαγ : (0 : ℝ) < α + γ := by linarith
  have hαγne : α + γ ≠ 0 := ne_of_gt hαγ
  have hab : a ≠ b := ne₁₂_of_not_collinear hnc
  have hacne : a ≠ c := ne₁₃_of_not_collinear hnc
  have hbcne : b ≠ c := ne₂₃_of_not_collinear hnc
  have hαC : ((α : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hα)
  have hβC : (((1 - α - γ : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hβ)
  have hγC : ((γ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hγ)
  have hαγC : ((α : ℝ) : ℂ) + ((γ : ℝ) : ℂ) ≠ 0 := by
    have h := Complex.ofReal_ne_zero.mpr hαγne
    push_cast at h
    exact h
  -- `d` is the point where the ray `b → x` meets the side `a c`
  obtain ⟨d, hd_def⟩ : ∃ d : ℂ, d = (α / (α + γ) : ℝ) • a + (γ / (α + γ) : ℝ) • c :=
    ⟨_, rfl⟩
  have hwad : Wbtw ℝ a d c := by
    rw [← mem_segment_iff_wbtw]
    exact ⟨α / (α + γ), γ / (α + γ), by positivity, by positivity, by field_simp,
      hd_def.symm⟩
  have hbd : b ≠ d := by
    intro h
    exact hnc (by rw [h]; exact hwad.collinear)
  -- the four elementary difference identities
  have hdiff_da : d - a
      = ((γ : ℝ) : ℂ) * (c - a) / (((α : ℝ) : ℂ) + ((γ : ℝ) : ℂ)) := by
    rw [hd_def]; simp only [Complex.real_smul]; push_cast; field_simp; ring
  have hdiff_dc : d - c
      = ((α : ℝ) : ℂ) * (a - c) / (((α : ℝ) : ℂ) + ((γ : ℝ) : ℂ)) := by
    rw [hd_def]; simp only [Complex.real_smul]; push_cast; field_simp; ring
  have hdiff_xb : x - b = (((α : ℝ) : ℂ) + ((γ : ℝ) : ℂ)) * (d - b) := by
    rw [hx, hd_def]; simp only [Complex.real_smul]; push_cast; field_simp; ring
  have hdiff_xd : x - d = (((1 - α - γ : ℝ)) : ℂ) * (b - d) := by
    rw [hx, hd_def]; simp only [Complex.real_smul]; push_cast; field_simp; ring
  have hdane : d ≠ a := by
    rw [← sub_ne_zero, hdiff_da]
    exact div_ne_zero (mul_ne_zero hγC (sub_ne_zero.mpr hacne.symm)) hαγC
  have hdcne : d ≠ c := by
    rw [← sub_ne_zero, hdiff_dc]
    exact div_ne_zero (mul_ne_zero hαC (sub_ne_zero.mpr hacne)) hαγC
  have hxbne : x ≠ b := by
    rw [← sub_ne_zero, hdiff_xb]
    exact mul_ne_zero hαγC (sub_ne_zero.mpr (Ne.symm hbd))
  have hxdne : x ≠ d := by
    rw [← sub_ne_zero, hdiff_xd]
    exact mul_ne_zero hβC (sub_ne_zero.mpr hbd)
  have hwbxd : Wbtw ℝ b x d := by
    rw [← mem_segment_iff_wbtw]
    refine ⟨1 - α - γ, α + γ, by linarith, by linarith, by ring, ?_⟩
    rw [hx, hd_def]; simp only [Complex.real_smul]; push_cast; field_simp; ring
  have hsad : Sbtw ℝ a d c := ⟨hwad, hdane, hdcne⟩
  have hsbxd : Sbtw ℝ b x d := ⟨hwbxd, hxbne, hxdne⟩
  -- splitting the angle at `x` by the ray `x → d`
  have hsplitx : EuclideanGeometry.angle a x d + EuclideanGeometry.angle d x c
      = EuclideanGeometry.angle a x c :=
    EuclideanGeometry.angle_add_angle_eq_of_sbtw hsad
  -- the exterior angle theorem in the triangles `a b x` and `c b x`
  have hext1 : EuclideanGeometry.angle a x d
      = EuclideanGeometry.angle x a b + EuclideanGeometry.angle a b x :=
    EuclideanGeometry.exterior_angle_eq_angle_add_angle d hsbxd.symm
  have hext2 : EuclideanGeometry.angle c x d
      = EuclideanGeometry.angle x c b + EuclideanGeometry.angle c b x :=
    EuclideanGeometry.exterior_angle_eq_angle_add_angle d hsbxd.symm
  have hcomm1 : EuclideanGeometry.angle d x c = EuclideanGeometry.angle c x d :=
    EuclideanGeometry.angle_comm d x c
  -- `x` and `d` lie on the same ray from `b`
  have hray1 : EuclideanGeometry.angle a b x = EuclideanGeometry.angle a b d :=
    Sbtw.angle_eq_right a hsbxd
  have hray2 : EuclideanGeometry.angle c b x = EuclideanGeometry.angle c b d :=
    Sbtw.angle_eq_right c hsbxd
  -- splitting the angle at `b` by the ray `b → d`
  have hsplitb : EuclideanGeometry.angle a b d + EuclideanGeometry.angle d b c
      = EuclideanGeometry.angle a b c :=
    EuclideanGeometry.angle_add_of_ne_of_ne hab.symm hbcne hwad
  have hcomm2 : EuclideanGeometry.angle d b c = EuclideanGeometry.angle c b d :=
    EuclideanGeometry.angle_comm d b c
  -- the two remote interior angles cannot both vanish
  have hpos : 0 < EuclideanGeometry.angle x a b + EuclideanGeometry.angle x c b := by
    rcases lt_or_eq_of_le (EuclideanGeometry.angle_nonneg x a b) with h | h
    · linarith [EuclideanGeometry.angle_nonneg x c b]
    rcases lt_or_eq_of_le (EuclideanGeometry.angle_nonneg x c b) with h' | h'
    · linarith
    exfalso
    apply hnc
    have hca : Collinear ℝ ({x, a, b} : Set ℂ) :=
      EuclideanGeometry.collinear_of_angle_eq_zero h.symm
    have hcc : Collinear ℝ ({x, c, b} : Set ℂ) :=
      EuclideanGeometry.collinear_of_angle_eq_zero h'.symm
    have hbx : b ≠ x := Ne.symm hxbne
    have hA : a ∈ line[ℝ, b, x] :=
      hca.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hbx
    have hC : c ∈ line[ℝ, b, x] :=
      hcc.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hbx
    have hB : b ∈ line[ℝ, b, x] := left_mem_affineSpan_pair ℝ b x
    exact collinear_triple_of_mem_affineSpan_pair hA hB hC
  linarith

/-! ## M4c1: extreme points and the direction window -/

/-- The extreme points of a convex hull belong to the generating set. -/
lemma extremePoints_convexHull_subset' (A : Set ℂ) :
    (convexHull ℝ A).extremePoints ℝ ⊆ A :=
  extremePoints_convexHull_subset

/-- **Minkowski's theorem for finite sets.**  A finite set of points in the
plane is contained in the convex hull of the extreme points of its own convex
hull. -/
theorem subset_convexHull_extremePoints (S : Finset ℂ) :
    (↑S : Set ℂ) ⊆ convexHull ℝ ((convexHull ℝ (↑S : Set ℂ)).extremePoints ℝ) := by
  have hfin : (↑S : Set ℂ).Finite := S.finite_toSet
  have hKM := closure_convexHull_extremePoints (hfin.isCompact_convexHull ℝ)
    (convex_convexHull ℝ (↑S : Set ℂ))
  have hfin2 : ((convexHull ℝ (↑S : Set ℂ)).extremePoints ℝ).Finite :=
    hfin.subset (extremePoints_convexHull_subset' _)
  rw [(hfin2.isClosed_convexHull ℝ).closure_eq] at hKM
  rw [hKM]
  exact subset_convexHull ℝ _

/-- An extreme point of the convex hull of a finite set does not lie in the
convex hull of the remaining points. -/
lemma extreme_notMem_convexHull_diff {S : Finset ℂ} {v : ℂ} (hv : v ∈ S)
    (hext : v ∈ (convexHull ℝ (↑S : Set ℂ)).extremePoints ℝ) :
    v ∉ convexHull ℝ ((↑S : Set ℂ) \ {v}) := by
  have _hv : v ∈ S := hv
  rw [(convex_convexHull ℝ (↑S : Set ℂ)).mem_extremePoints_iff_mem_sdiff_convexHull_sdiff]
    at hext
  intro hmem
  have hsub : ((↑S : Set ℂ) \ {v}) ⊆ (convexHull ℝ (↑S : Set ℂ) \ {v}) := by
    intro y hy
    exact ⟨subset_convexHull ℝ _ hy.1, hy.2⟩
  exact hext.2 (convexHull_mono hsub hmem)

/-- **Separation at an extreme point.**  At an extreme point `v` of a finite
set `S` there is a nonzero direction `w` such that every other point of `S`
lies strictly on one side of the line through `v` orthogonal to `w`. -/
lemma exists_sep_of_extreme {S : Finset ℂ} {v : ℂ} (hv : v ∈ S)
    (hext : v ∈ (convexHull ℝ (↑S : Set ℂ)).extremePoints ℝ) :
    ∃ w : ℂ, w ≠ 0 ∧ ∀ q ∈ S, q ≠ v →
      (starRingEnd ℂ w * (q - v)).re < 0 := by
  by_cases hS : ∃ q ∈ S, q ≠ v
  · obtain ⟨q₀, hq₀S, hq₀v⟩ := hS
    have hAclosed : IsClosed (convexHull ℝ ((↑S : Set ℂ) \ {v})) :=
      (S.finite_toSet.sdiff).isClosed_convexHull ℝ
    have hvA : v ∉ convexHull ℝ ((↑S : Set ℂ) \ {v}) :=
      extreme_notMem_convexHull_diff hv hext
    obtain ⟨f, r, hfA, hfv⟩ :=
      geometric_hahn_banach_closed_point (convex_convexHull ℝ _) hAclosed hvA
    have hmem : ∀ q ∈ S, q ≠ v → q ∈ convexHull ℝ ((↑S : Set ℂ) \ {v}) := by
      intro q hq hqv
      exact subset_convexHull ℝ _ ⟨Finset.mem_coe.mpr hq, by simpa using hqv⟩
    obtain ⟨w, hw_def⟩ : ∃ w : ℂ,
        w = ((f 1 : ℝ) : ℂ) + ((f Complex.I : ℝ) : ℂ) * Complex.I := ⟨_, rfl⟩
    have hfrep : ∀ z : ℂ, f z = (starRingEnd ℂ w * z).re := by
      intro z
      have hz : (z.re : ℝ) • (1 : ℂ) + (z.im : ℝ) • Complex.I = z := by
        simp [Complex.real_smul]
      calc f z = f ((z.re : ℝ) • (1 : ℂ) + (z.im : ℝ) • Complex.I) := by rw [hz]
        _ = z.re * f 1 + z.im * f Complex.I := by
            rw [map_add, map_smul, map_smul]; simp
        _ = (starRingEnd ℂ w * z).re := by
            rw [hw_def]
            simp [Complex.mul_re]
            ring
    refine ⟨w, ?_, ?_⟩
    · intro h0
      have hzero : ∀ z : ℂ, f z = 0 := by
        intro z; rw [hfrep z, h0]; simp
      have h1 := hfA q₀ (hmem q₀ hq₀S hq₀v)
      rw [hzero] at h1
      rw [hzero] at hfv
      linarith
    · intro q hq hqv
      have h1 := hfA q (hmem q hq hqv)
      have h2 : f (q - v) < 0 := by rw [map_sub]; linarith
      rwa [hfrep (q - v)] at h2
  · exact ⟨1, one_ne_zero, fun q hq hqv => absurd ⟨q, hq, hqv⟩ hS⟩

/-- **The window lemma.**  At an extreme point `v` of a finite set `S` all the
directions from `v` to the other points of `S` lie in a closed angular window
`[θ, θ + A]` of width `A < π`, and both edges of the window are attained by
actual points of `S`. -/
theorem exists_window_at_extreme {S : Finset ℂ} {v : ℂ} (hv : v ∈ S)
    (hS : ∃ q ∈ S, q ≠ v)
    (hext : v ∈ (convexHull ℝ (↑S : Set ℂ)).extremePoints ℝ) :
    ∃ θ A : ℝ, 0 ≤ A ∧ A < π ∧
      (∀ q ∈ S, q ≠ v → ∃ r t : ℝ, 0 < r ∧ 0 ≤ t ∧ t ≤ A ∧
        q - v = (r : ℂ) * Complex.exp (((θ + t : ℝ) : ℂ) * Complex.I)) ∧
      (∃ a ∈ S, a ≠ v ∧
        a - v = ((‖a - v‖ : ℝ) : ℂ)
          * Complex.exp ((θ : ℂ) * Complex.I)) ∧
      (∃ b ∈ S, b ≠ v ∧
        b - v = ((‖b - v‖ : ℝ) : ℂ)
          * Complex.exp (((θ + A : ℝ) : ℂ) * Complex.I)) := by
  classical
  obtain ⟨w, hw0, hwsep⟩ := exists_sep_of_extreme hv hext
  have hwnorm : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw0
  -- the unit direction pointing into the half-plane containing `S`
  obtain ⟨u, hu_def⟩ : ∃ u : ℂ,
      u = (((1 / ‖w‖ : ℝ)) : ℂ) * (-(starRingEnd ℂ w)) := ⟨_, rfl⟩
  have hunorm : ‖u‖ = 1 := by
    rw [hu_def, norm_mul, norm_neg, Complex.norm_conj, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / ‖w‖)]
    field_simp
  have hu0 : u ≠ 0 := by
    intro h
    rw [h] at hunorm
    simp at hunorm
  have hre : ∀ q ∈ S, q ≠ v → 0 < (u * (q - v)).re := by
    intro q hq hqv
    have hsep := hwsep q hq hqv
    have hrw : u * (q - v)
        = ((-(1 / ‖w‖) : ℝ) : ℂ) * (starRingEnd ℂ w * (q - v)) := by
      rw [hu_def]; push_cast; ring
    rw [hrw, Complex.re_ofReal_mul]
    have hpos : (0 : ℝ) < 1 / ‖w‖ := by positivity
    nlinarith [mul_pos hpos (neg_pos.mpr hsep)]
  -- the rotation taking the direction `u` back to `1`
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℝ, ψ = -Complex.arg u := ⟨_, rfl⟩
  have hui : u * Complex.exp ((ψ : ℂ) * Complex.I) = 1 := by
    have h2 : Complex.exp (((Complex.arg u : ℝ) : ℂ) * Complex.I) = u := by
      have h := Complex.norm_mul_exp_arg_mul_I u
      rw [hunorm] at h
      simpa using h
    have hz : ((Complex.arg u : ℝ) : ℂ) * Complex.I + (ψ : ℂ) * Complex.I = 0 := by
      rw [hψ]; push_cast; ring
    calc u * Complex.exp ((ψ : ℂ) * Complex.I)
        = Complex.exp (((Complex.arg u : ℝ) : ℂ) * Complex.I)
          * Complex.exp ((ψ : ℂ) * Complex.I) := by rw [h2]
      _ = Complex.exp (((Complex.arg u : ℝ) : ℂ) * Complex.I + (ψ : ℂ) * Complex.I) :=
          (Complex.exp_add _ _).symm
      _ = 1 := by rw [hz, Complex.exp_zero]
  -- polar form of every edge at `v`, measured from the direction `u`
  have hkey : ∀ q : ℂ, q ≠ v →
      q - v = ((‖q - v‖ : ℝ) : ℂ)
        * Complex.exp ((((ψ + Complex.arg (u * (q - v))) : ℝ) : ℂ) * Complex.I) := by
    intro q hqv
    have h5 : ‖u * (q - v)‖ = ‖q - v‖ := by rw [norm_mul, hunorm, one_mul]
    have h6 : ((‖q - v‖ : ℝ) : ℂ)
        * Complex.exp (((Complex.arg (u * (q - v)) : ℝ) : ℂ) * Complex.I)
        = u * (q - v) := by
      rw [← h5]; exact Complex.norm_mul_exp_arg_mul_I _
    have hsplit : (ψ : ℂ) * Complex.I
        + ((Complex.arg (u * (q - v)) : ℝ) : ℂ) * Complex.I
        = (((ψ + Complex.arg (u * (q - v))) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    calc q - v = 1 * (q - v) := (one_mul _).symm
      _ = (u * Complex.exp ((ψ : ℂ) * Complex.I)) * (q - v) := by rw [hui]
      _ = Complex.exp ((ψ : ℂ) * Complex.I) * (u * (q - v)) := by ring
      _ = Complex.exp ((ψ : ℂ) * Complex.I)
            * (((‖q - v‖ : ℝ) : ℂ)
              * Complex.exp (((Complex.arg (u * (q - v)) : ℝ) : ℂ) * Complex.I)) := by
          rw [h6]
      _ = ((‖q - v‖ : ℝ) : ℂ) * (Complex.exp ((ψ : ℂ) * Complex.I)
            * Complex.exp (((Complex.arg (u * (q - v)) : ℝ) : ℂ) * Complex.I)) := by ring
      _ = ((‖q - v‖ : ℝ) : ℂ)
            * Complex.exp ((((ψ + Complex.arg (u * (q - v))) : ℝ) : ℂ) * Complex.I) := by
          rw [← Complex.exp_add, hsplit]
  -- the extreme directions
  obtain ⟨q₀, hq₀S, hq₀v⟩ := hS
  have hne : (S.erase v).Nonempty := ⟨q₀, Finset.mem_erase.mpr ⟨hq₀v, hq₀S⟩⟩
  obtain ⟨a, haE, hamin⟩ := Finset.exists_min_image (S.erase v)
    (fun q => Complex.arg (u * (q - v))) hne
  obtain ⟨b, hbE, hbmax⟩ := Finset.exists_max_image (S.erase v)
    (fun q => Complex.arg (u * (q - v))) hne
  have hamin' : ∀ q ∈ S.erase v,
      Complex.arg (u * (a - v)) ≤ Complex.arg (u * (q - v)) := hamin
  have hbmax' : ∀ q ∈ S.erase v,
      Complex.arg (u * (q - v)) ≤ Complex.arg (u * (b - v)) := hbmax
  obtain ⟨hav, haS⟩ := Finset.mem_erase.mp haE
  obtain ⟨hbv, hbS⟩ := Finset.mem_erase.mp hbE
  have hargbd : ∀ q ∈ S, q ≠ v → |Complex.arg (u * (q - v))| < π / 2 := fun q hq hqv =>
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (hre q hq hqv))
  have hbndA := hargbd a haS hav
  have hbndB := hargbd b hbS hbv
  rw [abs_lt] at hbndA hbndB
  refine ⟨ψ + Complex.arg (u * (a - v)),
    Complex.arg (u * (b - v)) - Complex.arg (u * (a - v)),
    by linarith [hamin' b hbE], by linarith, ?_, ?_, ?_⟩
  · intro q hqS hqv
    have hqE : q ∈ S.erase v := Finset.mem_erase.mpr ⟨hqv, hqS⟩
    refine ⟨‖q - v‖, Complex.arg (u * (q - v)) - Complex.arg (u * (a - v)),
      norm_pos_iff.mpr (sub_ne_zero.mpr hqv), by linarith [hamin' q hqE],
      by linarith [hbmax' q hqE], ?_⟩
    have hrew : (ψ + Complex.arg (u * (a - v)))
        + (Complex.arg (u * (q - v)) - Complex.arg (u * (a - v)))
        = ψ + Complex.arg (u * (q - v)) := by ring
    rw [hrew]
    exact hkey q hqv
  · exact ⟨a, haS, hav, hkey a hav⟩
  · refine ⟨b, hbS, hbv, ?_⟩
    have hrew : (ψ + Complex.arg (u * (a - v)))
        + (Complex.arg (u * (b - v)) - Complex.arg (u * (a - v)))
        = ψ + Complex.arg (u * (b - v)) := by ring
    rw [hrew]
    exact hkey b hbv

/-! ## M4c2a: centroid and extreme-point basics -/

/-- The centroid (average) of a finite set of points of the plane. -/
noncomputable def szCentroid (S : Finset ℂ) : ℂ := (∑ p ∈ S, p) / S.card

/-- The extreme points of the convex hull of `S`, viewed as a subset of `S`. -/
noncomputable def extremeFinset (S : Finset ℂ) : Finset ℂ :=
  @Finset.filter ℂ (fun p => p ∈ (convexHull ℝ (↑S : Set ℂ)).extremePoints ℝ)
    (Classical.decPred _) S

lemma mem_extremeFinset {S : Finset ℂ} {p : ℂ} :
    p ∈ extremeFinset S ↔ p ∈ (convexHull ℝ (↑S : Set ℂ)).extremePoints ℝ := by
  have h := @Finset.mem_filter ℂ
    (fun q => q ∈ (convexHull ℝ (↑S : Set ℂ)).extremePoints ℝ) (Classical.decPred _) S p
  unfold extremeFinset
  exact h.trans ⟨fun hh => hh.2, fun hh => ⟨extremePoints_convexHull_subset' _ hh, hh⟩⟩

lemma mem_of_mem_extremeFinset {S : Finset ℂ} {p : ℂ} (h : p ∈ extremeFinset S) : p ∈ S :=
  extremePoints_convexHull_subset' _ (mem_extremeFinset.mp h)

/-- The vectors from the centroid to the points of `S` sum to zero. -/
lemma sum_sub_szCentroid {S : Finset ℂ} (hS : 0 < S.card) :
    ∑ p ∈ S, (p - szCentroid S) = 0 := by
  have hc : ((S.card : ℕ) : ℂ) ≠ 0 := by
    have : S.card ≠ 0 := by omega
    exact_mod_cast this
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, szCentroid]
  field_simp
  ring

/-- The centroid lies in the convex hull. -/
lemma szCentroid_mem_convexHull {S : Finset ℂ} (hS : 0 < S.card) :
    szCentroid S ∈ convexHull ℝ (↑S : Set ℂ) := by
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hS
  have h := S.centerMass_id_mem_convexHull (R := ℝ) (w := fun _ => (1 : ℝ))
    (fun i _ => zero_le_one) (by simpa using hcard)
  have heq : S.centerMass (fun _ => (1 : ℝ)) id = szCentroid S := by
    rw [Finset.centerMass, szCentroid]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, id_eq, one_smul,
      Complex.real_smul]
    push_cast
    field_simp
  rwa [heq] at h

/-- `extremeFinset` really is the set of extreme points. -/
lemma coe_extremeFinset (S : Finset ℂ) :
    (↑(extremeFinset S) : Set ℂ)
      = (convexHull ℝ (↑S : Set ℂ)).extremePoints ℝ := by
  ext p
  rw [Finset.mem_coe]
  exact mem_extremeFinset

/-- A finite set of at most two points is collinear. -/
lemma collinear_of_card_le_two {T : Finset ℂ} (h : T.card ≤ 2) :
    Collinear ℝ (↑T : Set ℂ) := by
  rcases T.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · simpa using collinear_empty ℝ ℂ
  rcases (T.erase a).eq_empty_or_nonempty with he | ⟨b, hb⟩
  · have hT : T = {a} := by rw [← Finset.insert_erase ha, he]; rfl
    rw [hT, Finset.coe_singleton]
    exact collinear_singleton ℝ a
  · have hc : (T.erase a).card ≤ 1 := by
      have := Finset.card_erase_of_mem ha
      omega
    have hsub : (↑T : Set ℂ) ⊆ ({a, b} : Set ℂ) := by
      intro x hx
      by_cases hxa : x = a
      · simp [hxa]
      · have hxe : x ∈ T.erase a := Finset.mem_erase.mpr ⟨hxa, hx⟩
        have hxb : x = b := Finset.card_le_one.mp hc x hxe b hb
        simp [hxb]
    exact (collinear_pair ℝ a b).subset hsub

/-- In general position a set of at least three points is not collinear. -/
lemma not_collinear_of_gen {S : Finset ℂ} (hS : 3 ≤ S.card)
    (hgen : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set ℂ)) :
    ¬ Collinear ℝ (↑S : Set ℂ) := by
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ :=
    (Finset.two_lt_card (s := S)).mp (by omega)
  intro h
  refine hgen a ha b hb c hc hab hbc hac (h.subset ?_)
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact hc

/-- In general position there are at least three extreme points. -/
lemma three_le_card_extremeFinset {S : Finset ℂ} (hS : 3 ≤ S.card)
    (hgen : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set ℂ)) :
    3 ≤ (extremeFinset S).card := by
  by_contra hcon
  rw [Nat.not_le] at hcon
  have hcolE : Collinear ℝ (↑(extremeFinset S) : Set ℂ) :=
    collinear_of_card_le_two (T := extremeFinset S) (by omega)
  rw [collinear_iff_exists_forall_eq_smul_vadd] at hcolE
  obtain ⟨p₀, vv, hL⟩ := hcolE
  obtain ⟨L, hL_def⟩ : ∃ L : Set ℂ, L = {x : ℂ | ∃ r : ℝ, x = (r : ℂ) * vv + p₀} :=
    ⟨_, rfl⟩
  have hLconv : Convex ℝ L := by
    rw [hL_def]
    intro x hx y hy s t hs ht hst
    obtain ⟨r₁, hr₁⟩ := hx
    obtain ⟨r₂, hr₂⟩ := hy
    refine ⟨s * r₁ + t * r₂, ?_⟩
    have hst' : (s : ℂ) + (t : ℂ) = 1 := by exact_mod_cast hst
    rw [hr₁, hr₂]
    simp only [Complex.real_smul]
    push_cast
    linear_combination (p₀ : ℂ) * hst'
  have hEL : (↑(extremeFinset S) : Set ℂ) ⊆ L := by
    intro p hp
    obtain ⟨r, hr⟩ := hL p hp
    rw [hL_def]
    exact ⟨r, by simpa [Complex.real_smul] using hr⟩
  have hSL : (↑S : Set ℂ) ⊆ L := by
    intro p hp
    have h1 := subset_convexHull_extremePoints S hp
    rw [← coe_extremeFinset] at h1
    exact convexHull_min hEL hLconv h1
  refine not_collinear_of_gen hS hgen ?_
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  refine ⟨p₀, vv, fun p hp => ?_⟩
  have hpL := hSL hp
  rw [hL_def] at hpL
  obtain ⟨r, hr⟩ := hpL
  exact ⟨r, by simpa [Complex.real_smul] using hr⟩

/-- An extreme point is never the centroid. -/
lemma extremeFinset_ne_szCentroid {S : Finset ℂ} (hS : 3 ≤ S.card)
    {v : ℂ} (hv : v ∈ extremeFinset S) : v ≠ szCentroid S := by
  intro hveq
  have hvS : v ∈ S := mem_of_mem_extremeFinset hv
  have hext : v ∈ (convexHull ℝ (↑S : Set ℂ)).extremePoints ℝ := mem_extremeFinset.mp hv
  have hcard : (S.erase v).card = S.card - 1 := Finset.card_erase_of_mem hvS
  have hpos : 0 < (S.erase v).card := by omega
  have hsum : ∑ p ∈ S, p = (∑ p ∈ S.erase v, p) + v :=
    (Finset.sum_erase_add S _ hvS).symm
  have hN0 : ((S.card : ℕ) : ℂ) ≠ 0 := by
    have h : S.card ≠ 0 := by omega
    exact_mod_cast h
  have hNcast : (((S.erase v).card : ℕ) : ℂ) = ((S.card : ℕ) : ℂ) - 1 := by
    rw [hcard, Nat.cast_sub (by omega : 1 ≤ S.card)]
    norm_num
  have hN1 : ((S.card : ℕ) : ℂ) - 1 ≠ 0 := by
    intro h
    have h2 : ((S.card : ℕ) : ℂ) = 1 := by linear_combination h
    have h3 : S.card = 1 := by exact_mod_cast h2
    omega
  have key : v = szCentroid (S.erase v) := by
    simp only [szCentroid] at hveq ⊢
    rw [eq_div_iff hN0, hsum] at hveq
    rw [hNcast, eq_div_iff hN1]
    linear_combination hveq
  have hmem := szCentroid_mem_convexHull hpos
  rw [← key, Finset.coe_erase] at hmem
  exact extreme_notMem_convexHull_diff hvS hext hmem

/-- Distinct extreme points are seen from the centroid in distinct directions. -/
lemma arg_sub_szCentroid_injOn {S : Finset ℂ} (hS : 3 ≤ S.card)
    (hgen : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set ℂ)) :
    ∀ v ∈ extremeFinset S, ∀ w ∈ extremeFinset S,
      Complex.arg (v - szCentroid S) = Complex.arg (w - szCentroid S) →
        v = w := by
  have _hgen := hgen
  have hcK : szCentroid S ∈ convexHull ℝ (↑S : Set ℂ) :=
    szCentroid_mem_convexHull (by omega)
  have main : ∀ x y : ℂ, x ∈ extremeFinset S → y ∈ S →
      Complex.arg (x - szCentroid S) = Complex.arg (y - szCentroid S) →
      ‖x - szCentroid S‖ < ‖y - szCentroid S‖ → False := by
    intro x y hx hy hargxy hlt
    have hxc : x ≠ szCentroid S := extremeFinset_ne_szCentroid hS hx
    have hxE : x ∈ (convexHull ℝ (↑S : Set ℂ)).extremePoints ℝ := mem_extremeFinset.mp hx
    have hyH : y ∈ convexHull ℝ (↑S : Set ℂ) := subset_convexHull ℝ _ hy
    have hnx : 0 < ‖x - szCentroid S‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxc)
    have hny : 0 < ‖y - szCentroid S‖ := lt_trans hnx hlt
    obtain ⟨s, hs_def⟩ : ∃ s : ℝ,
        s = ‖x - szCentroid S‖ / ‖y - szCentroid S‖ := ⟨_, rfl⟩
    have hs0 : 0 < s := by rw [hs_def]; positivity
    have hs1 : s < 1 := by rw [hs_def, div_lt_one hny]; exact hlt
    have hnyC : ((‖y - szCentroid S‖ : ℝ) : ℂ) ≠ 0 := by
      simpa using hny.ne'
    have hsm : (s : ℂ) * ((‖y - szCentroid S‖ : ℝ) : ℂ)
        = ((‖x - szCentroid S‖ : ℝ) : ℂ) := by
      rw [hs_def]
      push_cast
      field_simp
    obtain ⟨E, hE⟩ : ∃ E : ℂ,
        E = Complex.exp (((Complex.arg (y - szCentroid S) : ℝ) : ℂ) * Complex.I) :=
      ⟨_, rfl⟩
    have h1 : ((‖x - szCentroid S‖ : ℝ) : ℂ) * E = x - szCentroid S := by
      rw [hE, ← hargxy]
      exact Complex.norm_mul_exp_arg_mul_I _
    have h2 : ((‖y - szCentroid S‖ : ℝ) : ℂ) * E = y - szCentroid S := by
      rw [hE]
      exact Complex.norm_mul_exp_arg_mul_I _
    have hseg : x ∈ openSegment ℝ (szCentroid S) y := by
      refine ⟨1 - s, s, by linarith, hs0, by ring, ?_⟩
      simp only [Complex.real_smul]
      push_cast
      linear_combination h1 - (s : ℂ) * h2 + E * hsm
    exact hxc (hxE.2 hcK hyH hseg).symm
  intro v hv w hw harg
  have hvS : v ∈ S := mem_of_mem_extremeFinset hv
  have hwS : w ∈ S := mem_of_mem_extremeFinset hw
  rcases lt_trichotomy ‖v - szCentroid S‖ ‖w - szCentroid S‖ with h | h | h
  · exact (main v w hv hwS harg h).elim
  · have h1 := Complex.norm_mul_exp_arg_mul_I (v - szCentroid S)
    have h2 := Complex.norm_mul_exp_arg_mul_I (w - szCentroid S)
    rw [harg, h, h2] at h1
    linear_combination -h1
  · exact (main w v hw hvS harg.symm h).elim

/-- In general position, no closed half-plane through the centroid contains all
of `S`: for every direction `u` some point of `S` lies strictly on the negative
side. -/
theorem exists_re_neg_of_ne_zero {S : Finset ℂ} (hS : 3 ≤ S.card)
    (hgen : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set ℂ))
    {u : ℂ} (hu : u ≠ 0) :
    ∃ p ∈ S, (starRingEnd ℂ u * (p - szCentroid S)).re < 0 := by
  by_contra hcon
  have hnn : ∀ p ∈ S, 0 ≤ (starRingEnd ℂ u * (p - szCentroid S)).re := by
    intro p hp
    by_contra h
    exact hcon ⟨p, hp, not_le.mp h⟩
  have hsum : ∑ p ∈ S, (starRingEnd ℂ u * (p - szCentroid S)).re = 0 := by
    rw [← Complex.re_sum, ← Finset.mul_sum, sum_sub_szCentroid (by omega)]
    simp
  have hzero : ∀ p ∈ S, (starRingEnd ℂ u * (p - szCentroid S)).re = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum
  have hnsq : ((Complex.normSq u : ℝ) : ℂ) ≠ 0 := by
    simpa using (Complex.normSq_pos.mpr hu).ne'
  have hmc : u * (starRingEnd ℂ u) = ((Complex.normSq u : ℝ) : ℂ) := Complex.mul_conj u
  refine not_collinear_of_gen hS hgen ?_
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  refine ⟨szCentroid S, Complex.I * u, fun p hp => ?_⟩
  obtain ⟨y, hy_def⟩ : ∃ y : ℝ,
      y = (starRingEnd ℂ u * (p - szCentroid S)).im := ⟨_, rfl⟩
  have h0 := hzero p hp
  have hcu : starRingEnd ℂ u * (p - szCentroid S) = ((y : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext
    · rw [h0]; simp
    · rw [hy_def]; simp
  refine ⟨y / Complex.normSq u, ?_⟩
  rw [vadd_eq_add]
  simp only [Complex.real_smul]
  rw [← sub_eq_iff_eq_add, eq_comm]
  push_cast
  rw [div_mul_eq_mul_div, div_eq_iff hnsq]
  linear_combination (-u) * hcu + (p - szCentroid S) * hmc

/-! ## M4c2b1: the sorted cyclic enumeration -/

/-- The real part of `conj (e^{iχ}) * z`, in polar terms. -/
lemma re_conj_exp_mul (χ : ℝ) (z : ℂ) :
    ((starRingEnd ℂ) (Complex.exp ((χ : ℂ) * Complex.I)) * z).re
      = ‖z‖ * Real.cos (Complex.arg z - χ) := by
  have hconj : (starRingEnd ℂ) (Complex.exp ((χ : ℂ) * Complex.I))
      = Complex.exp (((-χ : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have hz : z = ((‖z‖ : ℝ) : ℂ)
      * Complex.exp (((Complex.arg z : ℝ) : ℂ) * Complex.I) :=
    (Complex.norm_mul_exp_arg_mul_I z).symm
  have hadd : Complex.exp (((Complex.arg z : ℝ) : ℂ) * Complex.I)
      * Complex.exp (((-χ : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((Complex.arg z - χ : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have key : (starRingEnd ℂ) (Complex.exp ((χ : ℂ) * Complex.I)) * z
      = ((‖z‖ : ℝ) : ℂ)
        * Complex.exp (((Complex.arg z - χ : ℝ) : ℂ) * Complex.I) := by
    rw [hconj]
    linear_combination Complex.exp (((-χ : ℝ) : ℂ) * Complex.I) * hz
      + ((‖z‖ : ℝ) : ℂ) * hadd
  rw [key, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-- **Half-plane exclusion, extreme-point version.**  In general position, for
every direction `u` some extreme point lies strictly on the negative side of the
line through the centroid orthogonal to `u`. -/
theorem exists_extreme_re_neg {S : Finset ℂ} (hS : 3 ≤ S.card)
    (hgen : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set ℂ))
    {u : ℂ} (hu : u ≠ 0) :
    ∃ v ∈ extremeFinset S, (starRingEnd ℂ u * (v - szCentroid S)).re < 0 := by
  by_contra hcon
  have hnn : ∀ v ∈ extremeFinset S,
      0 ≤ (starRingEnd ℂ u * (v - szCentroid S)).re := by
    intro v hv
    by_contra h
    exact hcon ⟨v, hv, not_le.mp h⟩
  obtain ⟨H, hHdef⟩ : ∃ H : Set ℂ,
      H = {z : ℂ | 0 ≤ (starRingEnd ℂ u * (z - szCentroid S)).re} := ⟨_, rfl⟩
  have hHconv : Convex ℝ H := by
    rw [hHdef]
    intro x hx y hy a b ha hb hab
    have hx' : 0 ≤ (starRingEnd ℂ u * (x - szCentroid S)).re := hx
    have hy' : 0 ≤ (starRingEnd ℂ u * (y - szCentroid S)).re := hy
    show 0 ≤ (starRingEnd ℂ u * ((a • x + b • y) - szCentroid S)).re
    have hab' : (a : ℂ) + (b : ℂ) = 1 := by exact_mod_cast hab
    have heq : starRingEnd ℂ u * ((a • x + b • y) - szCentroid S)
        = (a : ℂ) * (starRingEnd ℂ u * (x - szCentroid S))
          + (b : ℂ) * (starRingEnd ℂ u * (y - szCentroid S)) := by
      simp only [Complex.real_smul]
      linear_combination (starRingEnd ℂ u * szCentroid S) * hab'
    rw [heq, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    have h1 := mul_nonneg ha hx'
    have h2 := mul_nonneg hb hy'
    linarith
  have hsub : (↑(extremeFinset S) : Set ℂ) ⊆ H := by
    intro p hp
    rw [hHdef]
    exact hnn p (Finset.mem_coe.mp hp)
  have hSH : (↑S : Set ℂ) ⊆ H := by
    intro p hp
    have h1 := subset_convexHull_extremePoints S hp
    rw [← coe_extremeFinset] at h1
    exact convexHull_min hsub hHconv h1
  obtain ⟨p, hp, hlt⟩ := exists_re_neg_of_ne_zero hS hgen hu
  have hpH := hSH (Finset.mem_coe.mpr hp)
  rw [hHdef] at hpH
  have hpH' : 0 ≤ (starRingEnd ℂ u * (p - szCentroid S)).re := hpH
  linarith

/-- If the cosine test is nonnegative at every extreme point, all extreme points
lie in a closed half-plane through the centroid — impossible. -/
lemma not_forall_cos_nonneg {S : Finset ℂ} (hS : 3 ≤ S.card)
    (hgen : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set ℂ)) (χ : ℝ)
    (h : ∀ v ∈ extremeFinset S,
      0 ≤ Real.cos (Complex.arg (v - szCentroid S) - χ)) : False := by
  obtain ⟨v, hv, hlt⟩ := exists_extreme_re_neg hS hgen
    (u := Complex.exp ((χ : ℂ) * Complex.I)) (Complex.exp_ne_zero _)
  rw [re_conj_exp_mul] at hlt
  have hnn := mul_nonneg (norm_nonneg (v - szCentroid S)) (h v hv)
  linarith

/-- **The sorted cyclic enumeration.**  In general position the extreme points
can be listed in strictly increasing order of their argument as seen from the
centroid. -/
theorem exists_argSorted_enum {S : Finset ℂ} (hS : 3 ≤ S.card)
    (hgen : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set ℂ)) :
    ∃ w : Fin (extremeFinset S).card → ℂ,
      (∀ i, w i ∈ extremeFinset S) ∧
      (∀ v ∈ extremeFinset S, ∃ i, w i = v) ∧
      StrictMono (fun i => Complex.arg (w i - szCentroid S)) := by
  classical
  have hinj := arg_sub_szCentroid_injOn hS hgen
  have hinjOn : Set.InjOn (fun v => Complex.arg (v - szCentroid S))
      (↑(extremeFinset S) : Set ℂ) := by
    intro x hx y hy hxy
    exact hinj x (Finset.mem_coe.mp hx) y (Finset.mem_coe.mp hy) hxy
  have hcard : ((extremeFinset S).image
      (fun v => Complex.arg (v - szCentroid S))).card = (extremeFinset S).card :=
    Finset.card_image_of_injOn hinjOn
  obtain ⟨f, hfdef⟩ : ∃ f : Fin (extremeFinset S).card ↪o ℝ,
      f = ((extremeFinset S).image
        (fun v => Complex.arg (v - szCentroid S))).orderEmbOfFin hcard := ⟨_, rfl⟩
  have hfmem : ∀ i, f i ∈ (extremeFinset S).image
      (fun v => Complex.arg (v - szCentroid S)) := by
    intro i
    rw [hfdef]
    exact Finset.orderEmbOfFin_mem _ hcard i
  have hchoice : ∀ i : Fin (extremeFinset S).card,
      ∃ v, v ∈ extremeFinset S ∧ Complex.arg (v - szCentroid S) = f i := by
    intro i
    have h := hfmem i
    rw [Finset.mem_image] at h
    obtain ⟨v, hv, hveq⟩ := h
    exact ⟨v, hv, hveq⟩
  choose w hw hwarg using hchoice
  refine ⟨w, hw, ?_, ?_⟩
  · intro v hv
    have hvT : Complex.arg (v - szCentroid S) ∈ (extremeFinset S).image
        (fun v => Complex.arg (v - szCentroid S)) := Finset.mem_image_of_mem _ hv
    have hrange : Complex.arg (v - szCentroid S) ∈ Set.range f := by
      rw [hfdef, Finset.range_orderEmbOfFin]
      exact Finset.mem_coe.mpr hvT
    obtain ⟨i, hi⟩ := hrange
    exact ⟨i, hinj (w i) (hw i) v hv (by rw [hwarg i]; exact hi)⟩
  · intro i j hij
    simp only [hwarg]
    exact f.strictMono hij

/-- **The gaps of the sorted cyclic enumeration are less than `π`.** -/
theorem argGap_lt_pi {S : Finset ℂ} (hS : 3 ≤ S.card)
    (hgen : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set ℂ))
    {k : ℕ} (w : Fin k → ℂ)
    (hmem : ∀ i, w i ∈ extremeFinset S)
    (hsur : ∀ v ∈ extremeFinset S, ∃ i, w i = v)
    (hmono : StrictMono (fun i => Complex.arg (w i - szCentroid S)))
    (hk : 0 < k) :
    (∀ i : ℕ, ∀ hi : i + 1 < k,
      Complex.arg (w ⟨i + 1, hi⟩ - szCentroid S)
        - Complex.arg (w ⟨i, by omega⟩ - szCentroid S) < π) ∧
    Complex.arg (w ⟨0, hk⟩ - szCentroid S) + 2 * π
      - Complex.arg (w ⟨k - 1, by omega⟩ - szCentroid S) < π := by
  have _hmem := hmem
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hlo : ∀ l : Fin k, -π < Complex.arg (w l - szCentroid S) :=
    fun l => Complex.neg_pi_lt_arg _
  have hhi : ∀ l : Fin k, Complex.arg (w l - szCentroid S) ≤ π :=
    fun l => Complex.arg_le_pi _
  have key : ∀ χ : ℝ,
      (∀ l : Fin k, 0 ≤ Real.cos (Complex.arg (w l - szCentroid S) - χ)) →
      False := by
    intro χ hcos
    refine not_forall_cos_nonneg hS hgen χ ?_
    intro v hv
    obtain ⟨l, hl⟩ := hsur v hv
    rw [← hl]
    exact hcos l
  constructor
  · intro i hi
    by_contra hcon
    have hi0 : i < k := by omega
    have hgap : π ≤ Complex.arg (w ⟨i + 1, hi⟩ - szCentroid S)
        - Complex.arg (w ⟨i, hi0⟩ - szCentroid S) := not_lt.mp hcon
    obtain ⟨a, ha⟩ : ∃ a : ℝ, a = Complex.arg (w ⟨i, hi0⟩ - szCentroid S) :=
      ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b : ℝ, b = Complex.arg (w ⟨i + 1, hi⟩ - szCentroid S) :=
      ⟨_, rfl⟩
    rw [← ha, ← hb] at hgap
    have halo : -π < a := by rw [ha]; exact hlo _
    have hahi : a ≤ π := by rw [ha]; exact hhi _
    have hblo : -π < b := by rw [hb]; exact hlo _
    have hbhi : b ≤ π := by rw [hb]; exact hhi _
    refine key ((a + b) / 2 + π) ?_
    intro l
    obtain ⟨φ, hφ⟩ : ∃ φ : ℝ, φ = Complex.arg (w l - szCentroid S) := ⟨_, rfl⟩
    rw [← hφ]
    have hφlo : -π < φ := by rw [hφ]; exact hlo _
    have hφhi : φ ≤ π := by rw [hφ]; exact hhi _
    rcases le_or_gt (l : ℕ) i with hle | hgt
    · have hmA : φ ≤ a := by
        rw [hφ, ha]
        exact hmono.monotone (show l ≤ (⟨i, hi0⟩ : Fin k) from Fin.le_def.mpr hle)
      rw [← Real.cos_add_two_pi]
      refine Real.cos_nonneg_of_neg_pi_div_two_le_of_le ?_ ?_ <;> linarith
    · have hmB : b ≤ φ := by
        rw [hφ, hb]
        exact hmono.monotone
          (show (⟨i + 1, hi⟩ : Fin k) ≤ l from Fin.le_def.mpr hgt)
      refine Real.cos_nonneg_of_neg_pi_div_two_le_of_le ?_ ?_ <;> linarith
  · by_contra hcon
    have hk1 : k - 1 < k := by omega
    have hwrap : π ≤ Complex.arg (w ⟨0, hk⟩ - szCentroid S) + 2 * π
        - Complex.arg (w ⟨k - 1, hk1⟩ - szCentroid S) := not_lt.mp hcon
    obtain ⟨A, hA⟩ : ∃ A : ℝ, A = Complex.arg (w ⟨0, hk⟩ - szCentroid S) :=
      ⟨_, rfl⟩
    obtain ⟨B, hB⟩ : ∃ B : ℝ, B = Complex.arg (w ⟨k - 1, hk1⟩ - szCentroid S) :=
      ⟨_, rfl⟩
    rw [← hA, ← hB] at hwrap
    refine key ((A + B) / 2) ?_
    intro l
    have hlk := l.isLt
    obtain ⟨φ, hφ⟩ : ∃ φ : ℝ, φ = Complex.arg (w l - szCentroid S) := ⟨_, rfl⟩
    rw [← hφ]
    have hmA : A ≤ φ := by
      rw [hφ, hA]
      exact hmono.monotone
        (show (⟨0, hk⟩ : Fin k) ≤ l from Fin.le_def.mpr (Nat.zero_le _))
    have hmB : φ ≤ B := by
      rw [hφ, hB]
      exact hmono.monotone
        (show l ≤ (⟨k - 1, hk1⟩ : Fin k) from
          Fin.le_def.mpr (show (l : ℕ) ≤ k - 1 by omega))
    refine Real.cos_nonneg_of_neg_pi_div_two_le_of_le ?_ ?_ <;> linarith

/-! ## M4c2b2a: half-line support package -/

/-- The imaginary part of `conj z * w`, in polar terms. -/
lemma im_conj_mul (z w : ℂ) :
    ((starRingEnd ℂ) z * w).im
      = ‖z‖ * ‖w‖ * Real.sin (Complex.arg w - Complex.arg z) := by
  have hz : z = ((‖z‖ : ℝ) : ℂ)
      * Complex.exp (((Complex.arg z : ℝ) : ℂ) * Complex.I) :=
    (Complex.norm_mul_exp_arg_mul_I z).symm
  have hw : w = ((‖w‖ : ℝ) : ℂ)
      * Complex.exp (((Complex.arg w : ℝ) : ℂ) * Complex.I) :=
    (Complex.norm_mul_exp_arg_mul_I w).symm
  have hconj : (starRingEnd ℂ) z = ((‖z‖ : ℝ) : ℂ)
      * Complex.exp (((-Complex.arg z : ℝ) : ℂ) * Complex.I) := by
    conv_lhs => rw [hz]
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    congr 2
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have hadd : Complex.exp (((-Complex.arg z : ℝ) : ℂ) * Complex.I)
      * Complex.exp (((Complex.arg w : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((Complex.arg w - Complex.arg z : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have key : (starRingEnd ℂ) z * w
      = ((‖z‖ : ℝ) : ℂ) * ((‖w‖ : ℝ) : ℂ)
        * Complex.exp (((Complex.arg w - Complex.arg z : ℝ) : ℂ) * Complex.I) := by
    rw [hconj]
    linear_combination
      (((‖z‖ : ℝ) : ℂ) * Complex.exp (((-Complex.arg z : ℝ) : ℂ) * Complex.I)) * hw
      + ((‖z‖ : ℝ) : ℂ) * ((‖w‖ : ℝ) : ℂ) * hadd
  rw [key, ← Complex.ofReal_mul, Complex.im_ofReal_mul,
    Complex.exp_ofReal_mul_I_im]

/-- If `conj u * z` is real then `z` is a real multiple of `u`. -/
lemma eq_smul_of_im_conj_eq_zero {u z : ℂ} (hu : u ≠ 0)
    (h : ((starRingEnd ℂ) u * z).im = 0) :
    z = ((((starRingEnd ℂ) u * z).re) / Complex.normSq u) • u := by
  have hns : Complex.normSq u ≠ 0 := ne_of_gt (Complex.normSq_pos.mpr hu)
  have hns' : ((Complex.normSq u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hns
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ((starRingEnd ℂ) u * z).re := ⟨_, rfl⟩
  have hconj : (starRingEnd ℂ) u * z = (c : ℂ) := by
    apply Complex.ext
    · simp [hc]
    · simp [h]
  have hmul : u * ((starRingEnd ℂ) u * z) = ((Complex.normSq u : ℝ) : ℂ) * z := by
    rw [← mul_assoc, Complex.mul_conj]
  have h2 : ((Complex.normSq u : ℝ) : ℂ) * z = (c : ℂ) * u := by
    rw [← hmul, hconj]
    ring
  rw [← hc, Complex.real_smul, Complex.ofReal_div]
  field_simp
  linear_combination h2

/-- If all of `S` lies in the closed half-plane through `v ∈ S` with inner
normal `u`, and `S` is in general position with at least three points, then the
centroid lies strictly inside that half-plane. -/
lemma im_szCentroid_pos_of_halfline {S : Finset ℂ} (hS : 3 ≤ S.card)
    (hgen : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set ℂ))
    {v u : ℂ} (hv : v ∈ S) (hu : u ≠ 0)
    (hhalf : ∀ q ∈ S, 0 ≤ ((starRingEnd ℂ) u * (q - v)).im) :
    0 < ((starRingEnd ℂ) u * (szCentroid S - v)).im := by
  have hcard0 : 0 < S.card := by omega
  have hcardC : ((S.card : ℕ) : ℂ) ≠ 0 := by
    have : S.card ≠ 0 := by omega
    exact_mod_cast this
  have hcardR : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hcard0
  have hsum : ((S.card : ℕ) : ℂ) * (szCentroid S - v) = ∑ p ∈ S, (p - v) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, szCentroid]
    field_simp
  have h1 : (starRingEnd ℂ) u * (((S.card : ℕ) : ℂ) * (szCentroid S - v))
      = ∑ p ∈ S, ((starRingEnd ℂ) u * (p - v)) := by
    rw [hsum, Finset.mul_sum]
  have hcast : (starRingEnd ℂ) u * (((S.card : ℕ) : ℂ) * (szCentroid S - v))
      = ((S.card : ℝ) : ℂ) * ((starRingEnd ℂ) u * (szCentroid S - v)) := by
    push_cast
    ring
  have h2 : (S.card : ℝ) * ((starRingEnd ℂ) u * (szCentroid S - v)).im
      = ∑ p ∈ S, ((starRingEnd ℂ) u * (p - v)).im := by
    rw [← Complex.im_sum, ← h1, hcast, Complex.im_ofReal_mul]
  by_contra hcon
  rw [not_lt] at hcon
  have hle : ∑ p ∈ S, ((starRingEnd ℂ) u * (p - v)).im ≤ 0 := by
    rw [← h2]
    nlinarith [mul_nonneg hcardR.le (neg_nonneg.mpr hcon)]
  have hge : 0 ≤ ∑ p ∈ S, ((starRingEnd ℂ) u * (p - v)).im :=
    Finset.sum_nonneg hhalf
  have hz : ∑ p ∈ S, ((starRingEnd ℂ) u * (p - v)).im = 0 := le_antisymm hle hge
  have hall : ∀ p ∈ S, ((starRingEnd ℂ) u * (p - v)).im = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hhalf).mp hz
  refine not_collinear_of_gen hS hgen ?_
  rw [collinear_iff_of_mem (Finset.mem_coe.mpr hv)]
  refine ⟨u, fun p hp => ⟨((starRingEnd ℂ) u * (p - v)).re / Complex.normSq u, ?_⟩⟩
  have h3 := eq_smul_of_im_conj_eq_zero hu (hall p (Finset.mem_coe.mp hp))
  simpa [vadd_eq_add] using (sub_eq_iff_eq_add.mp h3)

/-- The functional `z ↦ (conj u * (z - v)).im` is affine. -/
lemma im_conj_mul_affine (u v x y : ℂ) {s t : ℝ} (hst : s + t = 1) :
    ((starRingEnd ℂ) u * ((s • x + t • y) - v)).im
      = s * ((starRingEnd ℂ) u * (x - v)).im
        + t * ((starRingEnd ℂ) u * (y - v)).im := by
  have hst' : (s : ℂ) + (t : ℂ) = 1 := by exact_mod_cast hst
  have heq : (starRingEnd ℂ) u * ((s • x + t • y) - v)
      = ((s : ℝ) : ℂ) * ((starRingEnd ℂ) u * (x - v))
        + ((t : ℝ) : ℂ) * ((starRingEnd ℂ) u * (y - v)) := by
    simp only [Complex.real_smul]
    linear_combination ((starRingEnd ℂ) u * v) * hst'
  rw [heq, Complex.add_im, Complex.im_ofReal_mul, Complex.im_ofReal_mul]

/-- The same functional applied to a convex combination. -/
lemma im_conj_mul_sum_smul (u v : ℂ) (T : Finset ℂ) (w : ℂ → ℝ)
    (hw : ∑ y ∈ T, w y = 1) :
    ((starRingEnd ℂ) u * ((∑ y ∈ T, w y • y) - v)).im
      = ∑ y ∈ T, w y * ((starRingEnd ℂ) u * (y - v)).im := by
  have hkey : (∑ y ∈ T, w y • y) - v = ∑ y ∈ T, w y • (y - v) := by
    simp only [smul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul, hw, one_smul]
  rw [hkey, Finset.mul_sum, Complex.im_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  have hy : (starRingEnd ℂ) u * (w y • (y - v))
      = ((w y : ℝ) : ℂ) * ((starRingEnd ℂ) u * (y - v)) := by
    rw [Complex.real_smul]
    ring
  rw [hy, Complex.im_ofReal_mul]

/-- A nonzero complex number fixed by a real dilation forces the factor to be `1`. -/
lemma real_smul_eq_self {c : ℝ} {z : ℂ} (hz : z ≠ 0) (h : c • z = z) : c = 1 := by
  rw [Complex.real_smul] at h
  have h1 : ((c : ℝ) : ℂ) * z = (1 : ℂ) * z := by rw [one_mul]; exact h
  have h2 : ((c : ℝ) : ℂ) = 1 := mul_right_cancel₀ hz h1
  exact_mod_cast h2

/-- **The endpoint of a support half-line is an extreme point.**  If `S` lies in
the closed half-plane through `v` with inner normal `u`, and `a` is the only
point of `S` other than `v` on the boundary line, then `a` is an extreme point
of the convex hull of `S`. -/
theorem mem_extremePoints_of_halfline {S : Finset ℂ} {v a u : ℂ}
    (hv : v ∈ S) (ha : a ∈ S) (hav : a ≠ v) (hu : u ≠ 0)
    (hhalf : ∀ q ∈ S, 0 ≤ ((starRingEnd ℂ) u * (q - v)).im)
    (hzero : ((starRingEnd ℂ) u * (a - v)).im = 0)
    (honly : ∀ q ∈ S, ((starRingEnd ℂ) u * (q - v)).im = 0 →
      q = v ∨ q = a) :
    a ∈ (convexHull ℝ (↑S : Set ℂ)).extremePoints ℝ := by
  classical
  have _hu := hu
  -- the closed half-plane is convex and contains the hull
  have hHconv : Convex ℝ {z : ℂ | 0 ≤ ((starRingEnd ℂ) u * (z - v)).im} := by
    intro x hx y hy s t hs ht hst
    have hx' : 0 ≤ ((starRingEnd ℂ) u * (x - v)).im := hx
    have hy' : 0 ≤ ((starRingEnd ℂ) u * (y - v)).im := hy
    show 0 ≤ ((starRingEnd ℂ) u * ((s • x + t • y) - v)).im
    rw [im_conj_mul_affine u v x y hst]
    have h1 := mul_nonneg hs hx'
    have h2 := mul_nonneg ht hy'
    linarith
  have hhull : ∀ x ∈ convexHull ℝ (↑S : Set ℂ),
      0 ≤ ((starRingEnd ℂ) u * (x - v)).im := by
    intro x hx
    have hsub : (↑S : Set ℂ) ⊆ {z : ℂ | 0 ≤ ((starRingEnd ℂ) u * (z - v)).im} :=
      fun p hp => hhalf p (Finset.mem_coe.mp hp)
    exact convexHull_min hsub hHconv hx
  -- the zero set of the functional on the hull is the segment `[v, a]`
  have hface : ∀ x ∈ convexHull ℝ (↑S : Set ℂ),
      ((starRingEnd ℂ) u * (x - v)).im = 0 → x ∈ segment ℝ v a := by
    intro x hx hFx
    rw [Finset.convexHull_eq] at hx
    obtain ⟨w, hw0, hw1, hwx⟩ := hx
    have hxsum : x = ∑ y ∈ S, w y • y := by
      rw [← hwx, Finset.centerMass, hw1]
      simp
    have hF : ∑ y ∈ S, w y * ((starRingEnd ℂ) u * (y - v)).im = 0 := by
      rw [← im_conj_mul_sum_smul u v S w hw1, ← hxsum]
      exact hFx
    have hterm : ∀ y ∈ S, 0 ≤ w y * ((starRingEnd ℂ) u * (y - v)).im :=
      fun y hy => mul_nonneg (hw0 y hy) (hhalf y hy)
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hF
    have hTS : ({v, a} : Finset ℂ) ⊆ S := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact hv
      · exact ha
    have hzero_out : ∀ y ∈ S, y ∉ ({v, a} : Finset ℂ) → w y = 0 := by
      intro y hy hny
      rcases mul_eq_zero.mp (hall y hy) with h | h
      · exact h
      · exfalso
        rcases honly y hy h with rfl | rfl
        · exact hny (by simp)
        · exact hny (by simp)
    have hsum1 : ∑ y ∈ ({v, a} : Finset ℂ), w y = 1 := by
      rw [Finset.sum_subset hTS (fun y hy hny => hzero_out y hy hny)]
      exact hw1
    have hsumx : ∑ y ∈ ({v, a} : Finset ℂ), w y • y = x := by
      rw [Finset.sum_subset hTS
        (fun y hy hny => by rw [hzero_out y hy hny, zero_smul])]
      exact hxsum.symm
    rw [Finset.sum_pair (Ne.symm hav)] at hsum1 hsumx
    exact ⟨w v, w a, hw0 v hv, hw0 a ha, hsum1, hsumx⟩
  -- now the extreme point argument
  rw [mem_extremePoints]
  refine ⟨subset_convexHull ℝ _ (Finset.mem_coe.mpr ha), ?_⟩
  intro x₁ hx₁ x₂ hx₂ hopen
  obtain ⟨s, t, hs, ht, hst, hstx⟩ := hopen
  have hF₁ : 0 ≤ ((starRingEnd ℂ) u * (x₁ - v)).im := hhull x₁ hx₁
  have hF₂ : 0 ≤ ((starRingEnd ℂ) u * (x₂ - v)).im := hhull x₂ hx₂
  have hsplit : s * ((starRingEnd ℂ) u * (x₁ - v)).im
      + t * ((starRingEnd ℂ) u * (x₂ - v)).im = 0 := by
    rw [← im_conj_mul_affine u v x₁ x₂ hst, hstx]
    exact hzero
  have hm1 := mul_nonneg hs.le hF₁
  have hm2 := mul_nonneg ht.le hF₂
  have hF₁0 : ((starRingEnd ℂ) u * (x₁ - v)).im = 0 := by
    have : s * ((starRingEnd ℂ) u * (x₁ - v)).im = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (ne_of_gt hs)
    · exact h
  have hF₂0 : ((starRingEnd ℂ) u * (x₂ - v)).im = 0 := by
    have : t * ((starRingEnd ℂ) u * (x₂ - v)).im = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (ne_of_gt ht)
    · exact h
  have hseg₁ := hface x₁ hx₁ hF₁0
  have hseg₂ := hface x₂ hx₂ hF₂0
  rw [segment_eq_image' ℝ v a] at hseg₁ hseg₂
  obtain ⟨s₁, hs₁mem, hs₁⟩ := hseg₁
  obtain ⟨s₂, hs₂mem, hs₂⟩ := hseg₂
  rw [Set.mem_Icc] at hs₁mem hs₂mem
  have hne : a - v ≠ 0 := sub_ne_zero.mpr hav
  have hst' : (s : ℂ) + (t : ℂ) = 1 := by exact_mod_cast hst
  have hs₁' : v + (s₁ : ℝ) • (a - v) = x₁ := hs₁
  have hs₂' : v + (s₂ : ℝ) • (a - v) = x₂ := hs₂
  have hxx : ((s : ℝ) : ℂ) * (v + ((s₁ : ℝ) : ℂ) * (a - v))
      + ((t : ℝ) : ℂ) * (v + ((s₂ : ℝ) : ℂ) * (a - v)) = a := by
    have e1 : ((s : ℝ) : ℂ) * (v + ((s₁ : ℝ) : ℂ) * (a - v)) = (s : ℝ) • x₁ := by
      rw [← hs₁']
      simp only [Complex.real_smul]
    have e2 : ((t : ℝ) : ℂ) * (v + ((s₂ : ℝ) : ℂ) * (a - v)) = (t : ℝ) • x₂ := by
      rw [← hs₂']
      simp only [Complex.real_smul]
    rw [e1, e2, hstx]
  have hkey : a - v = ((s * s₁ + t * s₂ : ℝ) : ℂ) * (a - v) := by
    push_cast
    linear_combination (-1 : ℂ) * hxx + v * hst'
  have hc : s * s₁ + t * s₂ = 1 := by
    have h1 : ((s * s₁ + t * s₂ : ℝ) : ℂ) * (a - v) = (1 : ℂ) * (a - v) := by
      rw [one_mul]; exact hkey.symm
    have h2 := mul_right_cancel₀ hne h1
    exact_mod_cast h2
  have hsum0 : s * (1 - s₁) + t * (1 - s₂) = 0 := by
    linear_combination hst - hc
  have hn1 : 0 ≤ s * (1 - s₁) := mul_nonneg hs.le (by linarith [hs₁mem.2])
  have hn2 : 0 ≤ t * (1 - s₂) := mul_nonneg ht.le (by linarith [hs₂mem.2])
  have he1 : s₁ = 1 := by
    have h0 : s * (1 - s₁) = 0 := by linarith
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h (ne_of_gt hs)
    · linarith
  have he2 : s₂ = 1 := by
    have h0 : t * (1 - s₂) = 0 := by linarith
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h (ne_of_gt ht)
    · linarith
  subst he1
  subst he2
  have f1 : x₁ = a := by rw [← hs₁']; simp
  have f2 : x₂ = a := by rw [← hs₂']; simp
  exact ⟨f1, f2⟩

/-! ## M4c2b2b1: the empty cone at the centroid -/

/-- Antisymmetry of the oriented area form. -/
lemma im_conj_mul_swap (z w : ℂ) :
    ((starRingEnd ℂ) z * w).im = -(((starRingEnd ℂ) w * z).im) := by
  simp [Complex.mul_im]; ring

/-- The oriented area form vanishes on a repeated argument. -/
lemma im_conj_self (w : ℂ) : ((starRingEnd ℂ) w * w).im = 0 := by
  simp [Complex.mul_im]; ring

/-- **Cramer's rule in the plane.**  If `X` and `Y` are linearly independent,
witnessed by a nonvanishing oriented area, then every `z` decomposes along
them, with the coefficients read off by the area form. -/
lemma exists_decomp_of_im_ne_zero {X Y z : ℂ}
    (hD : ((starRingEnd ℂ) X * Y).im ≠ 0) :
    ∃ p q : ℝ, z = p • X + q • Y ∧
      ((starRingEnd ℂ) X * z).im = q * ((starRingEnd ℂ) X * Y).im ∧
      ((starRingEnd ℂ) Y * z).im = p * ((starRingEnd ℂ) Y * X).im := by
  have hDe : ((starRingEnd ℂ) X * Y).im = X.re * Y.im - X.im * Y.re := by
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = X.re * Y.im - X.im * Y.re := ⟨_, rfl⟩
  have hDne : D ≠ 0 := by rw [hDdef, ← hDe]; exact hD
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p * D = z.re * Y.im - Y.re * z.im :=
    ⟨(z.re * Y.im - Y.re * z.im) / D, div_mul_cancel₀ _ hDne⟩
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q * D = X.re * z.im - z.re * X.im :=
    ⟨(X.re * z.im - z.re * X.im) / D, div_mul_cancel₀ _ hDne⟩
  have e1 : z.re = p * X.re + q * Y.re := by
    apply mul_right_cancel₀ hDne
    linear_combination z.re * hDdef - X.re * hp - Y.re * hq
  have e2 : z.im = p * X.im + q * Y.im := by
    apply mul_right_cancel₀ hDne
    linear_combination z.im * hDdef - X.im * hp - Y.im * hq
  refine ⟨p, q, ?_, ?_, ?_⟩
  · apply Complex.ext
    · simpa [Complex.real_smul] using e1
    · simpa [Complex.real_smul] using e2
  · simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
    linear_combination q * hDdef - hq
  · simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
    linear_combination hp - p * hDdef

/-- The oriented area of the triangle `(c, v, a)`, expressed through the polar
form of the edge `a - v`. -/
lemma im_vc_of_polar {v a c E : ℂ} {r : ℝ} (haform : a - v = (r : ℂ) * E) :
    ((starRingEnd ℂ) (v - c) * (a - c)).im
      = r * ((starRingEnd ℂ) E * (c - v)).im := by
  have hid : (starRingEnd ℂ) (v - c) * (a - c)
      = (r : ℂ) * ((starRingEnd ℂ) (v - c) * E)
        + (starRingEnd ℂ) (v - c) * (v - c) := by
    linear_combination ((starRingEnd ℂ) (v - c)) * haform
  have hswap : ((starRingEnd ℂ) (v - c) * E).im
      = ((starRingEnd ℂ) E * (c - v)).im := by
    rw [im_conj_mul_swap (v - c) E]
    have h : (starRingEnd ℂ) E * (v - c) = -((starRingEnd ℂ) E * (c - v)) := by ring
    rw [h, Complex.neg_im, neg_neg]
  rw [hid, Complex.add_im, Complex.im_ofReal_mul, hswap, im_conj_self, add_zero]

/-- **The empty cone at the centroid.**  Let `S` lie in the closed half-plane
through `v` with inner normal `u`, with `e` on the boundary line.  Then no
extreme point `x ≠ v, e` of `S` can lie in the open cone at the centroid
spanned by the directions of `v` and `e`. -/
theorem not_extreme_in_cone {S : Finset ℂ} (hS : 3 ≤ S.card)
    (hgen : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set ℂ))
    {v e u : ℂ} (hv : v ∈ S) (he : e ∈ S) (hev : e ≠ v) (hu : u ≠ 0)
    (hhalf : ∀ q ∈ S, 0 ≤ ((starRingEnd ℂ) u * (q - v)).im)
    (hzero : ((starRingEnd ℂ) u * (e - v)).im = 0)
    {x : ℂ} (hx : x ∈ extremeFinset S) (hxv : x ≠ v) (hxe : x ≠ e)
    (h₁ : 0 < ((starRingEnd ℂ) (v - szCentroid S) * (x - szCentroid S)).im
            * ((starRingEnd ℂ) (v - szCentroid S) * (e - szCentroid S)).im)
    (h₂ : 0 < ((starRingEnd ℂ) (e - szCentroid S) * (x - szCentroid S)).im
            * ((starRingEnd ℂ) (e - szCentroid S) * (v - szCentroid S)).im) :
    False := by
  have hxS : x ∈ S := mem_of_mem_extremeFinset hx
  have hxext : x ∈ (convexHull ℝ (↑S : Set ℂ)).extremePoints ℝ :=
    mem_extremeFinset.mp hx
  set c := szCentroid S with hcdef
  -- Step 0 : the two directions are independent
  have hDne : ((starRingEnd ℂ) (v - c) * (e - c)).im ≠ 0 := by
    intro h
    rw [h, mul_zero] at h₁
    exact lt_irrefl _ h₁
  obtain ⟨p, q, hdec, hqid, hpid⟩ :=
    exists_decomp_of_im_ne_zero (X := v - c) (Y := e - c) (z := x - c) hDne
  set D := ((starRingEnd ℂ) (v - c) * (e - c)).im with hDdef
  have hswap : ((starRingEnd ℂ) (e - c) * (v - c)).im = -D := by
    rw [hDdef, im_conj_mul_swap (v - c) (e - c), neg_neg]
  -- Step 1 : both coefficients are positive
  have hDD : 0 < D * D := mul_self_pos.mpr hDne
  have hq0 : 0 < q := by rw [hqid] at h₁; nlinarith
  have hp0 : 0 < p := by rw [hpid, hswap] at h₂; nlinarith
  -- Step 2 : the supporting functional bounds the barycentric weight of `c`
  rw [Complex.real_smul, Complex.real_smul] at hdec
  have hFc : 0 < ((starRingEnd ℂ) u * (c - v)).im :=
    im_szCentroid_pos_of_halfline hS hgen hv hu hhalf
  have hxsub : x - v = ((1 - p - q : ℝ) : ℂ) * (c - v) + ((q : ℝ) : ℂ) * (e - v) := by
    push_cast
    linear_combination hdec
  have hFx : ((starRingEnd ℂ) u * (x - v)).im
      = (1 - p - q) * ((starRingEnd ℂ) u * (c - v)).im
        + q * ((starRingEnd ℂ) u * (e - v)).im := by
    have hid : (starRingEnd ℂ) u * (x - v)
        = ((1 - p - q : ℝ) : ℂ) * ((starRingEnd ℂ) u * (c - v))
          + ((q : ℝ) : ℂ) * ((starRingEnd ℂ) u * (e - v)) := by
      linear_combination ((starRingEnd ℂ) u) * hxsub
    rw [hid, Complex.add_im, Complex.im_ofReal_mul, Complex.im_ofReal_mul]
  rw [hzero, mul_zero, add_zero] at hFx
  have hs0 : 0 ≤ 1 - p - q := by
    have h := hhalf x hxS
    rw [hFx] at h
    nlinarith
  rcases lt_or_eq_of_le hs0 with hspos | hseq
  · -- Step 3a : `x` lies strictly between the centroid and a point of `[v, e]`
    have hpq : (0 : ℝ) < p + q := by linarith
    have hpqne : (p + q : ℝ) ≠ 0 := ne_of_gt hpq
    have hvH : v ∈ convexHull ℝ (↑S : Set ℂ) :=
      subset_convexHull ℝ _ (Finset.mem_coe.mpr hv)
    have heH : e ∈ convexHull ℝ (↑S : Set ℂ) :=
      subset_convexHull ℝ _ (Finset.mem_coe.mpr he)
    have hsum1 : p / (p + q) + q / (p + q) = 1 := by field_simp
    have hz₀H : (p / (p + q)) • v + (q / (p + q)) • e ∈ convexHull ℝ (↑S : Set ℂ) :=
      (convex_convexHull ℝ (↑S : Set ℂ)) hvH heH
        (div_nonneg hp0.le hpq.le) (div_nonneg hq0.le hpq.le) hsum1
    have hcH : c ∈ convexHull ℝ (↑S : Set ℂ) := by
      rw [hcdef]; exact szCentroid_mem_convexHull (by omega)
    have hxopen : x ∈ openSegment ℝ c ((p / (p + q)) • v + (q / (p + q)) • e) := by
      refine ⟨1 - p - q, p + q, hspos, hpq, by ring, ?_⟩
      have e1 : (p + q) * (p / (p + q)) = p := by field_simp
      have e2 : (p + q) * (q / (p + q)) = q := by field_simp
      rw [smul_add, smul_smul, smul_smul, e1, e2]
      simp only [Complex.real_smul]
      push_cast
      linear_combination -hdec
    have hcx : c = x := by
      have h := hxext.2 hcH hz₀H hxopen
      tauto
    rw [hcdef] at hcx
    exact extremeFinset_ne_szCentroid hS hx hcx.symm
  · -- Step 3b : `x` lies on the segment `[v, e]`, contradicting general position
    have hq1 : x - v = ((q : ℝ) : ℂ) * (e - v) := by
      rw [hxsub, ← hseq]
      push_cast
      ring
    refine hgen x hxS v hv e he hxv (Ne.symm hev) hxe ?_
    rw [collinear_iff_of_mem (show v ∈ ({x, v, e} : Set ℂ) by simp)]
    refine ⟨e - v, fun z hz => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact ⟨q, by simp only [Complex.real_smul, vadd_eq_add]; linear_combination hq1⟩
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp only [Complex.real_smul, vadd_eq_add]; push_cast; ring⟩

/-- **The start of a support window lies to the left of the centroid.** -/
lemma im_vc_end_pos {S : Finset ℂ} (hS : 3 ≤ S.card)
    (hgen : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set ℂ))
    {v a : ℂ} {θ : ℝ} (hv : v ∈ S) (ha : a ∈ S) (hav : a ≠ v)
    (hhalf : ∀ q ∈ S,
      0 ≤ ((starRingEnd ℂ) (Complex.exp ((θ : ℂ) * Complex.I))
        * (q - v)).im)
    (haform : a - v
      = ((‖a - v‖ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) :
    0 < ((starRingEnd ℂ) (v - szCentroid S) * (a - szCentroid S)).im := by
  have _ha := ha
  have hc := im_szCentroid_pos_of_halfline hS hgen hv
    (Complex.exp_ne_zero ((θ : ℂ) * Complex.I)) hhalf
  have hr : 0 < ‖a - v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hav)
  rw [im_vc_of_polar (c := szCentroid S) haform]
  exact mul_pos hr hc

/-- Reversing the sign of the normal turns a lower half-plane into an upper one. -/
lemma im_conj_neg_mul (w z : ℂ) :
    ((starRingEnd ℂ) (-w) * z).im = -(((starRingEnd ℂ) w * z).im) := by
  rw [map_neg, neg_mul, Complex.neg_im]

/-- **The end of a support window lies to the right of the centroid.** -/
lemma im_vc_end_neg {S : Finset ℂ} (hS : 3 ≤ S.card)
    (hgen : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set ℂ))
    {v b : ℂ} {θ' : ℝ} (hv : v ∈ S) (hb : b ∈ S) (hbv : b ≠ v)
    (hhalf' : ∀ q ∈ S,
      ((starRingEnd ℂ) (Complex.exp ((θ' : ℂ) * Complex.I))
        * (q - v)).im ≤ 0)
    (hbform : b - v
      = ((‖b - v‖ : ℝ) : ℂ) * Complex.exp ((θ' : ℂ) * Complex.I)) :
    ((starRingEnd ℂ) (v - szCentroid S) * (b - szCentroid S)).im < 0 := by
  have _hb := hb
  have hu : -Complex.exp ((θ' : ℂ) * Complex.I) ≠ 0 :=
    neg_ne_zero.mpr (Complex.exp_ne_zero _)
  have hhalf : ∀ q ∈ S, 0 ≤ ((starRingEnd ℂ) (-Complex.exp ((θ' : ℂ) * Complex.I))
      * (q - v)).im := by
    intro q hq
    rw [im_conj_neg_mul]
    exact neg_nonneg.mpr (hhalf' q hq)
  have hc := im_szCentroid_pos_of_halfline hS hgen hv hu hhalf
  rw [im_conj_neg_mul] at hc
  have hc' : ((starRingEnd ℂ) (Complex.exp ((θ' : ℂ) * Complex.I))
      * (szCentroid S - v)).im < 0 := by linarith
  have hr : 0 < ‖b - v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hbv)
  rw [im_vc_of_polar (c := szCentroid S) hbform]
  exact mul_neg_of_pos_of_neg hr hc'

/-! ## M4c2b2b2: cyclic adjacency -/

/-- Polar form of `conj z * w`. -/
lemma conj_mul_polar (z w : ℂ) :
    (starRingEnd ℂ) z * w
      = ((‖z‖ * ‖w‖ : ℝ) : ℂ)
        * Complex.exp (((Complex.arg w - Complex.arg z : ℝ) : ℂ) * Complex.I) := by
  have hw : w = ((‖w‖ : ℝ) : ℂ)
      * Complex.exp (((Complex.arg w : ℝ) : ℂ) * Complex.I) :=
    (Complex.norm_mul_exp_arg_mul_I w).symm
  have hz : z = ((‖z‖ : ℝ) : ℂ)
      * Complex.exp (((Complex.arg z : ℝ) : ℂ) * Complex.I) :=
    (Complex.norm_mul_exp_arg_mul_I z).symm
  have hconj : (starRingEnd ℂ) z = ((‖z‖ : ℝ) : ℂ)
      * Complex.exp (((-Complex.arg z : ℝ) : ℂ) * Complex.I) := by
    conv_lhs => rw [hz]
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    congr 2
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have hadd : Complex.exp (((-Complex.arg z : ℝ) : ℂ) * Complex.I)
      * Complex.exp (((Complex.arg w : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((Complex.arg w - Complex.arg z : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have key : (starRingEnd ℂ) z * w
      = ((‖z‖ : ℝ) : ℂ) * ((‖w‖ : ℝ) : ℂ)
        * Complex.exp (((Complex.arg w - Complex.arg z : ℝ) : ℂ) * Complex.I) := by
    rw [hconj]
    linear_combination
      (((‖z‖ : ℝ) : ℂ) * Complex.exp (((-Complex.arg z : ℝ) : ℂ) * Complex.I)) * hw
      + ((‖z‖ : ℝ) : ℂ) * ((‖w‖ : ℝ) : ℂ) * hadd
  rw [Complex.ofReal_mul]
  exact key

/-- Shifting the exponent by `2π` does not change the exponential. -/
lemma exp_sub_two_pi (φ : ℝ) :
    Complex.exp (((φ - 2 * π : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((φ : ℂ) * Complex.I) := by
  have h : (φ : ℂ) * Complex.I
      = ((φ - 2 * π : ℝ) : ℂ) * Complex.I + (π : ℂ) * Complex.I
        + (π : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_add, Complex.exp_add, Complex.exp_pi_mul_I]
  ring

/-- The argument of `conj z₁ * z₂` is the difference of arguments, when that
difference already lies in the principal range. -/
lemma arg_conj_mul_of_mem {z₁ z₂ : ℂ} (h₁ : z₁ ≠ 0) (h₂ : z₂ ≠ 0)
    (h : Complex.arg z₂ - Complex.arg z₁ ∈ Set.Ioc (-π) π) :
    Complex.arg ((starRingEnd ℂ) z₁ * z₂)
      = Complex.arg z₂ - Complex.arg z₁ := by
  have hr : 0 < ‖z₁‖ * ‖z₂‖ :=
    mul_pos (norm_pos_iff.mpr h₁) (norm_pos_iff.mpr h₂)
  rw [conj_mul_polar, Complex.arg_real_mul _ hr, arg_exp_of_mem h]

/-- The same, when the difference overshoots `π`. -/
lemma arg_conj_mul_of_gt {z₁ z₂ : ℂ} (h₁ : z₁ ≠ 0) (h₂ : z₂ ≠ 0)
    (h : π < Complex.arg z₂ - Complex.arg z₁) :
    Complex.arg ((starRingEnd ℂ) z₁ * z₂)
      = Complex.arg z₂ - Complex.arg z₁ - 2 * π := by
  have hr : 0 < ‖z₁‖ * ‖z₂‖ :=
    mul_pos (norm_pos_iff.mpr h₁) (norm_pos_iff.mpr h₂)
  have hhi := Complex.arg_le_pi z₂
  have hlo := Complex.neg_pi_lt_arg z₁
  have hπ : (0 : ℝ) < π := Real.pi_pos
  rw [conj_mul_polar, Complex.arg_real_mul _ hr,
    ← exp_sub_two_pi (Complex.arg z₂ - Complex.arg z₁),
    arg_exp_of_mem ⟨by linarith, by linarith⟩]

/-- The same, when the difference undershoots `-π`. -/
lemma arg_conj_mul_of_le {z₁ z₂ : ℂ} (h₁ : z₁ ≠ 0) (h₂ : z₂ ≠ 0)
    (h : Complex.arg z₂ - Complex.arg z₁ ≤ -π) :
    Complex.arg ((starRingEnd ℂ) z₁ * z₂)
      = Complex.arg z₂ - Complex.arg z₁ + 2 * π := by
  have hr : 0 < ‖z₁‖ * ‖z₂‖ :=
    mul_pos (norm_pos_iff.mpr h₁) (norm_pos_iff.mpr h₂)
  have hhi := Complex.arg_le_pi z₁
  have hlo := Complex.neg_pi_lt_arg z₂
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hshift : Complex.exp (((Complex.arg z₂ - Complex.arg z₁ : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((Complex.arg z₂ - Complex.arg z₁ + 2 * π : ℝ) : ℂ)
          * Complex.I) := by
    rw [← exp_sub_two_pi (Complex.arg z₂ - Complex.arg z₁ + 2 * π)]
    congr 2
    push_cast
    ring
  rw [conj_mul_polar, Complex.arg_real_mul _ hr, hshift,
    arg_exp_of_mem ⟨by linarith, by linarith⟩]

/-- A point of the open upper half-plane has argument in `(0, π)`. -/
lemma arg_mem_Ioo_of_im_pos {W : ℂ} (h : 0 < W.im) :
    Complex.arg W ∈ Set.Ioo 0 π := by
  constructor
  · rcases lt_or_eq_of_le (Complex.arg_nonneg_iff.mpr h.le) with hlt | heq
    · exact hlt
    · exact absurd (Complex.arg_eq_zero_iff.mp heq.symm).2 (ne_of_gt h)
  · rcases lt_or_eq_of_le (Complex.arg_le_pi W) with hlt | heq
    · exact hlt
    · exact absurd (Complex.arg_eq_pi_iff.mp heq).2 (ne_of_gt h)

/-- Converse of `arg_mem_Ioo_of_im_pos`. -/
lemma im_pos_of_arg_mem_Ioo {W : ℂ} (hW : W ≠ 0)
    (h : Complex.arg W ∈ Set.Ioo 0 π) : 0 < W.im := by
  have hn : 0 < ‖W‖ := norm_pos_iff.mpr hW
  have hs : 0 < Real.sin (Complex.arg W) :=
    Real.sin_pos_of_pos_of_lt_pi h.1 h.2
  rw [Complex.sin_arg] at hs
  exact (div_pos_iff.mp hs).elim (fun hp => hp.1) (fun hp => absurd hp.2 (by linarith))

/-- Argument in `(-π, 0)` forces a negative imaginary part. -/
lemma im_neg_of_arg_mem_Ioo {W : ℂ} (hW : W ≠ 0)
    (h : Complex.arg W ∈ Set.Ioo (-π) 0) : W.im < 0 := by
  have hn : 0 < ‖W‖ := norm_pos_iff.mpr hW
  have hs : 0 < Real.sin (-Complex.arg W) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [h.2]) (by linarith [h.1])
  rw [Real.sin_neg, Complex.sin_arg] at hs
  have hlt : W.im / ‖W‖ < 0 := by linarith
  have heq : W.im = (W.im / ‖W‖) * ‖W‖ := by field_simp
  rw [heq]
  exact mul_neg_of_neg_of_pos hlt hn

/-- Being strictly to the left is detected by the argument of `conj z₁ * z₂`. -/
lemma arg_conj_mul_mem_Ioo {z₁ z₂ : ℂ}
    (h : 0 < ((starRingEnd ℂ) z₁ * z₂).im) :
    Complex.arg ((starRingEnd ℂ) z₁ * z₂) ∈ Set.Ioo 0 π :=
  arg_mem_Ioo_of_im_pos h

/-! ### M2: the adjacency theorems -/

lemma finRotate_val {k : ℕ} (i : Fin k) :
    ((finRotate k i : Fin k) : ℕ) = ((i : ℕ) + 1) % k := by
  match k, i with
  | 0, i => exact i.elim0
  | (m+1), i =>
    rw [coe_finRotate]
    by_cases h : i = Fin.last m
    · subst h; simp
    · rw [if_neg h]
      have hlt : (i : ℕ) < m := Fin.val_lt_last h
      rw [Nat.mod_eq_of_lt (by omega)]

lemma finRotate_val_of_lt {k : ℕ} (i : Fin k) (h : (i : ℕ) + 1 < k) :
    finRotate k i = ⟨(i : ℕ) + 1, h⟩ := by
  apply Fin.ext; rw [finRotate_val, Nat.mod_eq_of_lt h]

lemma finRotate_val_of_last {k : ℕ} (hk : 0 < k) (i : Fin k) (h : (i : ℕ) + 1 = k) :
    finRotate k i = ⟨0, hk⟩ := by
  apply Fin.ext; rw [finRotate_val, h, Nat.mod_self]

noncomputable def cycAdv {k : ℕ} (w : Fin k → ℂ) (c : ℂ) (i l : Fin k) : ℝ :=
  if i < l then Complex.arg (w l - c) - Complex.arg (w i - c)
  else Complex.arg (w l - c) - Complex.arg (w i - c) + 2 * π

/-- On the left-hand side, the argument of `conj (w i - c) * (w l - c)` is the
cyclic advance. -/
lemma arg_conj_eq_cycAdv {S : Finset ℂ} (hS : 3 ≤ S.card)
    {k : ℕ} (w : Fin k → ℂ) (hmem : ∀ i, w i ∈ extremeFinset S)
    (hmono : StrictMono (fun i => Complex.arg (w i - szCentroid S)))
    {i l : Fin k} (hli : l ≠ i)
    (hleft : 0 < ((starRingEnd ℂ) (w i - szCentroid S)
      * (w l - szCentroid S)).im) :
    Complex.arg ((starRingEnd ℂ) (w i - szCentroid S) * (w l - szCentroid S))
      = cycAdv w (szCentroid S) i l := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hne : ∀ j : Fin k, w j - szCentroid S ≠ 0 :=
    fun j => sub_ne_zero.mpr (extremeFinset_ne_szCentroid hS (hmem j))
  have hβ := arg_conj_mul_mem_Ioo hleft
  have hlo : ∀ j : Fin k, -π < Complex.arg (w j - szCentroid S) :=
    fun j => Complex.neg_pi_lt_arg _
  have hhi : ∀ j : Fin k, Complex.arg (w j - szCentroid S) ≤ π :=
    fun j => Complex.arg_le_pi _
  have hlo_i := hlo i; have hhi_i := hhi i
  have hlo_l := hlo l; have hhi_l := hhi l
  rcases lt_or_gt_of_ne hli with hlt | hgt
  · -- `l < i`
    have hmo : Complex.arg (w l - szCentroid S)
        < Complex.arg (w i - szCentroid S) := hmono hlt
    rw [cycAdv, if_neg (by exact not_lt.mpr (le_of_lt hlt))]
    rcases le_or_gt (Complex.arg (w l - szCentroid S)
        - Complex.arg (w i - szCentroid S)) (-π) with hle | hgt'
    · exact arg_conj_mul_of_le (hne i) (hne l) hle
    · rw [arg_conj_mul_of_mem (hne i) (hne l) ⟨hgt', by linarith⟩] at hβ
      linarith [hβ.1]
  · -- `i < l`
    have hmo : Complex.arg (w i - szCentroid S)
        < Complex.arg (w l - szCentroid S) := hmono hgt
    rw [cycAdv, if_pos hgt]
    rcases le_or_gt (Complex.arg (w l - szCentroid S)
        - Complex.arg (w i - szCentroid S)) π with hle | hgt'
    · exact arg_conj_mul_of_mem (hne i) (hne l) ⟨by linarith, hle⟩
    · rw [arg_conj_mul_of_gt (hne i) (hne l) hgt'] at hβ
      linarith [hβ.1]

/-- The cyclic successor realises the minimal advance. -/
lemma cycAdv_succ_lt {k : ℕ} (w : Fin k → ℂ) (c : ℂ)
    (hmono : StrictMono (fun i => Complex.arg (w i - c)))
    (hk3 : 3 ≤ k) (i l : Fin k) (hli : l ≠ i) (hls : l ≠ finRotate k i) :
    cycAdv w c i (finRotate k i) < cycAdv w c i l := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hk : 0 < k := by omega
  have hlo : ∀ j : Fin k, -π < Complex.arg (w j - c) :=
    fun j => Complex.neg_pi_lt_arg _
  have hhi : ∀ j : Fin k, Complex.arg (w j - c) ≤ π :=
    fun j => Complex.arg_le_pi _
  by_cases hcase : (i : ℕ) + 1 < k
  · have hs : finRotate k i = ⟨(i : ℕ) + 1, hcase⟩ := finRotate_val_of_lt i hcase
    have hilt : i < finRotate k i := by
      rw [hs, Fin.lt_def]; exact Nat.lt_succ_self _
    rw [cycAdv, if_pos hilt]
    rcases lt_or_gt_of_ne hli with hlt | hgt
    · rw [cycAdv, if_neg (not_lt.mpr hlt.le)]
      have h1 := hlo l
      have h2 := hhi (finRotate k i)
      linarith
    · rw [cycAdv, if_pos hgt]
      have hsl : finRotate k i < l := by
        rw [hs, Fin.lt_def]
        show (i : ℕ) + 1 < (l : ℕ)
        have hil : (i : ℕ) < (l : ℕ) := Fin.lt_def.mp hgt
        have hne : (l : ℕ) ≠ (i : ℕ) + 1 := by
          intro h
          exact hls (Fin.ext (by rw [h, hs]))
        omega
      have := hmono hsl
      simp only at this
      linarith
  · have heq : (i : ℕ) + 1 = k := by have := i.isLt; omega
    have hs : finRotate k i = ⟨0, hk⟩ := finRotate_val_of_last hk i heq
    have hnlt : ¬ (i < finRotate k i) := by
      rw [hs, Fin.lt_def]
      show ¬ ((i : ℕ) < 0)
      omega
    rw [cycAdv, if_neg hnlt]
    have hlt : l < i := by
      rcases lt_or_gt_of_ne hli with h | h
      · exact h
      · have := Fin.lt_def.mp h
        have := l.isLt
        omega
    rw [cycAdv, if_neg (not_lt.mpr hlt.le)]
    have hsl : finRotate k i < l := by
      rw [hs, Fin.lt_def]
      show 0 < (l : ℕ)
      rcases Nat.eq_zero_or_pos (l : ℕ) with h0 | hpos
      · exact absurd (Fin.ext (show (l : ℕ) = ((⟨0, hk⟩ : Fin k) : ℕ) from h0))
          (by rw [← hs]; exact hls)
      · exact hpos
    have := hmono hsl
    simp only at this
    linarith

/-- The advance to the cyclic successor is realised by the argument, and lies
strictly between `0` and `π`. -/
lemma arg_conj_succ {S : Finset ℂ} (hS : 3 ≤ S.card)
    (hgen : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set ℂ))
    {k : ℕ} (w : Fin k → ℂ)
    (hmem : ∀ i, w i ∈ extremeFinset S)
    (hsur : ∀ v ∈ extremeFinset S, ∃ i, w i = v)
    (hmono : StrictMono (fun i => Complex.arg (w i - szCentroid S)))
    (hk3 : 3 ≤ k) (i : Fin k) :
    Complex.arg ((starRingEnd ℂ) (w i - szCentroid S)
        * (w (finRotate k i) - szCentroid S))
      = cycAdv w (szCentroid S) i (finRotate k i)
    ∧ cycAdv w (szCentroid S) i (finRotate k i) ∈ Set.Ioo 0 π := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hk : 0 < k := by omega
  have hne : ∀ j : Fin k, w j - szCentroid S ≠ 0 :=
    fun j => sub_ne_zero.mpr (extremeFinset_ne_szCentroid hS (hmem j))
  have hgap := argGap_lt_pi hS hgen w hmem hsur hmono hk
  have hlo : ∀ j : Fin k, -π < Complex.arg (w j - szCentroid S) :=
    fun j => Complex.neg_pi_lt_arg _
  have hhi : ∀ j : Fin k, Complex.arg (w j - szCentroid S) ≤ π :=
    fun j => Complex.arg_le_pi _
  by_cases hcase : (i : ℕ) + 1 < k
  · have hs : finRotate k i = ⟨(i : ℕ) + 1, hcase⟩ := finRotate_val_of_lt i hcase
    have hilt : i < finRotate k i := by
      rw [hs, Fin.lt_def]; exact Nat.lt_succ_self _
    have hmo := hmono hilt
    simp only at hmo
    have hgap1 := hgap.1 (i : ℕ) hcase
    rw [show (⟨(i : ℕ), by omega⟩ : Fin k) = i from Fin.eta _ _] at hgap1
    have hub : Complex.arg (w (finRotate k i) - szCentroid S)
        - Complex.arg (w i - szCentroid S) < π := by rw [hs]; exact hgap1
    rw [cycAdv, if_pos hilt]
    exact ⟨arg_conj_mul_of_mem (hne i) (hne _) ⟨by linarith, by linarith⟩,
      ⟨by linarith, by linarith⟩⟩
  · have heq : (i : ℕ) + 1 = k := by have := i.isLt; omega
    have hs : finRotate k i = ⟨0, hk⟩ := finRotate_val_of_last hk i heq
    have hnlt : ¬ (i < finRotate k i) := by
      rw [hs, Fin.lt_def]
      show ¬ ((i : ℕ) < 0)
      omega
    have hgap2 := hgap.2
    rw [show (⟨k - 1, by omega⟩ : Fin k) = i from Fin.ext (by show k - 1 = (i : ℕ); omega)] at hgap2
    rw [← hs] at hgap2
    rw [cycAdv, if_neg hnlt]
    have hle : Complex.arg (w (finRotate k i) - szCentroid S)
        - Complex.arg (w i - szCentroid S) ≤ -π := by linarith
    refine ⟨arg_conj_mul_of_le (hne i) (hne _) hle, ?_, ?_⟩
    · have h1 := hlo (finRotate k i)
      have h2 := hhi i
      linarith
    · linarith

/-- The sine of the difference of the arguments only depends on the difference
of the cyclic advances. -/
lemma sin_sub_arg_eq_sin_sub_cycAdv {k : ℕ} (w : Fin k → ℂ) (c : ℂ) (i j l : Fin k) :
    Real.sin (Complex.arg (w j - c) - Complex.arg (w l - c))
      = Real.sin (cycAdv w c i j - cycAdv w c i l) := by
  by_cases hij : i < j <;> by_cases hil : i < l
  · rw [cycAdv, cycAdv, if_pos hij, if_pos hil]
    congr 1
    ring
  · rw [cycAdv, cycAdv, if_pos hij, if_neg hil,
      show (Complex.arg (w j - c) - Complex.arg (w i - c))
          - (Complex.arg (w l - c) - Complex.arg (w i - c) + 2 * π)
        = (Complex.arg (w j - c) - Complex.arg (w l - c)) - 2 * π from by ring,
      Real.sin_sub_two_pi]
  · rw [cycAdv, cycAdv, if_neg hij, if_pos hil,
      show (Complex.arg (w j - c) - Complex.arg (w i - c) + 2 * π)
          - (Complex.arg (w l - c) - Complex.arg (w i - c))
        = (Complex.arg (w j - c) - Complex.arg (w l - c)) + 2 * π from by ring,
      Real.sin_add_two_pi]
  · rw [cycAdv, cycAdv, if_neg hij, if_neg hil]
    congr 1
    ring

/-- If `w j` advances strictly less than `w l`, then `w j` lies to the right of
`w l` as seen from the centre. -/
lemma im_conj_mul_neg_of_cycAdv_lt {k : ℕ} (w : Fin k → ℂ) (c : ℂ) (i j l : Fin k)
    (hj : cycAdv w c i j ∈ Set.Ioo 0 π) (hl : cycAdv w c i l ∈ Set.Ioo 0 π)
    (hlt : cycAdv w c i j < cycAdv w c i l)
    (hnj : w j - c ≠ 0) (hnl : w l - c ≠ 0) :
    ((starRingEnd ℂ) (w l - c) * (w j - c)).im < 0 := by
  rw [im_conj_mul, sin_sub_arg_eq_sin_sub_cycAdv w c i j l]
  have hsin : Real.sin (cycAdv w c i j - cycAdv w c i l) < 0 := by
    have h1 : 0 < cycAdv w c i l - cycAdv w c i j := by linarith
    have h2 : cycAdv w c i l - cycAdv w c i j < π := by
      have := hj.1; have := hl.2; linarith
    have := Real.sin_pos_of_pos_of_lt_pi h1 h2
    rw [show cycAdv w c i j - cycAdv w c i l
        = -(cycAdv w c i l - cycAdv w c i j) from by ring, Real.sin_neg]
    linarith
  have hnormj : 0 < ‖w j - c‖ := norm_pos_iff.mpr hnj
  have hnorml : 0 < ‖w l - c‖ := norm_pos_iff.mpr hnl
  exact mul_neg_of_pos_of_neg (mul_pos hnorml hnormj) hsin

lemma conj_exp_mul_exp (θ t : ℝ) :
    (starRingEnd ℂ) (Complex.exp ((θ : ℂ) * Complex.I))
      * Complex.exp (((θ + t : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((t : ℂ) * Complex.I) := by
  have hconj : (starRingEnd ℂ) (Complex.exp ((θ : ℂ) * Complex.I))
      = Complex.exp ((-(θ : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [hconj, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma im_conj_exp_mul_polar {v q : ℂ} {θ t r : ℝ}
    (h : q - v = (r : ℂ) * Complex.exp (((θ + t : ℝ) : ℂ) * Complex.I)) :
    ((starRingEnd ℂ) (Complex.exp ((θ : ℂ) * Complex.I)) * (q - v)).im
      = r * Real.sin t := by
  have hkey : (starRingEnd ℂ) (Complex.exp ((θ : ℂ) * Complex.I)) * (q - v)
      = ((r : ℝ) : ℂ) * Complex.exp ((t : ℂ) * Complex.I) := by
    rw [h, ← conj_exp_mul_exp θ t]
    ring
  rw [hkey, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]

/-- The window puts all of `S` in the closed half-plane of its start direction. -/
lemma window_half {S : Finset ℂ} {v : ℂ} {θ A : ℝ} (hA : A < π)
    (hwin : ∀ q ∈ S, q ≠ v → ∃ r t : ℝ, 0 < r ∧ 0 ≤ t ∧ t ≤ A ∧
      q - v = (r : ℂ) * Complex.exp (((θ + t : ℝ) : ℂ) * Complex.I)) :
    ∀ q ∈ S, 0 ≤ ((starRingEnd ℂ) (Complex.exp ((θ : ℂ) * Complex.I))
      * (q - v)).im := by
  intro q hq
  by_cases hqv : q = v
  · rw [hqv, sub_self, mul_zero, Complex.zero_im]
  · obtain ⟨r, t, hr, ht0, htA, hform⟩ := hwin q hq hqv
    rw [im_conj_exp_mul_polar hform]
    exact mul_nonneg hr.le
      (Real.sin_nonneg_of_nonneg_of_le_pi ht0 (by linarith))

/-- The start of the window lies on the boundary line. -/
lemma window_zero {v a : ℂ} {θ : ℝ}
    (haform : a - v = ((‖a - v‖ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) :
    ((starRingEnd ℂ) (Complex.exp ((θ : ℂ) * Complex.I)) * (a - v)).im = 0 := by
  have h : a - v = ((‖a - v‖ : ℝ) : ℂ)
      * Complex.exp (((θ + 0 : ℝ) : ℂ) * Complex.I) := by
    rw [haform]
    norm_num
  rw [im_conj_exp_mul_polar h, Real.sin_zero, mul_zero]

/-- In general position, `a` is the only point of `S` other than `v` on the
boundary line of the window. -/
lemma window_only {S : Finset ℂ}
    (hgen : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set ℂ))
    {v a : ℂ} {θ A : ℝ} (hA : A < π) (hv : v ∈ S) (ha : a ∈ S) (hav : a ≠ v)
    (hwin : ∀ q ∈ S, q ≠ v → ∃ r t : ℝ, 0 < r ∧ 0 ≤ t ∧ t ≤ A ∧
      q - v = (r : ℂ) * Complex.exp (((θ + t : ℝ) : ℂ) * Complex.I))
    (haform : a - v = ((‖a - v‖ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) :
    ∀ q ∈ S, ((starRingEnd ℂ) (Complex.exp ((θ : ℂ) * Complex.I))
      * (q - v)).im = 0 → q = v ∨ q = a := by
  intro q hq hz
  by_cases hqv : q = v
  · exact Or.inl hqv
  refine Or.inr ?_
  obtain ⟨r, t, hr, ht0, htA, hform⟩ := hwin q hq hqv
  rw [im_conj_exp_mul_polar hform] at hz
  have hsin : Real.sin t = 0 := by
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd h (ne_of_gt hr)
    · exact h
  have ht : t = 0 := by
    by_contra hne
    have hpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm hne)
    have := Real.sin_pos_of_pos_of_lt_pi hpos (by linarith)
    linarith
  subst ht
  have hq' : q - v = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [hform]
    norm_num
  have hnorm : 0 < ‖a - v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hav)
  by_contra hqa
  refine hgen q hq v hv a ha hqv (Ne.symm hav) hqa ?_
  rw [collinear_iff_of_mem (show v ∈ ({q, v, a} : Set ℂ) by simp)]
  refine ⟨a - v, fun z hz' => ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz'
  have hnormC : ((‖a - v‖ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hnorm
  rcases hz' with rfl | rfl | rfl
  · refine ⟨r / ‖a - v‖, ?_⟩
    simp only [Complex.real_smul, vadd_eq_add, Complex.ofReal_div]
    field_simp
    linear_combination ((‖a - v‖ : ℝ) : ℂ) * hq' - (r : ℂ) * haform
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp only [Complex.real_smul, vadd_eq_add]; push_cast; ring⟩

lemma finRotate_ne_self {k : ℕ} (hk3 : 3 ≤ k) (i : Fin k) : finRotate k i ≠ i := by
  intro h
  have hval : ((i : ℕ) + 1) % k = (i : ℕ) := by rw [← finRotate_val, h]
  have hik := i.isLt
  rcases Nat.lt_or_ge ((i : ℕ) + 1) k with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at hval; omega
  · have he : (i : ℕ) + 1 = k := by omega
    rw [he, Nat.mod_self] at hval; omega

lemma conj_mul_ne_zero {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) :
    (starRingEnd ℂ) z * w ≠ 0 := by
  refine mul_ne_zero ?_ hw
  intro h
  exact hz (by simpa using congrArg (starRingEnd ℂ) h)

/-- **The cyclic successor is the start of the window.** -/
theorem succ_eq_window_start {S : Finset ℂ} (hS : 3 ≤ S.card)
    (hgen : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set ℂ))
    {k : ℕ} (w : Fin k → ℂ)
    (hmem : ∀ i, w i ∈ extremeFinset S)
    (hsur : ∀ v ∈ extremeFinset S, ∃ i, w i = v)
    (hmono : StrictMono (fun i => Complex.arg (w i - szCentroid S)))
    (hk : 0 < k) (hk3 : 3 ≤ k) (i : Fin k)
    {θ A : ℝ} {a : ℂ} (haS : a ∈ S) (hav : a ≠ w i) (hA : A < π)
    (hwin : ∀ q ∈ S, q ≠ w i → ∃ r t : ℝ, 0 < r ∧ 0 ≤ t ∧ t ≤ A ∧
      q - w i = (r : ℂ) * Complex.exp (((θ + t : ℝ) : ℂ) * Complex.I))
    (haform : a - w i
      = ((‖a - w i‖ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) :
    w (finRotate k i) = a := by
  have _hk := hk
  have hviS : w i ∈ S := mem_of_mem_extremeFinset (hmem i)
  have hne : ∀ j : Fin k, w j - szCentroid S ≠ 0 :=
    fun j => sub_ne_zero.mpr (extremeFinset_ne_szCentroid hS (hmem j))
  have hwinj : Function.Injective w := fun x y hxy =>
    hmono.injective (show (fun j => Complex.arg (w j - szCentroid S)) x
      = (fun j => Complex.arg (w j - szCentroid S)) y from by simp only [hxy])
  have hhalf := window_half hA hwin
  have hzero := window_zero haform
  have honly := window_only hgen hA hviS haS hav hwin haform
  have haE : a ∈ extremeFinset S :=
    mem_extremeFinset.mpr (mem_extremePoints_of_halfline hviS haS hav
      (Complex.exp_ne_zero _) hhalf hzero honly)
  have haleft : 0 < ((starRingEnd ℂ) (w i - szCentroid S)
      * (a - szCentroid S)).im :=
    im_vc_end_pos hS hgen hviS haS hav hhalf haform
  obtain ⟨l, hl⟩ := hsur a haE
  have hli : l ≠ i := by
    intro h
    rw [h] at hl
    exact hav hl.symm
  by_cases hls : l = finRotate k i
  · rw [← hls, hl]
  exfalso
  obtain ⟨hβs, hIoo⟩ := arg_conj_succ hS hgen w hmem hsur hmono hk3 i
  have hβl : Complex.arg ((starRingEnd ℂ) (w i - szCentroid S)
      * (w l - szCentroid S)) = cycAdv w (szCentroid S) i l :=
    arg_conj_eq_cycAdv hS w hmem hmono hli (by rw [hl]; exact haleft)
  have hlIoo : cycAdv w (szCentroid S) i l ∈ Set.Ioo 0 π := by
    rw [← hβl]
    exact arg_conj_mul_mem_Ioo (by rw [hl]; exact haleft)
  have hstrict := cycAdv_succ_lt w (szCentroid S) hmono hk3 i l hli hls
  have hxleft : 0 < ((starRingEnd ℂ) (w i - szCentroid S)
      * (w (finRotate k i) - szCentroid S)).im := by
    refine im_pos_of_arg_mem_Ioo (conj_mul_ne_zero (hne i) (hne _)) ?_
    rw [hβs]
    exact hIoo
  have hxa : ((starRingEnd ℂ) (a - szCentroid S)
      * (w (finRotate k i) - szCentroid S)).im < 0 := by
    rw [← hl]
    exact im_conj_mul_neg_of_cycAdv_lt w (szCentroid S) i (finRotate k i) l
      hIoo hlIoo hstrict (hne _) (hne l)
  have hav' : ((starRingEnd ℂ) (a - szCentroid S)
      * (w i - szCentroid S)).im < 0 := by
    rw [im_conj_mul_swap]
    linarith
  have hxv : w (finRotate k i) ≠ w i := by
    intro h
    exact finRotate_ne_self hk3 i (hwinj h)
  have hxe : w (finRotate k i) ≠ a := by
    rw [← hl]
    intro h
    exact hls (hwinj h).symm
  exact not_extreme_in_cone hS hgen hviS haS hav (Complex.exp_ne_zero _)
    hhalf hzero (hmem _) hxv hxe (mul_pos hxleft haleft)
    (mul_pos_of_neg_of_neg hxa hav')

lemma finRotate_symm_of_pos {k : ℕ} (i : Fin k) (h : 0 < (i : ℕ)) :
    (finRotate k).symm i = ⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ := by
  rw [Equiv.symm_apply_eq]
  rw [finRotate_val_of_lt _ (by have := i.isLt; show (i : ℕ) - 1 + 1 < k; omega)]
  exact Fin.ext (by show (i : ℕ) = (i : ℕ) - 1 + 1; omega)

lemma finRotate_symm_of_zero {k : ℕ} (hk : 0 < k) (i : Fin k) (h : (i : ℕ) = 0) :
    (finRotate k).symm i = ⟨k - 1, by omega⟩ := by
  rw [Equiv.symm_apply_eq]
  rw [finRotate_val_of_last hk _ (by show k - 1 + 1 = k; omega)]
  exact Fin.ext (by show (i : ℕ) = 0; omega)

/-- Dual form of `sin_sub_arg_eq_sin_sub_cycAdv`, with a common *target*. -/
lemma sin_sub_arg_eq_sin_sub_cycAdv' {k : ℕ} (w : Fin k → ℂ) (c : ℂ)
    (i j l : Fin k) :
    Real.sin (Complex.arg (w j - c) - Complex.arg (w l - c))
      = Real.sin (cycAdv w c l i - cycAdv w c j i) := by
  by_cases hli : l < i <;> by_cases hji : j < i
  · rw [cycAdv, cycAdv, if_pos hli, if_pos hji]
    congr 1
    ring
  · rw [cycAdv, cycAdv, if_pos hli, if_neg hji,
      show (Complex.arg (w i - c) - Complex.arg (w l - c))
          - (Complex.arg (w i - c) - Complex.arg (w j - c) + 2 * π)
        = (Complex.arg (w j - c) - Complex.arg (w l - c)) - 2 * π from by ring,
      Real.sin_sub_two_pi]
  · rw [cycAdv, cycAdv, if_neg hli, if_pos hji,
      show (Complex.arg (w i - c) - Complex.arg (w l - c) + 2 * π)
          - (Complex.arg (w i - c) - Complex.arg (w j - c))
        = (Complex.arg (w j - c) - Complex.arg (w l - c)) + 2 * π from by ring,
      Real.sin_add_two_pi]
  · rw [cycAdv, cycAdv, if_neg hli, if_neg hji]
    congr 1
    ring

/-- If `w j` retreats strictly less than `w l`, then `w j` lies to the left of
`w l` as seen from the centre. -/
lemma im_conj_mul_pos_of_cycAdv_lt {k : ℕ} (w : Fin k → ℂ) (c : ℂ) (i j l : Fin k)
    (hj : cycAdv w c j i ∈ Set.Ioo 0 π) (hl : cycAdv w c l i ∈ Set.Ioo 0 π)
    (hlt : cycAdv w c j i < cycAdv w c l i)
    (hnj : w j - c ≠ 0) (hnl : w l - c ≠ 0) :
    0 < ((starRingEnd ℂ) (w l - c) * (w j - c)).im := by
  rw [im_conj_mul, sin_sub_arg_eq_sin_sub_cycAdv' w c i j l]
  have hsin : 0 < Real.sin (cycAdv w c l i - cycAdv w c j i) := by
    refine Real.sin_pos_of_pos_of_lt_pi (by linarith) ?_
    have := hj.1; have := hl.2; linarith
  have hnormj : 0 < ‖w j - c‖ := norm_pos_iff.mpr hnj
  have hnorml : 0 < ‖w l - c‖ := norm_pos_iff.mpr hnl
  exact mul_pos (mul_pos hnorml hnormj) hsin

/-- The cyclic predecessor realises the minimal retreat. -/
lemma cycAdv_pred_lt {k : ℕ} (w : Fin k → ℂ) (c : ℂ)
    (hmono : StrictMono (fun i => Complex.arg (w i - c)))
    (hk3 : 3 ≤ k) (i j : Fin k) (hji : j ≠ i)
    (hjp : j ≠ (finRotate k).symm i) :
    cycAdv w c ((finRotate k).symm i) i < cycAdv w c j i := by
  have _hji := hji
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hk : 0 < k := by omega
  have hlo : ∀ m : Fin k, -π < Complex.arg (w m - c) :=
    fun m => Complex.neg_pi_lt_arg _
  have hhi : ∀ m : Fin k, Complex.arg (w m - c) ≤ π :=
    fun m => Complex.arg_le_pi _
  by_cases hcase : 0 < (i : ℕ)
  · have hp : (finRotate k).symm i = ⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ :=
      finRotate_symm_of_pos i hcase
    have hpi : (finRotate k).symm i < i := by
      rw [hp, Fin.lt_def]
      show (i : ℕ) - 1 < (i : ℕ)
      omega
    rw [cycAdv, if_pos hpi]
    by_cases hjlt : j < i
    · rw [cycAdv, if_pos hjlt]
      have hjp' : j < (finRotate k).symm i := by
        rw [hp, Fin.lt_def]
        show (j : ℕ) < (i : ℕ) - 1
        have h1 : (j : ℕ) < (i : ℕ) := Fin.lt_def.mp hjlt
        have h2 : (j : ℕ) ≠ (i : ℕ) - 1 := by
          intro h
          exact hjp (by rw [hp]; exact Fin.ext (by show (j : ℕ) = (i : ℕ) - 1; omega))
        omega
      have := hmono hjp'
      simp only at this
      linarith
    · rw [cycAdv, if_neg hjlt]
      have h1 := hhi j
      have h2 := hlo ((finRotate k).symm i)
      linarith
  · have hi0 : (i : ℕ) = 0 := by omega
    have hp : (finRotate k).symm i = ⟨k - 1, by omega⟩ :=
      finRotate_symm_of_zero hk i hi0
    have hpi : ¬ ((finRotate k).symm i < i) := by
      rw [hp, Fin.lt_def]
      show ¬ (k - 1 < (i : ℕ))
      omega
    rw [cycAdv, if_neg hpi]
    have hjlt : ¬ (j < i) := by
      rw [Fin.lt_def]
      show ¬ ((j : ℕ) < (i : ℕ))
      omega
    rw [cycAdv, if_neg hjlt]
    have hjp' : j < (finRotate k).symm i := by
      rw [hp, Fin.lt_def]
      show (j : ℕ) < k - 1
      have h1 := j.isLt
      have h2 : (j : ℕ) ≠ k - 1 := by
        intro h
        exact hjp (by rw [hp]; exact Fin.ext (by show (j : ℕ) = k - 1; omega))
      omega
    have := hmono hjp'
    simp only at this
    linarith

/-- The window puts all of `S` in the closed half-plane of its end direction. -/
lemma window_half' {S : Finset ℂ} {v : ℂ} {θ A : ℝ} (hA : A < π)
    (hwin : ∀ q ∈ S, q ≠ v → ∃ r t : ℝ, 0 < r ∧ 0 ≤ t ∧ t ≤ A ∧
      q - v = (r : ℂ) * Complex.exp (((θ + t : ℝ) : ℂ) * Complex.I)) :
    ∀ q ∈ S, ((starRingEnd ℂ) (Complex.exp (((θ + A : ℝ) : ℂ) * Complex.I))
      * (q - v)).im ≤ 0 := by
  intro q hq
  by_cases hqv : q = v
  · rw [hqv, sub_self, mul_zero, Complex.zero_im]
  · obtain ⟨r, t, hr, ht0, htA, hform⟩ := hwin q hq hqv
    have hform' : q - v
        = (r : ℂ) * Complex.exp ((((θ + A) + (t - A) : ℝ) : ℂ) * Complex.I) := by
      rw [show ((θ + A) + (t - A) : ℝ) = θ + t from by ring]
      exact hform
    rw [im_conj_exp_mul_polar hform']
    have hsin : Real.sin (t - A) ≤ 0 := by
      rw [show t - A = -(A - t) from by ring, Real.sin_neg, neg_nonpos]
      exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    nlinarith

/-- In general position, `b` is the only point of `S` other than `v` on the
end line of the window. -/
lemma window_only' {S : Finset ℂ}
    (hgen : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set ℂ))
    {v b : ℂ} {θ A : ℝ} (hA : A < π) (hv : v ∈ S) (hb : b ∈ S) (hbv : b ≠ v)
    (hwin : ∀ q ∈ S, q ≠ v → ∃ r t : ℝ, 0 < r ∧ 0 ≤ t ∧ t ≤ A ∧
      q - v = (r : ℂ) * Complex.exp (((θ + t : ℝ) : ℂ) * Complex.I))
    (hbform : b - v = ((‖b - v‖ : ℝ) : ℂ)
      * Complex.exp (((θ + A : ℝ) : ℂ) * Complex.I)) :
    ∀ q ∈ S, ((starRingEnd ℂ) (Complex.exp (((θ + A : ℝ) : ℂ) * Complex.I))
      * (q - v)).im = 0 → q = v ∨ q = b := by
  intro q hq hz
  by_cases hqv : q = v
  · exact Or.inl hqv
  refine Or.inr ?_
  obtain ⟨r, t, hr, ht0, htA, hform⟩ := hwin q hq hqv
  have hform' : q - v
      = (r : ℂ) * Complex.exp ((((θ + A) + (t - A) : ℝ) : ℂ) * Complex.I) := by
    rw [show ((θ + A) + (t - A) : ℝ) = θ + t from by ring]
    exact hform
  rw [im_conj_exp_mul_polar hform'] at hz
  have hsin : Real.sin (t - A) = 0 := by
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd h (ne_of_gt hr)
    · exact h
  have ht : t = A := by
    by_contra hne
    have hpos : 0 < A - t := lt_of_le_of_ne (by linarith) (by intro h; exact hne (by linarith))
    have hs := Real.sin_pos_of_pos_of_lt_pi hpos (by linarith)
    rw [show t - A = -(A - t) from by ring, Real.sin_neg] at hsin
    linarith
  subst ht
  have hq' : q - v = (r : ℂ) * Complex.exp (((θ + t : ℝ) : ℂ) * Complex.I) := hform
  have hnorm : 0 < ‖b - v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hbv)
  by_contra hqb
  refine hgen q hq v hv b hb hqv (Ne.symm hbv) hqb ?_
  rw [collinear_iff_of_mem (show v ∈ ({q, v, b} : Set ℂ) by simp)]
  refine ⟨b - v, fun z hz' => ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz'
  have hnormC : ((‖b - v‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hnorm
  rcases hz' with rfl | rfl | rfl
  · refine ⟨r / ‖b - v‖, ?_⟩
    simp only [Complex.real_smul, vadd_eq_add, Complex.ofReal_div]
    field_simp
    linear_combination ((‖b - v‖ : ℝ) : ℂ) * hq' - (r : ℂ) * hbform
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp only [Complex.real_smul, vadd_eq_add]; push_cast; ring⟩

/-- **The cyclic predecessor is the end of the window.** -/
theorem pred_eq_window_end {S : Finset ℂ} (hS : 3 ≤ S.card)
    (hgen : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set ℂ))
    {k : ℕ} (w : Fin k → ℂ)
    (hmem : ∀ i, w i ∈ extremeFinset S)
    (hsur : ∀ v ∈ extremeFinset S, ∃ i, w i = v)
    (hmono : StrictMono (fun i => Complex.arg (w i - szCentroid S)))
    (hk : 0 < k) (hk3 : 3 ≤ k) (i : Fin k)
    {θ A : ℝ} {b : ℂ} (hbS : b ∈ S) (hbv : b ≠ w i) (hA : A < π)
    (hwin : ∀ q ∈ S, q ≠ w i → ∃ r t : ℝ, 0 < r ∧ 0 ≤ t ∧ t ≤ A ∧
      q - w i = (r : ℂ) * Complex.exp (((θ + t : ℝ) : ℂ) * Complex.I))
    (hbform : b - w i
      = ((‖b - w i‖ : ℝ) : ℂ)
        * Complex.exp (((θ + A : ℝ) : ℂ) * Complex.I)) :
    w ((finRotate k).symm i) = b := by
  have _hk := hk
  have hviS : w i ∈ S := mem_of_mem_extremeFinset (hmem i)
  have hne : ∀ j : Fin k, w j - szCentroid S ≠ 0 :=
    fun j => sub_ne_zero.mpr (extremeFinset_ne_szCentroid hS (hmem j))
  have hwinj : Function.Injective w := fun x y hxy =>
    hmono.injective (show (fun j => Complex.arg (w j - szCentroid S)) x
      = (fun j => Complex.arg (w j - szCentroid S)) y from by simp only [hxy])
  have hhalf' := window_half' hA hwin
  have hzero' := window_zero hbform
  have honly' := window_only' hgen hA hviS hbS hbv hwin hbform
  have hhalfu : ∀ q ∈ S, 0 ≤ ((starRingEnd ℂ)
      (-Complex.exp (((θ + A : ℝ) : ℂ) * Complex.I)) * (q - w i)).im := by
    intro q hq
    rw [im_conj_neg_mul]
    exact neg_nonneg.mpr (hhalf' q hq)
  have hzerou : ((starRingEnd ℂ)
      (-Complex.exp (((θ + A : ℝ) : ℂ) * Complex.I)) * (b - w i)).im = 0 := by
    rw [im_conj_neg_mul, hzero', neg_zero]
  have honlyu : ∀ q ∈ S, ((starRingEnd ℂ)
      (-Complex.exp (((θ + A : ℝ) : ℂ) * Complex.I)) * (q - w i)).im = 0 →
      q = w i ∨ q = b := by
    intro q hq h
    rw [im_conj_neg_mul, neg_eq_zero] at h
    exact honly' q hq h
  have hbE : b ∈ extremeFinset S :=
    mem_extremeFinset.mpr (mem_extremePoints_of_halfline hviS hbS hbv
      (neg_ne_zero.mpr (Complex.exp_ne_zero _)) hhalfu hzerou honlyu)
  have hright : ((starRingEnd ℂ) (w i - szCentroid S)
      * (b - szCentroid S)).im < 0 :=
    im_vc_end_neg hS hgen hviS hbS hbv hhalf' hbform
  obtain ⟨m, hm⟩ := hsur b hbE
  have hmi : m ≠ i := by
    intro h
    rw [h] at hm
    exact hbv hm.symm
  obtain ⟨p, hpdef⟩ : ∃ p : Fin k, p = (finRotate k).symm i := ⟨_, rfl⟩
  rw [← hpdef]
  by_cases hmp : m = p
  · rw [← hmp]; exact hm
  exfalso
  have hfp : finRotate k p = i := by
    rw [hpdef]; exact Equiv.apply_symm_apply (finRotate k) i
  obtain ⟨hβp, hIoop⟩ := arg_conj_succ hS hgen w hmem hsur hmono hk3 p
  rw [hfp] at hβp hIoop
  have hleftm : 0 < ((starRingEnd ℂ) (w m - szCentroid S)
      * (w i - szCentroid S)).im := by
    rw [im_conj_mul_swap, hm]
    linarith
  have hβm : Complex.arg ((starRingEnd ℂ) (w m - szCentroid S)
      * (w i - szCentroid S)) = cycAdv w (szCentroid S) m i :=
    arg_conj_eq_cycAdv hS w hmem hmono (Ne.symm hmi) hleftm
  have hIoom : cycAdv w (szCentroid S) m i ∈ Set.Ioo 0 π := by
    rw [← hβm]
    exact arg_conj_mul_mem_Ioo hleftm
  have hstrict : cycAdv w (szCentroid S) p i < cycAdv w (szCentroid S) m i := by
    rw [hpdef]
    exact cycAdv_pred_lt w (szCentroid S) hmono hk3 i m hmi
      (by rw [← hpdef]; exact hmp)
  have hpleft : 0 < ((starRingEnd ℂ) (w p - szCentroid S)
      * (w i - szCentroid S)).im := by
    refine im_pos_of_arg_mem_Ioo (conj_mul_ne_zero (hne p) (hne i)) ?_
    rw [hβp]
    exact hIoop
  have hpi_neg : ((starRingEnd ℂ) (w i - szCentroid S)
      * (w p - szCentroid S)).im < 0 := by
    rw [im_conj_mul_swap]
    linarith
  have hmp_pos : 0 < ((starRingEnd ℂ) (w m - szCentroid S)
      * (w p - szCentroid S)).im :=
    im_conj_mul_pos_of_cycAdv_lt w (szCentroid S) i p m hIoop hIoom hstrict
      (hne p) (hne m)
  have hxv : w p ≠ w i := by
    intro h
    have hpi : p = i := hwinj h
    rw [hpi] at hfp
    exact finRotate_ne_self hk3 i hfp
  have hxe : w p ≠ b := by
    rw [← hm]
    intro h
    exact hmp (hwinj h).symm
  exact not_extreme_in_cone hS hgen hviS hbS hbv
    (neg_ne_zero.mpr (Complex.exp_ne_zero _)) hhalfu hzerou (hmem p) hxv hxe
    (mul_pos_of_neg_of_neg hpi_neg hright)
    (mul_pos (by rw [← hm]; exact hmp_pos) (by rw [← hm]; exact hleftm))

/-! ## M4c3: the master rigidity theorem -/

/-- In window coordinates the Euclidean angle at the vertex is the difference
of the angular coordinates. -/
lemma angle_eq_abs_of_polar {v q₁ q₂ : ℂ} {θ t₁ t₂ r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (ht : |t₁ - t₂| < π)
    (h₁ : q₁ - v = (r₁ : ℂ) * Complex.exp (((θ + t₁ : ℝ) : ℂ) * Complex.I))
    (h₂ : q₂ - v = (r₂ : ℂ) * Complex.exp (((θ + t₂ : ℝ) : ℂ) * Complex.I)) :
    EuclideanGeometry.angle q₁ v q₂ = |t₁ - t₂| := by
  have hbridge : EuclideanGeometry.angle q₁ v q₂
      = InnerProductGeometry.angle (q₁ - v) (q₂ - v) := by
    simp [EuclideanGeometry.angle, vsub_eq_sub]
  have hne₁ : q₁ - v ≠ 0 := by
    rw [h₁]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hr₁))
      (Complex.exp_ne_zero _)
  have hne₂ : q₂ - v ≠ 0 := by
    rw [h₂]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hr₂))
      (Complex.exp_ne_zero _)
  have hexp : (starRingEnd ℂ) (Complex.exp (((θ + t₁ : ℝ) : ℂ) * Complex.I))
      * Complex.exp (((θ + t₂ : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((t₂ - t₁ : ℝ) : ℂ) * Complex.I) := by
    have h := conj_exp_mul_exp (θ + t₁) (t₂ - t₁)
    rw [show ((θ + t₁) + (t₂ - t₁) : ℝ) = θ + t₂ from by ring] at h
    exact h
  have hkey : (starRingEnd ℂ) (q₁ - v) * (q₂ - v)
      = ((r₁ * r₂ : ℝ) : ℂ) * Complex.exp (((t₂ - t₁ : ℝ) : ℂ) * Complex.I) := by
    rw [h₁, h₂, map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
    linear_combination ((r₁ : ℂ) * (r₂ : ℂ)) * hexp
  have habs := abs_lt.mp ht
  rw [hbridge, angle_eq_abs_arg hne₁ hne₂, hkey,
    Complex.arg_real_mul _ (mul_pos hr₁ hr₂),
    arg_exp_of_mem ⟨by linarith [habs.2], by linarith [habs.1]⟩, abs_sub_comm]

lemma exp_mul_conj_exp (θ : ℝ) :
    Complex.exp ((θ : ℂ) * Complex.I)
      * (starRingEnd ℂ) (Complex.exp ((θ : ℂ) * Complex.I)) = 1 := by
  have h := conj_exp_mul_exp θ 0
  rw [add_zero] at h
  rw [mul_comm, h]
  norm_num

/-- **The centroid is seen strictly inside the window.** -/
lemma centroid_window_coord {S : Finset ℂ} (hS : 3 ≤ S.card)
    (hgen : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set ℂ))
    {v : ℂ} {θ A : ℝ} (hv : v ∈ S) (hA0 : 0 ≤ A) (hA : A < π)
    (hwin : ∀ q ∈ S, q ≠ v → ∃ r t : ℝ, 0 < r ∧ 0 ≤ t ∧ t ≤ A ∧
      q - v = (r : ℂ) * Complex.exp (((θ + t : ℝ) : ℂ) * Complex.I)) :
    ∃ tc : ℝ, 0 < tc ∧ tc < A ∧
      szCentroid S - v = ((‖szCentroid S - v‖ : ℝ) : ℂ)
        * Complex.exp (((θ + tc : ℝ) : ℂ) * Complex.I) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hhalf := window_half hA hwin
  have hc : 0 < ((starRingEnd ℂ) (Complex.exp ((θ : ℂ) * Complex.I))
      * (szCentroid S - v)).im :=
    im_szCentroid_pos_of_halfline hS hgen hv (Complex.exp_ne_zero _) hhalf
  obtain ⟨z, hzdef⟩ : ∃ z : ℂ, z = (starRingEnd ℂ) (Complex.exp ((θ : ℂ) * Complex.I))
      * (szCentroid S - v) := ⟨_, rfl⟩
  rw [← hzdef] at hc
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, Complex.zero_im] at hc
    exact lt_irrefl _ hc
  have htc := arg_mem_Ioo_of_im_pos hc
  have hEz : szCentroid S - v = Complex.exp ((θ : ℂ) * Complex.I) * z := by
    rw [hzdef, ← mul_assoc, exp_mul_conj_exp, one_mul]
  have hnorm : ‖szCentroid S - v‖ = ‖z‖ := by
    rw [hEz, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hnormpos : 0 < ‖szCentroid S - v‖ := by
    rw [hnorm]
    exact norm_pos_iff.mpr hz0
  have hpolar : szCentroid S - v = ((‖szCentroid S - v‖ : ℝ) : ℂ)
      * Complex.exp (((θ + Complex.arg z : ℝ) : ℂ) * Complex.I) := by
    rw [hnorm, hEz]
    conv_lhs => rw [Complex.norm_mul_exp_arg_mul_I z |>.symm]
    rw [show ((θ + Complex.arg z : ℝ) : ℂ) * Complex.I
        = (θ : ℂ) * Complex.I + ((Complex.arg z : ℝ) : ℂ) * Complex.I from by
          push_cast; ring, Complex.exp_add]
    ring
  refine ⟨Complex.arg z, htc.1, ?_, hpolar⟩
  have hhalf' := window_half' hA hwin
  have hhalfu : ∀ q ∈ S, 0 ≤ ((starRingEnd ℂ)
      (-Complex.exp (((θ + A : ℝ) : ℂ) * Complex.I)) * (q - v)).im := by
    intro q hq
    rw [im_conj_neg_mul]
    exact neg_nonneg.mpr (hhalf' q hq)
  have hcneg := im_szCentroid_pos_of_halfline hS hgen hv
    (neg_ne_zero.mpr (Complex.exp_ne_zero _)) hhalfu
  rw [im_conj_neg_mul] at hcneg
  have hpolar' : szCentroid S - v = ((‖szCentroid S - v‖ : ℝ) : ℂ)
      * Complex.exp ((((θ + A) + (Complex.arg z - A) : ℝ) : ℂ) * Complex.I) := by
    rw [show ((θ + A) + (Complex.arg z - A) : ℝ) = θ + Complex.arg z from by ring]
    exact hpolar
  rw [im_conj_exp_mul_polar hpolar'] at hcneg
  have hsinneg : Real.sin (Complex.arg z - A) < 0 := by nlinarith
  by_contra hcon
  rw [not_lt] at hcon
  have hnn : 0 ≤ Real.sin (Complex.arg z - A) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [htc.2])
  linarith

lemma exp_add_int_two_pi (x : ℝ) (m : ℤ) :
    Complex.exp (((x + 2 * π * m : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((x : ℂ) * Complex.I) := by
  rw [show ((x + 2 * π * m : ℝ) : ℂ) * Complex.I
      = (x : ℂ) * Complex.I + (m : ℂ) * (2 * (π : ℂ) * Complex.I) from by
        push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **The rotation rule.**  Reversing an edge turns the direction by `π`. -/
lemma edge_rotation_rule {v v' : ℂ} {θ θ' A' ℓ ℓ' : ℝ} (hℓ : 0 < ℓ) (hℓ' : 0 < ℓ')
    (hsucc : v' - v = (ℓ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
    (hpred : v - v' = (ℓ' : ℂ)
      * Complex.exp (((θ' + A' : ℝ) : ℂ) * Complex.I)) :
    ∃ m : ℤ, θ' + A' = θ + π + 2 * π * m := by
  have hn1 : ‖v' - v‖ = ℓ := by
    rw [hsucc, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hℓ]
  have hn2 : ‖v - v'‖ = ℓ' := by
    rw [hpred, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hℓ']
  have hll : ℓ' = ℓ := by
    rw [← hn1, ← hn2, ← norm_neg (v - v')]
    congr 1
    ring
  have hneg : v - v' = (ℓ : ℂ) * Complex.exp (((θ + π : ℝ) : ℂ) * Complex.I) := by
    rw [← neg_exp_eq, show v - v' = -(v' - v) from by ring, hsucc]
    ring
  have hexp : Complex.exp (((θ' + A' : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((θ + π : ℝ) : ℂ) * Complex.I) := by
    have h : (ℓ : ℂ) * Complex.exp (((θ' + A' : ℝ) : ℂ) * Complex.I)
        = (ℓ : ℂ) * Complex.exp (((θ + π : ℝ) : ℂ) * Complex.I) := by
      rw [← hneg, hpred, hll]
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt hℓ)) h
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
  refine ⟨m, ?_⟩
  have h2 : ((θ' + A' : ℝ) : ℂ) = ((θ + π : ℝ) : ℂ) + (m : ℂ) * (2 * (π : ℂ)) := by
    apply mul_right_cancel₀ Complex.I_ne_zero
    linear_combination hm
  push_cast at h2
  have h3 : ((θ' + A' : ℝ) : ℂ) = ((θ + π + 2 * π * m : ℝ) : ℂ) := by
    push_cast
    linear_combination h2
  exact_mod_cast h3

/-- The cyclic advance of the centroid direction between consecutive vertices,
in terms of the two windows. -/
lemma arg_conj_centroid_succ {v v' c : ℂ} {θ A t θ' A' t' ρ ρ' : ℝ} {m : ℤ}
    (hA : A < π) (hA' : A' < π) (ht0 : 0 < t) (htA : t < A)
    (ht'0 : 0 < t') (ht'A : t' < A')
    (hcv : c - v = (ρ : ℂ) * Complex.exp (((θ + t : ℝ) : ℂ) * Complex.I))
    (hcv' : c - v' = (ρ' : ℂ)
      * Complex.exp (((θ' + t' : ℝ) : ℂ) * Complex.I))
    (hρ : 0 < ρ) (hρ' : 0 < ρ')
    (hrot : θ' + A' = θ + π + 2 * π * m) :
    Complex.arg ((starRingEnd ℂ) (v - c) * (v' - c)) = π - A' + t' - t := by
  have hexp : (starRingEnd ℂ) (Complex.exp (((θ + t : ℝ) : ℂ) * Complex.I))
      * Complex.exp (((θ' + t' : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((π - A' + t' - t : ℝ) : ℂ) * Complex.I) := by
    have h := conj_exp_mul_exp (θ + t) ((θ' + t') - (θ + t))
    rw [show ((θ + t) + ((θ' + t') - (θ + t)) : ℝ) = θ' + t' from by ring] at h
    rw [h, show ((θ' + t') - (θ + t) : ℝ) = (π - A' + t' - t) + 2 * π * m from by
      linarith, exp_add_int_two_pi]
  have hkey : (starRingEnd ℂ) (v - c) * (v' - c)
      = ((ρ * ρ' : ℝ) : ℂ)
        * Complex.exp (((π - A' + t' - t : ℝ) : ℂ) * Complex.I) := by
    have h1 : (starRingEnd ℂ) (v - c) * (v' - c)
        = (starRingEnd ℂ) (c - v) * (c - v') := by
      rw [show v - c = -(c - v) from by ring, show v' - c = -(c - v') from by ring,
        map_neg, neg_mul, mul_neg, neg_neg]
    rw [h1, hcv, hcv', map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
    linear_combination ((ρ : ℂ) * (ρ' : ℂ)) * hexp
  rw [hkey, Complex.arg_real_mul _ (mul_pos hρ hρ'),
    arg_exp_of_mem ⟨by linarith, by linarith⟩]

/-- The cyclic advances around the centroid sum to a full turn. -/
lemma sum_cycAdv_succ {k : ℕ} (hk3 : 3 ≤ k) (w : Fin k → ℂ) (c : ℂ) :
    ∑ i : Fin k, cycAdv w c i (finRotate k i) = 2 * π := by
  have hk1 : k - 1 < k := by omega
  have hval : ∀ i : Fin k, cycAdv w c i (finRotate k i)
      = (Complex.arg (w (finRotate k i) - c) - Complex.arg (w i - c))
        + (if i = (⟨k - 1, hk1⟩ : Fin k) then 2 * π else 0) := by
    intro i
    have hi := i.isLt
    by_cases h : (i : ℕ) + 1 < k
    · have hlt : i < finRotate k i := by
        rw [finRotate_val_of_lt i h, Fin.lt_def]
        exact Nat.lt_succ_self _
      have hne : i ≠ (⟨k - 1, hk1⟩ : Fin k) := by
        intro hc
        have : (i : ℕ) = k - 1 := by rw [hc]
        omega
      rw [cycAdv, if_pos hlt, if_neg hne, add_zero]
    · have heq : (i : ℕ) + 1 = k := by omega
      have hnlt : ¬ (i < finRotate k i) := by
        rw [finRotate_val_of_last (by omega) i heq, Fin.lt_def]
        show ¬ ((i : ℕ) < 0)
        omega
      have hie : i = (⟨k - 1, hk1⟩ : Fin k) := Fin.ext (by show (i : ℕ) = k - 1; omega)
      rw [cycAdv, if_neg hnlt, if_pos hie]
  rw [Finset.sum_congr rfl (fun i _ => hval i), Finset.sum_add_distrib,
    Finset.sum_sub_distrib,
    Equiv.sum_comp (finRotate k) (fun j => Complex.arg (w j - c))]
  simp

lemma conj_exp_eq (θ : ℝ) :
    (starRingEnd ℂ) (Complex.exp ((θ : ℂ) * Complex.I))
      = Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

lemma finCongr_symm_finRotate {k m : ℕ} (h : k = m) (j : Fin m) :
    (finCongr h).symm (finRotate m j) = finRotate k ((finCongr h).symm j) := by
  subst h
  simp

lemma finCongr_symm_finRotate_symm {k m : ℕ} (h : k = m) (j : Fin m) :
    (finCongr h).symm ((finRotate m).symm j)
      = (finRotate k).symm ((finCongr h).symm j) := by
  subst h
  simp

/-- Main step of the master rigidity theorem, with the sorted enumeration of
the extreme points supplied. -/
theorem master_rigidity_aux {n : ℕ} (hn : 3 ≤ n) {S : Finset ℂ}
    (hcard : S.card = 2 ^ n)
    (hangle : ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
      EuclideanGeometry.angle p q r ≤ (1 - 1 / (n : ℝ)) * π)
    (hgen : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set ℂ))
    (hS3 : 3 ≤ S.card)
    {k : ℕ} (w₀ : Fin k → ℂ)
    (hmem : ∀ i, w₀ i ∈ extremeFinset S)
    (hsur : ∀ v ∈ extremeFinset S, ∃ i, w₀ i = v)
    (hmono : StrictMono (fun i => Complex.arg (w₀ i - szCentroid S)))
    (hk3 : 3 ≤ k) :
    ∃ (w : Fin (2 * n) → ℂ) (θ : Fin (2 * n) → ℝ),
      Function.Injective w ∧ (∀ i, w i ∈ S) ∧
      (∀ i, ∀ q ∈ S, q ≠ w i → ∃ r t : ℝ, 0 < r ∧ 0 ≤ t ∧
        t ≤ (1 - 1 / (n : ℝ)) * π ∧
        q - w i = (r : ℂ)
          * Complex.exp (((θ i + t : ℝ) : ℂ) * Complex.I)) ∧
      (∀ i, w (finRotate (2 * n) i) - w i
        = ((‖w (finRotate (2 * n) i) - w i‖ : ℝ) : ℂ)
          * Complex.exp ((θ i : ℂ) * Complex.I)) ∧
      (∀ i, w ((finRotate (2 * n)).symm i) - w i
        = ((‖w ((finRotate (2 * n)).symm i) - w i‖ : ℝ) : ℂ)
          * Complex.exp
            (((θ i + (1 - 1 / (n : ℝ)) * π : ℝ) : ℂ) * Complex.I)) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hnR3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hinv : 0 < 1 / (n : ℝ) := by positivity
  have hinv1 : 1 / (n : ℝ) < 1 := by
    rw [div_lt_one hnR]; linarith
  have hWlt : (1 - 1 / (n : ℝ)) * π < π := by nlinarith
  have hW0 : 0 < (1 - 1 / (n : ℝ)) * π := by nlinarith
  have hk : 0 < k := by omega
  have hwmemS : ∀ i, w₀ i ∈ S := fun i => mem_of_mem_extremeFinset (hmem i)
  have hwinj : Function.Injective w₀ := fun x y hxy =>
    hmono.injective (show (fun j => Complex.arg (w₀ j - szCentroid S)) x
      = (fun j => Complex.arg (w₀ j - szCentroid S)) y from by simp only [hxy])
  have hexne : ∀ v : ℂ, ∃ q ∈ S, q ≠ v := by
    intro v
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
    by_cases h : a = v
    · exact ⟨b, hb, by rw [← h]; exact Ne.symm hab⟩
    · exact ⟨a, ha, h⟩
  have hwin_ex : ∀ i : Fin k, ∃ θ A : ℝ, 0 ≤ A ∧ A < π ∧
      (∀ q ∈ S, q ≠ w₀ i → ∃ r t : ℝ, 0 < r ∧ 0 ≤ t ∧ t ≤ A ∧
        q - w₀ i = (r : ℂ) * Complex.exp (((θ + t : ℝ) : ℂ) * Complex.I)) ∧
      (∃ a ∈ S, a ≠ w₀ i ∧ a - w₀ i = ((‖a - w₀ i‖ : ℝ) : ℂ)
        * Complex.exp ((θ : ℂ) * Complex.I)) ∧
      (∃ b ∈ S, b ≠ w₀ i ∧ b - w₀ i = ((‖b - w₀ i‖ : ℝ) : ℂ)
        * Complex.exp (((θ + A : ℝ) : ℂ) * Complex.I)) := fun i =>
    exists_window_at_extreme (hwmemS i) (hexne _) (mem_extremeFinset.mp (hmem i))
  choose θ A hA0 hAπ hwin hstart hend using hwin_ex
  have hsuccne : ∀ i : Fin k, w₀ (finRotate k i) ≠ w₀ i :=
    fun i h => finRotate_ne_self hk3 i (hwinj h)
  have hpredidx : ∀ i : Fin k, (finRotate k).symm i ≠ i := by
    intro i h
    have h2 : finRotate k i = i := by
      have h3 := Equiv.apply_symm_apply (finRotate k) i
      rw [h] at h3
      exact h3
    exact finRotate_ne_self hk3 i h2
  have hpredne : ∀ i : Fin k, w₀ ((finRotate k).symm i) ≠ w₀ i :=
    fun i h => hpredidx i (hwinj h)
  have hsuccval : ∀ i : Fin k, w₀ (finRotate k i) - w₀ i
      = ((‖w₀ (finRotate k i) - w₀ i‖ : ℝ) : ℂ)
        * Complex.exp ((θ i : ℂ) * Complex.I) := by
    intro i
    obtain ⟨a, haS, hav, haform⟩ := hstart i
    rw [succ_eq_window_start hS3 hgen w₀ hmem hsur hmono hk hk3 i haS hav
      (hAπ i) (hwin i) haform]
    exact haform
  have hpredval : ∀ i : Fin k, w₀ ((finRotate k).symm i) - w₀ i
      = ((‖w₀ ((finRotate k).symm i) - w₀ i‖ : ℝ) : ℂ)
        * Complex.exp (((θ i + A i : ℝ) : ℂ) * Complex.I) := by
    intro i
    obtain ⟨b, hbS, hbv, hbform⟩ := hend i
    rw [pred_eq_window_end hS3 hgen w₀ hmem hsur hmono hk hk3 i hbS hbv
      (hAπ i) (hwin i) hbform]
    exact hbform
  have hAangle : ∀ i : Fin k, EuclideanGeometry.angle (w₀ (finRotate k i)) (w₀ i)
      (w₀ ((finRotate k).symm i)) = A i := by
    intro i
    have h := angle_eq_abs_of_polar (v := w₀ i) (θ := θ i) (t₁ := 0) (t₂ := A i)
      (hr₁ := norm_pos_iff.mpr (sub_ne_zero.mpr (hsuccne i)))
      (hr₂ := norm_pos_iff.mpr (sub_ne_zero.mpr (hpredne i)))
      (ht := by rw [zero_sub, abs_neg, abs_of_nonneg (hA0 i)]; exact hAπ i)
      (h₁ := by rw [add_zero]; exact hsuccval i) (h₂ := hpredval i)
    rw [h, zero_sub, abs_neg, abs_of_nonneg (hA0 i)]
  have hAle : ∀ i : Fin k, A i ≤ (1 - 1 / (n : ℝ)) * π := by
    intro i
    rw [← hAangle i]
    exact hangle _ (hwmemS _) _ (hwmemS i) _ (hwmemS _) (hsuccne i) (hpredne i)
  -- the window cannot be strictly narrower than `(1 - 1/n)·π`
  have hAge : ∀ i : Fin k, (1 - 1 / (n : ℝ)) * π ≤ A i := by
    intro i
    by_contra hcon
    rw [not_le] at hcon
    have hu0 : Complex.exp (((-(θ i) : ℝ) : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    have hinj : Function.Injective
        (fun z => Complex.exp (((-(θ i) : ℝ) : ℂ) * Complex.I) * z) :=
      fun x y h => mul_left_cancel₀ hu0 h
    have hcard' : (S.image
        (fun z => Complex.exp (((-(θ i) : ℝ) : ℂ) * Complex.I) * z)).card = 2 ^ n := by
      rw [Finset.card_image_of_injective _ hinj, hcard]
    have hangle' : ∀ p ∈ S.image
        (fun z => Complex.exp (((-(θ i) : ℝ) : ℂ) * Complex.I) * z),
        ∀ q ∈ S.image (fun z => Complex.exp (((-(θ i) : ℝ) : ℂ) * Complex.I) * z),
        ∀ r ∈ S.image (fun z => Complex.exp (((-(θ i) : ℝ) : ℂ) * Complex.I) * z),
        p ≠ q → r ≠ q →
        EuclideanGeometry.angle p q r ≤ (1 - 1 / (n : ℝ)) * π := by
      intro p hp q hq r hr hpq hrq
      rw [Finset.mem_image] at hp hq hr
      obtain ⟨p', hp', rfl⟩ := hp
      obtain ⟨q', hq', rfl⟩ := hq
      obtain ⟨r', hr', rfl⟩ := hr
      rw [euclidean_angle_const_mul hu0]
      exact hangle p' hp' q' hq' r' hr' (fun h => hpq (by rw [h]))
        (fun h => hrq (by rw [h]))
    have hpmem : Complex.exp (((-(θ i) : ℝ) : ℂ) * Complex.I) * w₀ i ∈ S.image
        (fun z => Complex.exp (((-(θ i) : ℝ) : ℂ) * Complex.I) * z) :=
      Finset.mem_image_of_mem _ (hwmemS i)
    have hdir : ∀ q ∈ S.image (fun z => Complex.exp (((-(θ i) : ℝ) : ℂ) * Complex.I) * z),
        q ≠ Complex.exp (((-(θ i) : ℝ) : ℂ) * Complex.I) * w₀ i →
        0 ≤ Complex.arg (q - Complex.exp (((-(θ i) : ℝ) : ℂ) * Complex.I) * w₀ i) ∧
          Complex.arg (q - Complex.exp (((-(θ i) : ℝ) : ℂ) * Complex.I) * w₀ i)
            ≤ A i := by
      intro q hq hqp
      rw [Finset.mem_image] at hq
      obtain ⟨q', hq', rfl⟩ := hq
      have hq'ne : q' ≠ w₀ i := fun h => hqp (by rw [h])
      obtain ⟨r, t, hr, ht0, htA, hform⟩ := hwin i q' hq' hq'ne
      have hkey : Complex.exp (((-(θ i) : ℝ) : ℂ) * Complex.I) * q'
          - Complex.exp (((-(θ i) : ℝ) : ℂ) * Complex.I) * w₀ i
          = (r : ℂ) * Complex.exp ((t : ℂ) * Complex.I) := by
        rw [← mul_sub, hform, ← conj_exp_eq]
        linear_combination (r : ℂ) * conj_exp_mul_exp (θ i) t
      rw [hkey, Complex.arg_real_mul _ hr,
        arg_exp_of_mem ⟨by linarith, by linarith [hAπ i]⟩]
      exact ⟨ht0, htA⟩
    exact no_small_cone hn0 hcard' hangle' hpmem hcon hdir
  have hAeq : ∀ i : Fin k, A i = (1 - 1 / (n : ℝ)) * π :=
    fun i => le_antisymm (hAle i) (hAge i)
  -- the centroid direction inside each window
  have hcne : ∀ i : Fin k, szCentroid S - w₀ i ≠ 0 := by
    intro i
    exact sub_ne_zero.mpr (fun h =>
      extremeFinset_ne_szCentroid hS3 (hmem i) h.symm)
  have hρ : ∀ i : Fin k, 0 < ‖szCentroid S - w₀ i‖ :=
    fun i => norm_pos_iff.mpr (hcne i)
  have htc_ex : ∀ i : Fin k, ∃ tc : ℝ, 0 < tc ∧ tc < A i ∧
      szCentroid S - w₀ i = ((‖szCentroid S - w₀ i‖ : ℝ) : ℂ)
        * Complex.exp (((θ i + tc : ℝ) : ℂ) * Complex.I) :=
    fun i => centroid_window_coord hS3 hgen (hwmemS i) (hA0 i) (hAπ i) (hwin i)
  choose tc htc0 htcA htcform using htc_ex
  -- the rotation rule
  have hrot : ∀ i : Fin k, ∃ m : ℤ,
      θ (finRotate k i) + A (finRotate k i) = θ i + π + 2 * π * m := by
    intro i
    have hps : (finRotate k).symm (finRotate k i) = i := Equiv.symm_apply_apply _ _
    have h2 := hpredval (finRotate k i)
    rw [hps] at h2
    exact edge_rotation_rule
      (norm_pos_iff.mpr (sub_ne_zero.mpr (hsuccne i)))
      (norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => (hsuccne i) h.symm)))
      (hsuccval i) h2
  -- the cyclic advance of the centroid direction
  have hcyc : ∀ i : Fin k, cycAdv w₀ (szCentroid S) i (finRotate k i)
      = π - A (finRotate k i) + tc (finRotate k i) - tc i := by
    intro i
    obtain ⟨m, hm⟩ := hrot i
    rw [← (arg_conj_succ hS3 hgen w₀ hmem hsur hmono hk3 i).1]
    exact arg_conj_centroid_succ (hAπ i) (hAπ _) (htc0 i) (htcA i) (htc0 _)
      (htcA _) (htcform i) (htcform _) (hρ i) (hρ _) hm
  -- summing around the cycle gives `k = 2n`
  have hsum : ∑ i : Fin k, cycAdv w₀ (szCentroid S) i (finRotate k i) = 2 * π :=
    sum_cycAdv_succ hk3 w₀ (szCentroid S)
  have hsum2 : ∑ i : Fin k,
      (π - (1 - 1 / (n : ℝ)) * π + tc (finRotate k i) - tc i) = 2 * π := by
    rw [← hsum]
    exact (Finset.sum_congr rfl (fun i _ => by rw [hcyc i, hAeq])).symm
  have htcsum : ∑ i : Fin k, tc (finRotate k i) = ∑ i : Fin k, tc i :=
    Equiv.sum_comp (finRotate k) tc
  have hexpand : ∑ i : Fin k,
      (π - (1 - 1 / (n : ℝ)) * π + tc (finRotate k i) - tc i)
      = (k : ℝ) * (π - (1 - 1 / (n : ℝ)) * π)
        + (∑ i : Fin k, tc (finRotate k i)) - ∑ i : Fin k, tc i := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hexpand, htcsum] at hsum2
  have hpiovern : π - (1 - 1 / (n : ℝ)) * π = π / n := by
    field_simp
    ring
  rw [hpiovern] at hsum2
  have hkn : k = 2 * n := by
    have h1 : (k : ℝ) = 2 * n := by
      have h2 : (k : ℝ) * π = 2 * n * π := by
        field_simp at hsum2
        linarith
      exact mul_right_cancel₀ (ne_of_gt hπ) h2
    exact_mod_cast h1
  -- transport the data along `k = 2 * n`
  refine ⟨fun j => w₀ ((finCongr hkn).symm j),
    fun j => θ ((finCongr hkn).symm j), ?_, ?_, ?_, ?_, ?_⟩
  · exact fun x y h => (finCongr hkn).symm.injective (hwinj h)
  · exact fun j => hwmemS _
  · intro j q hq hqj
    obtain ⟨r, t, hr, ht0, htA, hform⟩ := hwin ((finCongr hkn).symm j) q hq hqj
    refine ⟨r, t, hr, ht0, ?_, hform⟩
    rw [← hAeq ((finCongr hkn).symm j)]
    exact htA
  · intro j
    dsimp only
    rw [finCongr_symm_finRotate hkn j]
    exact hsuccval _
  · intro j
    dsimp only
    rw [finCongr_symm_finRotate_symm hkn j, ← hAeq ((finCongr hkn).symm j)]
    exact hpredval _

/-- **The master rigidity theorem.**  If a set of `2 ^ n` points has all angles
at most `(1 - 1/n)·π`, then its extreme points form a `2n`-gon whose window at
each vertex has opening exactly `(1 - 1/n)·π`. -/
theorem master_rigidity {n : ℕ} (hn : 3 ≤ n) {S : Finset ℂ}
    (hcard : S.card = 2 ^ n)
    (hangle : ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
      EuclideanGeometry.angle p q r ≤ (1 - 1 / (n : ℝ)) * π) :
    ∃ (w : Fin (2 * n) → ℂ) (θ : Fin (2 * n) → ℝ),
      Function.Injective w ∧ (∀ i, w i ∈ S) ∧
      (∀ i, ∀ q ∈ S, q ≠ w i → ∃ r t : ℝ, 0 < r ∧ 0 ≤ t ∧
        t ≤ (1 - 1 / (n : ℝ)) * π ∧
        q - w i = (r : ℂ)
          * Complex.exp (((θ i + t : ℝ) : ℂ) * Complex.I)) ∧
      (∀ i, w (finRotate (2 * n) i) - w i
        = ((‖w (finRotate (2 * n) i) - w i‖ : ℝ) : ℂ)
          * Complex.exp ((θ i : ℂ) * Complex.I)) ∧
      (∀ i, w ((finRotate (2 * n)).symm i) - w i
        = ((‖w ((finRotate (2 * n)).symm i) - w i‖ : ℝ) : ℂ)
          * Complex.exp
            (((θ i + (1 - 1 / (n : ℝ)) * π : ℝ) : ℂ) * Complex.I)) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hnR3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hinv : 0 < 1 / (n : ℝ) := by positivity
  have hWlt : (1 - 1 / (n : ℝ)) * π < π := by nlinarith
  have hS3 : 3 ≤ S.card := by
    rw [hcard]
    calc (3 : ℕ) ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hgen : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set ℂ) := by
    intro a ha b hb c hc hab hbc hac hcol
    rcases exists_angle_eq_pi_of_collinear hab hbc hac hcol with h | h | h
    · have h2 := hangle a ha b hb c hc hab (Ne.symm hbc)
      rw [h] at h2; linarith
    · have h2 := hangle b hb a ha c hc (Ne.symm hab) (Ne.symm hac)
      rw [h] at h2; linarith
    · have h2 := hangle a ha c hc b hb hac hbc
      rw [h] at h2; linarith
  obtain ⟨w₀, hmem, hsur, hmono⟩ := exists_argSorted_enum hS3 hgen
  exact master_rigidity_aux hn hcard hangle hgen hS3 w₀ hmem hsur hmono
    (three_le_card_extremeFinset hS3 hgen)

/-! ## M4d1: edge algebra and the dichotomy -/

/-- The rigid `2n`-gon configuration produced by `master_rigidity`. -/
structure RigidConfig (n : ℕ) (S : Finset ℂ) where
  w : Fin (2 * n) → ℂ
  θ : Fin (2 * n) → ℝ
  inj : Function.Injective w
  mem : ∀ i, w i ∈ S
  win : ∀ i, ∀ q ∈ S, q ≠ w i → ∃ r t : ℝ, 0 < r ∧ 0 ≤ t ∧
    t ≤ (1 - 1 / (n : ℝ)) * π ∧
    q - w i = (r : ℂ) * Complex.exp (((θ i + t : ℝ) : ℂ) * Complex.I)
  succ : ∀ i, w (finRotate (2 * n) i) - w i
    = ((‖w (finRotate (2 * n) i) - w i‖ : ℝ) : ℂ)
      * Complex.exp ((θ i : ℂ) * Complex.I)
  pred : ∀ i, w ((finRotate (2 * n)).symm i) - w i
    = ((‖w ((finRotate (2 * n)).symm i) - w i‖ : ℝ) : ℂ)
      * Complex.exp (((θ i + (1 - 1 / (n : ℝ)) * π : ℝ) : ℂ) * Complex.I)

theorem exists_rigidConfig {n : ℕ} (hn : 3 ≤ n) {S : Finset ℂ}
    (hcard : S.card = 2 ^ n)
    (hangle : ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
      EuclideanGeometry.angle p q r ≤ (1 - 1 / (n : ℝ)) * π) :
    Nonempty (RigidConfig n S) := by
  obtain ⟨w, θ, h1, h2, h3, h4, h5⟩ := master_rigidity hn hcard hangle
  exact ⟨⟨w, θ, h1, h2, h3, h4, h5⟩⟩

/-- The edge length from `w i` to its cyclic successor. -/
noncomputable def RigidConfig.len {n : ℕ} {S : Finset ℂ} (C : RigidConfig n S)
    (i : Fin (2 * n)) : ℝ := ‖C.w (finRotate (2 * n) i) - C.w i‖

lemma RigidConfig.succ_ne {n : ℕ} {S : Finset ℂ} (C : RigidConfig n S)
    (hn : 3 ≤ n) (i : Fin (2 * n)) : C.w (finRotate (2 * n) i) ≠ C.w i :=
  fun h => finRotate_ne_self (by omega) i (C.inj h)

lemma RigidConfig.len_pos {n : ℕ} {S : Finset ℂ} (C : RigidConfig n S)
    (hn : 3 ≤ n) (i : Fin (2 * n)) : 0 < C.len i :=
  norm_pos_iff.mpr (sub_ne_zero.mpr (C.succ_ne hn i))

/-- **M4-a: the rotation law.**  Consecutive edge directions differ by `π/n`
modulo a full turn. -/
lemma RigidConfig.theta_succ {n : ℕ} {S : Finset ℂ} (C : RigidConfig n S)
    (hn : 3 ≤ n) (i : Fin (2 * n)) :
    ∃ m : ℤ, C.θ (finRotate (2 * n) i) = C.θ i + π / n + 2 * π * m := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hps : (finRotate (2 * n)).symm (finRotate (2 * n) i) = i :=
    Equiv.symm_apply_apply _ _
  have h2 := C.pred (finRotate (2 * n) i)
  rw [hps] at h2
  obtain ⟨m, hm⟩ := edge_rotation_rule
    (norm_pos_iff.mpr (sub_ne_zero.mpr (C.succ_ne hn i)))
    (norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => (C.succ_ne hn i) h.symm)))
    (C.succ i) h2
  refine ⟨m, ?_⟩
  have : (1 - 1 / (n : ℝ)) * π = π - π / n := by field_simp
  rw [this] at hm
  linarith

/-- **M4-b: the edge directions form an arithmetic progression.** -/
lemma RigidConfig.theta_val {n : ℕ} {S : Finset ℂ} (C : RigidConfig n S)
    (hn : 3 ≤ n) (h0 : 0 < 2 * n) :
    ∀ j : ℕ, ∀ hj : j < 2 * n,
      ∃ m : ℤ, C.θ ⟨j, hj⟩ = C.θ ⟨0, h0⟩ + j * (π / n) + 2 * π * m := by
  intro j
  induction j with
  | zero => intro hj; exact ⟨0, by norm_num⟩
  | succ j ih =>
    intro hj
    obtain ⟨m, hm⟩ := ih (by omega)
    obtain ⟨m', hm'⟩ := C.theta_succ hn ⟨j, by omega⟩
    rw [finRotate_val_of_lt ⟨j, by omega⟩ (by exact hj)] at hm'
    refine ⟨m + m', ?_⟩
    rw [hm', hm]
    push_cast
    ring

/-- The primitive rotation of the rigid configuration. -/
noncomputable def zeta (n : ℕ) : ℂ :=
  Complex.exp (((π / n : ℝ) : ℂ) * Complex.I)

lemma zeta_pow (n : ℕ) (j : ℕ) :
    zeta n ^ j = Complex.exp (((j * (π / n) : ℝ) : ℂ) * Complex.I) := by
  rw [zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- **M4-b (edge form).**  Every edge is `ℓ_j · u₀ · ζ^j`. -/
lemma RigidConfig.edge_eq {n : ℕ} {S : Finset ℂ} (C : RigidConfig n S) (hn : 3 ≤ n)
    (h0 : 0 < 2 * n) (i : Fin (2 * n)) :
    C.w (finRotate (2 * n) i) - C.w i
      = (C.len i : ℂ) * Complex.exp ((C.θ ⟨0, h0⟩ : ℂ) * Complex.I)
        * zeta n ^ (i : ℕ) := by
  obtain ⟨m, hm⟩ := C.theta_val hn h0 (i : ℕ) i.isLt
  rw [show (⟨(i : ℕ), i.isLt⟩ : Fin (2 * n)) = i from Fin.eta _ _] at hm
  have hexp : Complex.exp ((C.θ i : ℂ) * Complex.I)
      = Complex.exp ((C.θ ⟨0, h0⟩ : ℂ) * Complex.I) * zeta n ^ (i : ℕ) := by
    rw [hm, show (C.θ ⟨0, h0⟩ + (i : ℕ) * (π / n) + 2 * π * m : ℝ)
        = (C.θ ⟨0, h0⟩ + (i : ℕ) * (π / n)) + 2 * π * m from by ring,
      exp_add_int_two_pi, zeta_pow,
      show ((C.θ ⟨0, h0⟩ + (i : ℕ) * (π / n) : ℝ) : ℂ) * Complex.I
        = (C.θ ⟨0, h0⟩ : ℂ) * Complex.I
          + (((i : ℕ) * (π / n) : ℝ) : ℂ) * Complex.I from by push_cast; ring,
      Complex.exp_add]
  rw [C.succ i, hexp]
  simp only [RigidConfig.len]
  ring

/-- **M4-c: the closing relation.** -/
lemma RigidConfig.sum_len_zeta {n : ℕ} {S : Finset ℂ} (C : RigidConfig n S)
    (hn : 3 ≤ n) (h0 : 0 < 2 * n) :
    ∑ i : Fin (2 * n), (C.len i : ℂ) * zeta n ^ (i : ℕ) = 0 := by
  have hedge : ∑ i : Fin (2 * n), (C.w (finRotate (2 * n) i) - C.w i) = 0 := by
    rw [Finset.sum_sub_distrib, Equiv.sum_comp (finRotate (2 * n)) C.w, sub_self]
  rw [Finset.sum_congr rfl (fun i _ => C.edge_eq hn h0 i)] at hedge
  have hfac : ∑ i : Fin (2 * n), (C.len i : ℂ)
      * Complex.exp ((C.θ ⟨0, h0⟩ : ℂ) * Complex.I) * zeta n ^ (i : ℕ)
      = Complex.exp ((C.θ ⟨0, h0⟩ : ℂ) * Complex.I)
        * ∑ i : Fin (2 * n), (C.len i : ℂ) * zeta n ^ (i : ℕ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hfac] at hedge
  rcases mul_eq_zero.mp hedge with h | h
  · exact absurd h (Complex.exp_ne_zero _)
  · exact h

lemma zeta_im (n : ℕ) : (zeta n).im = Real.sin (π / n) := by
  rw [zeta, Complex.exp_ofReal_mul_I_im]

lemma zeta_ne_zero (n : ℕ) : zeta n ≠ 0 := Complex.exp_ne_zero _

lemma pi_div_n_mem {n : ℕ} (hn : 3 ≤ n) : 0 < π / n ∧ π / n < π := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hπ : (0 : ℝ) < π := Real.pi_pos
  constructor
  · positivity
  · rw [div_lt_iff₀ hn0]
    nlinarith

lemma arg_zeta {n : ℕ} (hn : 3 ≤ n) : Complex.arg (zeta n) = π / n := by
  obtain ⟨h1, h2⟩ := pi_div_n_mem hn
  exact arg_exp_of_mem ⟨by linarith, le_of_lt h2⟩

/-- **M4-d(1): the angular position of a skipped vertex.** -/
lemma arg_add_mul_zeta_mem {n : ℕ} (hn : 3 ≤ n) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Complex.arg ((x : ℂ) + (y : ℂ) * zeta n) ∈ Set.Ioo 0 (π / n) := by
  obtain ⟨hp1, hp2⟩ := pi_div_n_mem hn
  have hsin : 0 < Real.sin (π / n) := Real.sin_pos_of_pos_of_lt_pi hp1 hp2
  have him : ((x : ℂ) + (y : ℂ) * zeta n).im = y * Real.sin (π / n) := by
    rw [Complex.add_im, Complex.ofReal_im, zero_add, Complex.im_ofReal_mul, zeta_im]
  have himpos : 0 < ((x : ℂ) + (y : ℂ) * zeta n).im := by
    rw [him]; exact mul_pos hy hsin
  have hz0 : (x : ℂ) + (y : ℂ) * zeta n ≠ 0 := by
    intro h
    rw [h, Complex.zero_im] at himpos
    exact lt_irrefl _ himpos
  have hIoo := arg_mem_Ioo_of_im_pos himpos
  refine ⟨hIoo.1, ?_⟩
  -- rotate back by `ζ` and use that the imaginary part becomes negative
  have hconj : (starRingEnd ℂ) (zeta n) * ((x : ℂ) + (y : ℂ) * zeta n)
      = (x : ℂ) * (starRingEnd ℂ) (zeta n) + (y : ℂ) := by
    have h1 : (starRingEnd ℂ) (zeta n) * zeta n = 1 := by
      rw [zeta, mul_comm]
      exact exp_mul_conj_exp _
    linear_combination (y : ℂ) * h1
  have him2 : ((starRingEnd ℂ) (zeta n) * ((x : ℂ) + (y : ℂ) * zeta n)).im
      = -(x * Real.sin (π / n)) := by
    rw [hconj, Complex.add_im, Complex.ofReal_im, add_zero,
      Complex.im_ofReal_mul, Complex.conj_im, zeta_im]
    ring
  have hneg : ((starRingEnd ℂ) (zeta n) * ((x : ℂ) + (y : ℂ) * zeta n)).im < 0 := by
    rw [him2]
    exact neg_neg_of_pos (mul_pos hx hsin)
  have heq := arg_conj_mul_of_mem (zeta_ne_zero n) hz0
    (by rw [arg_zeta hn]; exact ⟨by linarith [hIoo.1], by linarith [hIoo.2]⟩)
  rw [arg_zeta hn] at heq
  have := Complex.arg_neg_iff.mpr hneg
  rw [heq] at this
  linarith

/-- Reflecting the pair `(x, y)` reflects the angle inside the sector. -/
lemma arg_swap_zeta {n : ℕ} (hn : 3 ≤ n) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Complex.arg ((y : ℂ) + (x : ℂ) * zeta n)
      = π / n - Complex.arg ((x : ℂ) + (y : ℂ) * zeta n) := by
  obtain ⟨hp1, hp2⟩ := pi_div_n_mem hn
  have hIoo := arg_add_mul_zeta_mem hn hx hy
  have hu0 : (x : ℂ) + (y : ℂ) * zeta n ≠ 0 := by
    intro h
    have := arg_add_mul_zeta_mem hn hx hy
    rw [h, Complex.arg_zero] at this
    exact lt_irrefl _ this.1
  have hnpos : 0 < ‖(x : ℂ) + (y : ℂ) * zeta n‖ := norm_pos_iff.mpr hu0
  have hzz : zeta n * (starRingEnd ℂ) (zeta n) = 1 := by
    rw [zeta]; exact exp_mul_conj_exp _
  have hswap : (y : ℂ) + (x : ℂ) * zeta n
      = zeta n * (starRingEnd ℂ) ((x : ℂ) + (y : ℂ) * zeta n) := by
    rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal]
    linear_combination (-(y : ℂ)) * hzz
  have hupolar : (starRingEnd ℂ) ((x : ℂ) + (y : ℂ) * zeta n)
      = ((‖(x : ℂ) + (y : ℂ) * zeta n‖ : ℝ) : ℂ)
        * Complex.exp (((-Complex.arg ((x : ℂ) + (y : ℂ) * zeta n) : ℝ) : ℂ)
          * Complex.I) := by
    conv_lhs => rw [(Complex.norm_mul_exp_arg_mul_I ((x : ℂ) + (y : ℂ) * zeta n)).symm]
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    congr 2
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have hfinal : (y : ℂ) + (x : ℂ) * zeta n
      = ((‖(x : ℂ) + (y : ℂ) * zeta n‖ : ℝ) : ℂ)
        * Complex.exp (((π / n - Complex.arg ((x : ℂ) + (y : ℂ) * zeta n) : ℝ) : ℂ)
          * Complex.I) := by
    rw [hswap, hupolar, zeta, ← mul_assoc, mul_comm (Complex.exp (((π / n : ℝ) : ℂ)
      * Complex.I)) _, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hfinal, Complex.arg_real_mul _ hnpos,
    arg_exp_of_mem ⟨by linarith [hIoo.2], by linarith [hIoo.1]⟩]

/-- The angular position of the vertex two steps ahead, in the window at `w i`. -/
noncomputable def RigidConfig.phi {n : ℕ} {S : Finset ℂ} (C : RigidConfig n S)
    (i : Fin (2 * n)) : ℝ :=
  Complex.arg ((C.len i : ℂ) + (C.len (finRotate (2 * n) i) : ℂ) * zeta n)

lemma RigidConfig.phi_mem {n : ℕ} {S : Finset ℂ} (C : RigidConfig n S) (hn : 3 ≤ n)
    (i : Fin (2 * n)) : C.phi i ∈ Set.Ioo 0 (π / n) :=
  arg_add_mul_zeta_mem hn (C.len_pos hn i) (C.len_pos hn _)

/-- The doubled cyclic predecessor. -/
noncomputable def pred2 (n : ℕ) : Equiv.Perm (Fin (2 * n)) :=
  (finRotate (2 * n)).symm.trans (finRotate (2 * n)).symm

/-- **M4-d(3): the dichotomy.** -/
theorem RigidConfig.phi_dichotomy {n : ℕ} {S : Finset ℂ} (C : RigidConfig n S) :
    (∀ i, C.phi (pred2 n i) = C.phi i) ∨ (∃ i, C.phi i < C.phi (pred2 n i)) := by
  by_cases h : ∀ i, C.phi (pred2 n i) = C.phi i
  · exact Or.inl h
  refine Or.inr ?_
  by_contra hcon
  refine h (fun i => ?_)
  have hle : ∀ j, C.phi (pred2 n j) ≤ C.phi j :=
    fun j => not_lt.mp (fun hj => hcon ⟨j, hj⟩)
  have hsum : ∑ j : Fin (2 * n), (C.phi j - C.phi (pred2 n j)) = 0 := by
    rw [Finset.sum_sub_distrib, Equiv.sum_comp (pred2 n) C.phi, sub_self]
  have hnn : ∀ j ∈ (Finset.univ : Finset (Fin (2 * n))),
      0 ≤ C.phi j - C.phi (pred2 n j) := fun j _ => sub_nonneg.mpr (hle j)
  exact (sub_eq_zero.mp
    ((Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum i (Finset.mem_univ i))).symm

lemma RigidConfig.exp_theta_succ {n : ℕ} {S : Finset ℂ} (C : RigidConfig n S)
    (hn : 3 ≤ n) (i : Fin (2 * n)) :
    Complex.exp ((C.θ (finRotate (2 * n) i) : ℂ) * Complex.I)
      = Complex.exp ((C.θ i : ℂ) * Complex.I) * zeta n := by
  obtain ⟨m, hm⟩ := C.theta_succ hn i
  rw [hm, show (C.θ i + π / n + 2 * π * m : ℝ) = (C.θ i + π / n) + 2 * π * m from by
      ring, exp_add_int_two_pi,
    show ((C.θ i + π / n : ℝ) : ℂ) * Complex.I
      = (C.θ i : ℂ) * Complex.I + ((π / n : ℝ) : ℂ) * Complex.I from by
      push_cast; ring, Complex.exp_add, zeta]

/-- **M4-d(2a): the vertex two steps ahead sits at angle `φ i` in the window. -/
lemma RigidConfig.skip_succ_form {n : ℕ} {S : Finset ℂ} (C : RigidConfig n S)
    (hn : 3 ≤ n) (i : Fin (2 * n)) :
    ∃ r : ℝ, 0 < r ∧
      C.w (finRotate (2 * n) (finRotate (2 * n) i)) - C.w i
        = (r : ℂ) * Complex.exp (((C.θ i + C.phi i : ℝ) : ℂ) * Complex.I) := by
  obtain ⟨hp1, hp2⟩ := pi_div_n_mem hn
  set u : ℂ := (C.len i : ℂ) + (C.len (finRotate (2 * n) i) : ℂ) * zeta n with hu
  have hu0 : u ≠ 0 := by
    intro h
    have hm := arg_add_mul_zeta_mem hn (C.len_pos hn i) (C.len_pos hn (finRotate (2 * n) i))
    rw [← hu, h, Complex.arg_zero] at hm
    exact lt_irrefl _ hm.1
  have hnpos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  refine ⟨‖u‖, hnpos, ?_⟩
  have hdec : C.w (finRotate (2 * n) (finRotate (2 * n) i)) - C.w i
      = (C.w (finRotate (2 * n) (finRotate (2 * n) i)) - C.w (finRotate (2 * n) i))
        + (C.w (finRotate (2 * n) i) - C.w i) := by ring
  rw [hdec, C.succ (finRotate (2 * n) i), C.succ i, C.exp_theta_succ hn i]
  have hupolar : u = ((‖u‖ : ℝ) : ℂ)
      * Complex.exp (((C.phi i : ℝ) : ℂ) * Complex.I) :=
    (Complex.norm_mul_exp_arg_mul_I u).symm
  rw [show ((C.θ i + C.phi i : ℝ) : ℂ) * Complex.I
      = (C.θ i : ℂ) * Complex.I + ((C.phi i : ℝ) : ℂ) * Complex.I from by
      push_cast; ring, Complex.exp_add]
  simp only [RigidConfig.len] at hu ⊢
  rw [show ((‖u‖ : ℝ) : ℂ) * (Complex.exp ((C.θ i : ℂ) * Complex.I)
      * Complex.exp (((C.phi i : ℝ) : ℂ) * Complex.I))
    = Complex.exp ((C.θ i : ℂ) * Complex.I)
      * (((‖u‖ : ℝ) : ℂ) * Complex.exp (((C.phi i : ℝ) : ℂ) * Complex.I)) from by ring,
    ← hupolar, hu]
  ring

lemma conj_polar (z : ℂ) :
    (starRingEnd ℂ) z = ((‖z‖ : ℝ) : ℂ)
      * Complex.exp (((-Complex.arg z : ℝ) : ℂ) * Complex.I) := by
  conv_lhs => rw [(Complex.norm_mul_exp_arg_mul_I z).symm]
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- **M4-d(2b): the vertex two steps back sits at angle `W - π/n + φ` in the
window. -/
lemma RigidConfig.skip_pred_form {n : ℕ} {S : Finset ℂ} (C : RigidConfig n S)
    (hn : 3 ≤ n) (i : Fin (2 * n)) :
    ∃ r : ℝ, 0 < r ∧
      C.w (pred2 n i) - C.w i
        = (r : ℂ) * Complex.exp (((C.θ i
            + ((1 - 1 / (n : ℝ)) * π - π / n + C.phi (pred2 n i)) : ℝ) : ℂ)
              * Complex.I) := by
  obtain ⟨hp1, hp2⟩ := pi_div_n_mem hn
  obtain ⟨q1, hq1⟩ : ∃ q1, q1 = (finRotate (2 * n)).symm i := ⟨_, rfl⟩
  obtain ⟨q2, hq2⟩ : ∃ q2, q2 = (finRotate (2 * n)).symm q1 := ⟨_, rfl⟩
  have hfq1 : finRotate (2 * n) q1 = i := by rw [hq1, Equiv.apply_symm_apply]
  have hfq2 : finRotate (2 * n) q2 = q1 := by rw [hq2, Equiv.apply_symm_apply]
  have hpred2 : pred2 n i = q2 := by rw [hq2, hq1, pred2, Equiv.trans_apply]
  rw [hpred2]
  have hlen1 : ‖C.w q1 - C.w i‖ = C.len q1 := by
    rw [RigidConfig.len, hfq1, norm_sub_rev]
  have hlen2 : ‖C.w q2 - C.w q1‖ = C.len q2 := by
    rw [RigidConfig.len, hfq2, norm_sub_rev]
  have hapos : 0 < C.len q1 := C.len_pos hn q1
  have hbpos : 0 < C.len q2 := C.len_pos hn q2
  obtain ⟨u, hu⟩ : ∃ u : ℂ, u = (C.len q1 : ℂ) + (C.len q2 : ℂ) * zeta n := ⟨_, rfl⟩
  have hu0 : u ≠ 0 := by
    intro h
    have hm := arg_add_mul_zeta_mem hn hapos hbpos
    rw [← hu, h, Complex.arg_zero] at hm
    exact lt_irrefl _ hm.1
  have hnpos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  have hargu : Complex.arg u = π / n - C.phi q2 := by
    rw [hu, arg_swap_zeta hn hbpos hapos, RigidConfig.phi, hfq2]
  refine ⟨‖u‖, hnpos, ?_⟩
  have hdec : C.w q2 - C.w i = (C.w q2 - C.w q1) + (C.w q1 - C.w i) := by ring
  have hstep1 := C.pred i
  have hstep2 := C.pred q1
  rw [← hq1, hlen1] at hstep1
  rw [← hq2, hlen2] at hstep2
  have hzz : zeta n * (starRingEnd ℂ) (zeta n) = 1 := by
    rw [zeta]; exact exp_mul_conj_exp _
  have hθq1 : Complex.exp ((C.θ q1 : ℂ) * Complex.I)
      = Complex.exp ((C.θ i : ℂ) * Complex.I) * (starRingEnd ℂ) (zeta n) := by
    have h := C.exp_theta_succ hn q1
    rw [hfq1] at h
    rw [h]
    linear_combination (Complex.exp ((C.θ q1 : ℂ) * Complex.I)) * hzz.symm
  have hexpand : ((C.θ i + ((1 - 1 / (n : ℝ)) * π : ℝ) : ℝ) : ℂ) * Complex.I
      = (C.θ i : ℂ) * Complex.I + (((1 - 1 / (n : ℝ)) * π : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  have hexpand2 : ((C.θ q1 + ((1 - 1 / (n : ℝ)) * π : ℝ) : ℝ) : ℂ) * Complex.I
      = (C.θ q1 : ℂ) * Complex.I + (((1 - 1 / (n : ℝ)) * π : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hdec, hstep1, hstep2, hexpand, hexpand2, Complex.exp_add, Complex.exp_add, hθq1]
  have hconju : (starRingEnd ℂ) u = ((‖u‖ : ℝ) : ℂ)
      * Complex.exp (((C.phi q2 - π / n : ℝ) : ℂ) * Complex.I) := by
    rw [conj_polar u, hargu]
    congr 2
    push_cast
    ring
  have hconju2 : (C.len q1 : ℂ) + (C.len q2 : ℂ) * (starRingEnd ℂ) (zeta n)
      = ((‖u‖ : ℝ) : ℂ)
        * Complex.exp (((C.phi q2 - π / n : ℝ) : ℂ) * Complex.I) := by
    rw [← hconju, hu, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal]
  have htarget : ((C.θ i + ((1 - 1 / (n : ℝ)) * π - π / n + C.phi q2) : ℝ) : ℂ)
      * Complex.I
      = (C.θ i : ℂ) * Complex.I + (((1 - 1 / (n : ℝ)) * π : ℝ) : ℂ) * Complex.I
        + ((C.phi q2 - π / n : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [htarget, Complex.exp_add, Complex.exp_add]
  linear_combination (Complex.exp ((C.θ i : ℂ) * Complex.I)
    * Complex.exp ((((1 - 1 / (n : ℝ)) * π : ℝ) : ℂ) * Complex.I)) * hconju2

/-- **M4-d(2): the skip angle.**  The angle subtended at `w i` by the two
vertices two steps away. -/
lemma RigidConfig.sigma_eq {n : ℕ} {S : Finset ℂ} (C : RigidConfig n S)
    (hn : 3 ≤ n) (i : Fin (2 * n)) :
    EuclideanGeometry.angle (C.w (finRotate (2 * n) (finRotate (2 * n) i)))
        (C.w i) (C.w (pred2 n i))
      = ((1 - 1 / (n : ℝ)) * π - π / n + C.phi (pred2 n i)) - C.phi i := by
  obtain ⟨hp1, hp2⟩ := pi_div_n_mem hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hπ : (0 : ℝ) < π := Real.pi_pos
  obtain ⟨r₁, hr₁, hf₁⟩ := C.skip_succ_form hn i
  obtain ⟨r₂, hr₂, hf₂⟩ := C.skip_pred_form hn i
  have hφi := C.phi_mem hn i
  have hφp := C.phi_mem hn (pred2 n i)
  have hid : (1 - 1 / (n : ℝ)) * π = π - π / n := by field_simp
  have hdn : (π / n) * n = π := by field_simp
  have hkey : 3 * (π / n) ≤ π := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hn3) hp1.le]
  have hlt : C.phi i
      < (1 - 1 / (n : ℝ)) * π - π / n + C.phi (pred2 n i) := by
    have h1 := hφi.2
    have h2 := hφp.1
    rw [hid]
    linarith
  have habs : |C.phi i
      - ((1 - 1 / (n : ℝ)) * π - π / n + C.phi (pred2 n i))| < π := by
    rw [abs_of_neg (by linarith)]
    have h1 := hφp.2
    have h2 := hφi.1
    rw [hid]
    linarith
  rw [angle_eq_abs_of_polar hr₁ hr₂ habs hf₁ hf₂,
    abs_of_neg (by linarith : C.phi i
      - ((1 - 1 / (n : ℝ)) * π - π / n + C.phi (pred2 n i)) < 0)]
  ring

/-! ### M4-e: the second case of the dichotomy is impossible -/

/-- The oriented area of two vectors given in polar form. -/
lemma im_conj_polar_mul {v z₁ z₂ : ℂ} {θ t₁ t₂ r₁ r₂ : ℝ}
    (h₁ : z₁ - v = (r₁ : ℂ) * Complex.exp (((θ + t₁ : ℝ) : ℂ) * Complex.I))
    (h₂ : z₂ - v = (r₂ : ℂ) * Complex.exp (((θ + t₂ : ℝ) : ℂ) * Complex.I)) :
    ((starRingEnd ℂ) (z₁ - v) * (z₂ - v)).im = r₁ * r₂ * Real.sin (t₂ - t₁) := by
  have hexp : (starRingEnd ℂ) (Complex.exp (((θ + t₁ : ℝ) : ℂ) * Complex.I))
      * Complex.exp (((θ + t₂ : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((t₂ - t₁ : ℝ) : ℂ) * Complex.I) := by
    have h := conj_exp_mul_exp (θ + t₁) (t₂ - t₁)
    rw [show ((θ + t₁) + (t₂ - t₁) : ℝ) = θ + t₂ from by ring] at h
    exact h
  have hkey : (starRingEnd ℂ) (z₁ - v) * (z₂ - v)
      = ((r₁ * r₂ : ℝ) : ℂ) * Complex.exp (((t₂ - t₁ : ℝ) : ℂ) * Complex.I) := by
    rw [h₁, h₂, map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
    linear_combination ((r₁ : ℂ) * (r₂ : ℂ)) * hexp
  rw [hkey, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]

lemma pos_of_mul_pos_of_eq {a b c : ℝ} (hab : 0 < a * b) (h : b = c * a) : 0 < c := by
  have ha : a ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hab
    exact lt_irrefl _ hab
  have ha2 : 0 < a * a := mul_self_pos.mpr ha
  have hab' : 0 < c * (a * a) := by
    have h2 : a * b = c * (a * a) := by rw [h]; ring
    rw [← h2]; exact hab
  by_contra hc
  rw [not_lt] at hc
  nlinarith [mul_nonneg (neg_nonneg.mpr hc) ha2.le]

/-- **M4-e (step 1): no point of `S` lies strictly inside the triangle cut out
by a vertex, its neighbour, and the neighbour's other neighbour.** -/
lemma no_interior_point {n : ℕ} {S : Finset ℂ}
    (hgen : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set ℂ))
    (hangle : ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
      EuclideanGeometry.angle p q r ≤ (1 - 1 / (n : ℝ)) * π)
    {v b c x u : ℂ} {θ σ t rb rc rx : ℝ}
    (hv : v ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hx : x ∈ S)
    (hrb : 0 < rb) (hrc : 0 < rc) (hrx : 0 < rx)
    (hbf : b - v = (rb : ℂ) * Complex.exp (((θ + 0 : ℝ) : ℂ) * Complex.I))
    (hcf : c - v = (rc : ℂ) * Complex.exp (((θ + σ : ℝ) : ℂ) * Complex.I))
    (hxf : x - v = (rx : ℂ) * Complex.exp (((θ + t : ℝ) : ℂ) * Complex.I))
    (hbetween : (0 < σ ∧ 0 < t ∧ t < σ) ∨ (σ < 0 ∧ σ < t ∧ t < 0))
    (hσπ : |σ| < π)
    (hangbc : EuclideanGeometry.angle v b c = (1 - 1 / (n : ℝ)) * π)
    (hFhalf : ∀ q ∈ S, 0 ≤ ((starRingEnd ℂ) u * (q - b)).im)
    (hFc : ((starRingEnd ℂ) u * (c - b)).im = 0)
    (hFv : 0 < ((starRingEnd ℂ) u * (v - b)).im) :
    False := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have habs := abs_lt.mp hσπ
  -- the three oriented areas
  have hD : ((starRingEnd ℂ) (b - v) * (c - v)).im = rb * rc * Real.sin σ := by
    rw [im_conj_polar_mul hbf hcf, sub_zero]
  have hqarea : ((starRingEnd ℂ) (b - v) * (x - v)).im
      = rb * rx * Real.sin t := by
    rw [im_conj_polar_mul hbf hxf, sub_zero]
  have hparea : ((starRingEnd ℂ) (c - v) * (x - v)).im
      = rc * rx * Real.sin (t - σ) := by
    rw [im_conj_polar_mul hcf hxf]
  -- signs
  have hsign : (0 < rb * rc * Real.sin σ ∧ 0 < rb * rx * Real.sin t ∧
      rc * rx * Real.sin (t - σ) < 0) ∨
      (rb * rc * Real.sin σ < 0 ∧ rb * rx * Real.sin t < 0 ∧
      0 < rc * rx * Real.sin (t - σ)) := by
    rcases hbetween with ⟨hσ0, ht0, htσ⟩ | ⟨hσ0, hσt, ht0⟩
    · refine Or.inl ⟨?_, ?_, ?_⟩
      · exact mul_pos (mul_pos hrb hrc)
          (Real.sin_pos_of_pos_of_lt_pi hσ0 (by linarith [habs.2]))
      · exact mul_pos (mul_pos hrb hrx)
          (Real.sin_pos_of_pos_of_lt_pi ht0 (by linarith [habs.2]))
      · refine mul_neg_of_pos_of_neg (mul_pos hrc hrx) ?_
        rw [show t - σ = -(σ - t) from by ring, Real.sin_neg, neg_neg_iff_pos]
        exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [habs.1])
    · refine Or.inr ⟨?_, ?_, ?_⟩
      · refine mul_neg_of_pos_of_neg (mul_pos hrb hrc) ?_
        rw [show σ = -(-σ) from by ring, Real.sin_neg, neg_neg_iff_pos]
        exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [habs.1])
      · refine mul_neg_of_pos_of_neg (mul_pos hrb hrx) ?_
        rw [show t = -(-t) from by ring, Real.sin_neg, neg_neg_iff_pos]
        exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [habs.1])
      · exact mul_pos (mul_pos hrc hrx)
          (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [habs.2]))
  -- Cramer decomposition
  have hDne : ((starRingEnd ℂ) (b - v) * (c - v)).im ≠ 0 := by
    rw [hD]
    rcases hsign with ⟨h, _, _⟩ | ⟨h, _, _⟩
    · exact ne_of_gt h
    · exact ne_of_lt h
  obtain ⟨p, q, hdec, hqid, hpid⟩ :=
    exists_decomp_of_im_ne_zero (X := b - v) (Y := c - v) (z := x - v) hDne
  have hswapD : ((starRingEnd ℂ) (c - v) * (b - v)).im
      = -(rb * rc * Real.sin σ) := by
    rw [im_conj_mul_swap, hD]
  rw [hqarea, hD] at hqid
  rw [hparea, hswapD] at hpid
  have hq0 : 0 < q := by
    refine pos_of_mul_pos_of_eq ?_ hqid
    rcases hsign with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩
    · exact mul_pos h1 h2
    · exact mul_pos_of_neg_of_neg h1 h2
  have hp0 : 0 < p := by
    refine pos_of_mul_pos_of_eq ?_ hpid
    rcases hsign with ⟨h1, _, h3⟩ | ⟨h1, _, h3⟩
    · exact mul_pos_of_neg_of_neg (by linarith) h3
    · exact mul_pos (by linarith) h3
  -- distinctness
  have hbv' : v ≠ b := by
    intro h
    rw [← h, sub_self] at hbf
    exact (mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hrb))
      (Complex.exp_ne_zero _)) hbf.symm
  have hcv' : v ≠ c := by
    intro h
    rw [← h, sub_self] at hcf
    exact (mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hrc))
      (Complex.exp_ne_zero _)) hcf.symm
  have hxv : v ≠ x := by
    intro h
    rw [← h, sub_self] at hxf
    exact (mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hrx))
      (Complex.exp_ne_zero _)) hxf.symm
  have hbc : b ≠ c := by
    intro h
    rw [h, im_conj_self] at hD
    rcases hsign with ⟨h1, _, _⟩ | ⟨h1, _, _⟩
    · exact absurd hD.symm (ne_of_gt h1)
    · exact absurd hD.symm (ne_of_lt h1)
  have hxb : x ≠ b := by
    intro h
    rw [h, im_conj_self] at hqarea
    rcases hsign with ⟨_, h2, _⟩ | ⟨_, h2, _⟩
    · exact absurd hqarea.symm (ne_of_gt h2)
    · exact absurd hqarea.symm (ne_of_lt h2)
  have hxc : x ≠ c := by
    intro h
    rw [h, im_conj_self] at hparea
    rcases hsign with ⟨_, _, h3⟩ | ⟨_, _, h3⟩
    · exact absurd hparea.symm (ne_of_lt h3)
    · exact absurd hparea.symm (ne_of_gt h3)
  -- the half-plane at `b` bounds the barycentric weight of `v`
  rw [Complex.real_smul, Complex.real_smul] at hdec
  have hxbeq : x - b = ((1 - p - q : ℝ) : ℂ) * (v - b) + ((q : ℝ) : ℂ) * (c - b) := by
    push_cast
    linear_combination hdec
  have hFx : ((starRingEnd ℂ) u * (x - b)).im
      = (1 - p - q) * ((starRingEnd ℂ) u * (v - b)).im
        + q * ((starRingEnd ℂ) u * (c - b)).im := by
    have hid : (starRingEnd ℂ) u * (x - b)
        = ((1 - p - q : ℝ) : ℂ) * ((starRingEnd ℂ) u * (v - b))
          + ((q : ℝ) : ℂ) * ((starRingEnd ℂ) u * (c - b)) := by
      linear_combination ((starRingEnd ℂ) u) * hxbeq
    rw [hid, Complex.add_im, Complex.im_ofReal_mul, Complex.im_ofReal_mul]
  rw [hFc, mul_zero, add_zero] at hFx
  have hs0 : 0 ≤ 1 - p - q := by
    have h := hFhalf x hx
    rw [hFx] at h
    nlinarith
  have hs0' : 0 < 1 - p - q := by
    rcases lt_or_eq_of_le hs0 with h | h
    · exact h
    exfalso
    have hxbc : x - b = ((q : ℝ) : ℂ) * (c - b) := by
      rw [hxbeq, ← h]
      push_cast
      ring
    refine hgen x hx b hb c hc hxb hbc hxc ?_
    rw [collinear_iff_of_mem (show b ∈ ({x, b, c} : Set ℂ) by simp)]
    refine ⟨c - b, fun z hz => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact ⟨q, by simp only [Complex.real_smul, vadd_eq_add]; linear_combination hxbc⟩
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp only [Complex.real_smul, vadd_eq_add]; push_cast; ring⟩
  -- an interior point sees the far side under too large an angle
  have hxeq : x = (1 - p - q) • v + p • b + q • c := by
    simp only [Complex.real_smul]
    push_cast
    linear_combination hdec
  have hnc : ¬ Collinear ℝ ({v, b, c} : Set ℂ) := hgen v hv b hb c hc hbv' hbc hcv'
  have hlt := angle_lt_angle_of_interior hs0' hp0 hq0 (by ring) hxeq hnc
  rw [hangbc] at hlt
  have hle := hangle v hv x hx c hc hxv (Ne.symm hxc)
  linarith

/-- **M4-e (step 2): at the extremal cardinality, every vertex has at least
three edges in any two prescribed sectors.** -/
theorem three_le_card_dir_edges {n : ℕ} (hn : 0 < n) (S : Finset ℂ)
    (hcard : S.card = 2 ^ n)
    (hangle : ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
      EuclideanGeometry.angle p q r ≤ (1 - 1 / (n : ℝ)) * π)
    {p : ℂ} (hp : p ∈ S) {i₀ i₁ : Fin n} (hii : i₀ ≠ i₁) :
    3 ≤ (S.filter (fun q => q ≠ p ∧
      (dirIndex n (q - p) = (i₀ : ℕ) ∨ dirIndex n (q - p) = (i₁ : ℕ)))).card := by
  classical
  have key : ∀ u v : {x // x ∈ S}, (u : ℂ) ≠ (v : ℂ) →
      IsPos ((v : ℂ) - (u : ℂ)) →
      ¬ ∃ w : {x // x ∈ S}, (w : ℂ) ≠ (v : ℂ) ∧ IsPos ((w : ℂ) - (v : ℂ)) ∧
        dirIndex n ((w : ℂ) - (v : ℂ)) = dirIndex n ((v : ℂ) - (u : ℂ)) := by
    rintro u v huv hpos ⟨w, hwv, hwpos, hwcol⟩
    have hpq : (v : ℂ) - (u : ℂ) ≠ 0 := sub_ne_zero.mpr huv.symm
    have hqr : (w : ℂ) - (v : ℂ) ≠ 0 := sub_ne_zero.mpr hwv
    have hbig := lt_angle_of_isPos_of_dirIndex_eq hn hpq hqr hpos hwpos hwcol.symm
    have hle := hangle (u : ℂ) u.2 (v : ℂ) v.2 (w : ℂ) w.2 huv hwv
    linarith
  have hside : ∀ u v : {x // x ∈ S}, u ≠ v →
      (decide (∃ w : {x // x ∈ S}, (w : ℂ) ≠ (u : ℂ) ∧
          IsPos ((w : ℂ) - (u : ℂ)) ∧
          dirIndex n ((w : ℂ) - (u : ℂ)) = dirIndex n ((v : ℂ) - (u : ℂ))))
        ≠ (decide (∃ w : {x // x ∈ S}, (w : ℂ) ≠ (v : ℂ) ∧
          IsPos ((w : ℂ) - (v : ℂ)) ∧
          dirIndex n ((w : ℂ) - (v : ℂ)) = dirIndex n ((v : ℂ) - (u : ℂ)))) := by
    intro u v huv
    have huv' : (u : ℂ) ≠ (v : ℂ) := fun h => huv (Subtype.ext h)
    have hz : (v : ℂ) - (u : ℂ) ≠ 0 := sub_ne_zero.mpr huv'.symm
    have hdi : dirIndex n ((u : ℂ) - (v : ℂ))
        = dirIndex n ((v : ℂ) - (u : ℂ)) := by
      rw [show ((u : ℂ) - (v : ℂ)) = -((v : ℂ) - (u : ℂ)) by ring, dirIndex_neg]
    by_cases hpos : IsPos ((v : ℂ) - (u : ℂ))
    · have hPu : ∃ w : {x // x ∈ S}, (w : ℂ) ≠ (u : ℂ) ∧
          IsPos ((w : ℂ) - (u : ℂ)) ∧
          dirIndex n ((w : ℂ) - (u : ℂ)) = dirIndex n ((v : ℂ) - (u : ℂ)) :=
        ⟨v, huv'.symm, hpos, rfl⟩
      have hPv : ¬ ∃ w : {x // x ∈ S}, (w : ℂ) ≠ (v : ℂ) ∧
          IsPos ((w : ℂ) - (v : ℂ)) ∧
          dirIndex n ((w : ℂ) - (v : ℂ)) = dirIndex n ((v : ℂ) - (u : ℂ)) :=
        key u v huv' hpos
      rw [decide_eq_true hPu, decide_eq_false hPv]
      simp
    · have hpos' : IsPos ((u : ℂ) - (v : ℂ)) := by
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
      rw [decide_eq_false hPu, decide_eq_true hPv]
      simp
  have hcard' : Fintype.card {x // x ∈ S} = 2 ^ n := by
    rw [Fintype.card_coe]; exact hcard
  have h3 := three_le_card_edges_of_card_eq
    (fun u v : {x // x ∈ S} =>
      (⟨dirIndex n ((v : ℂ) - (u : ℂ)), dirIndex_lt hn _⟩ : Fin n))
    (fun (j : Fin n) (v : {x // x ∈ S}) => decide (∃ w : {x // x ∈ S},
      (w : ℂ) ≠ (v : ℂ) ∧ IsPos ((w : ℂ) - (v : ℂ)) ∧
        dirIndex n ((w : ℂ) - (v : ℂ)) = (j : ℕ)))
    hside hcard' ⟨p, hp⟩ hii
  refine le_trans h3 ?_
  rw [← Finset.card_image_of_injective _ (Subtype.val_injective)]
  apply Finset.card_le_card
  intro z hz
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hz
  obtain ⟨u, ⟨hune, hcol⟩, rfl⟩ := hz
  have hdi : dirIndex n ((u : ℂ) - p) = dirIndex n (p - (u : ℂ)) := by
    rw [show ((u : ℂ) - p) = -(p - (u : ℂ)) by ring, dirIndex_neg]
  simp only [Finset.mem_filter]
  refine ⟨u.2, fun h => hune (Subtype.ext h), ?_⟩
  rcases hcol with h | h
  · exact Or.inl (by rw [hdi]; exact congrArg Fin.val h)
  · exact Or.inr (by rw [hdi]; exact congrArg Fin.val h)

lemma arg_of_polar {r α : ℝ} (hr : 0 < r) (hlo : -π < α) (hhi : α ≤ π) :
    Complex.arg ((r : ℂ) * Complex.exp ((α : ℂ) * Complex.I)) = α := by
  rw [Complex.arg_real_mul _ hr, arg_exp_of_mem ⟨hlo, hhi⟩]

/-- The sector index of a direction with argument in `[0, π)`. -/
lemma dirIndex_of_polar_nonneg {n : ℕ} {r α : ℝ}
    (hr : 0 < r) (h0 : 0 ≤ α) (hπα : α < π) :
    dirIndex n ((r : ℂ) * Complex.exp ((α : ℂ) * Complex.I))
      = (⌊(n : ℝ) * (α / π)⌋).toNat := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hfr : Int.fract (α / π) = α / π := by
    refine Int.fract_eq_self.mpr ⟨by positivity, ?_⟩
    rw [div_lt_one hπ]
    exact hπα
  unfold dirIndex
  rw [arg_of_polar hr (by linarith) (le_of_lt hπα), hfr]

/-- The sector index of a direction with argument in `(-π/n, 0)` is `n - 1`. -/
lemma dirIndex_of_polar_neg {n : ℕ} (hn : 0 < n) {r α : ℝ}
    (hr : 0 < r) (hlo : -(π / n) < α) (h0 : α < 0) :
    dirIndex n ((r : ℂ) * Complex.exp ((α : ℂ) * Complex.I)) = n - 1 := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hπn : 0 < π / n := by positivity
  have hπnle : π / n ≤ π := by
    rw [div_le_iff₀ hnR]
    nlinarith
  have hαπ : -π < α := by linarith
  have hnα : -π < (n : ℝ) * α := by
    have h2 : (n : ℝ) * (π / n) = π := by field_simp
    have h := mul_lt_mul_of_pos_left hlo hnR
    rw [mul_neg, h2] at h
    exact h
  have hdiv : -1 < (n : ℝ) * α / π := by
    rw [lt_div_iff₀ hπ]
    linarith
  have hdiv2 : (n : ℝ) * α / π < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hnR h0) hπ
  have heq : (n : ℝ) * (α / π + 1) = (n : ℝ) * α / π + n := by field_simp
  have hfr : Int.fract (α / π) = α / π + 1 := by
    have hA : (0 : ℝ) ≤ α / π + 1 := by
      have hB : -1 < α / π := by
        rw [lt_div_iff₀ hπ]
        linarith
      linarith
    have hC : α / π + 1 < 1 := by
      have hD : α / π < 0 := div_neg_of_neg_of_pos h0 hπ
      linarith
    calc Int.fract (α / π) = Int.fract (α / π + 1) := (Int.fract_add_one _).symm
      _ = α / π + 1 := Int.fract_eq_self.mpr ⟨hA, hC⟩
  have hfloor : ⌊(n : ℝ) * Int.fract (α / π)⌋ = (n : ℤ) - 1 := by
    rw [hfr]
    refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
    · push_cast
      rw [heq]
      linarith
    · push_cast
      rw [heq]
      linarith
  unfold dirIndex
  rw [arg_of_polar hr hαπ (by linarith), hfloor]
  omega

/-- In general position, two points of `S` on the same ray from `v ∈ S` coincide. -/
lemma eq_of_same_ray {S : Finset ℂ}
    (hgen : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set ℂ))
    {v b q : ℂ} {ψ rb rq : ℝ}
    (hv : v ∈ S) (hb : b ∈ S) (hq : q ∈ S) (hrb : 0 < rb) (hrq : 0 < rq)
    (hbf : b - v = (rb : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I))
    (hqf : q - v = (rq : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I)) :
    q = b := by
  by_contra hqb
  have hbv : v ≠ b := by
    intro h
    rw [← h, sub_self] at hbf
    exact (mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hrb))
      (Complex.exp_ne_zero _)) hbf.symm
  have hqv : q ≠ v := by
    intro h
    rw [h, sub_self] at hqf
    exact (mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hrq))
      (Complex.exp_ne_zero _)) hqf.symm
  refine hgen q hq v hv b hb hqv hbv hqb ?_
  rw [collinear_iff_of_mem (show v ∈ ({q, v, b} : Set ℂ) by simp)]
  refine ⟨Complex.exp ((ψ : ℂ) * Complex.I), fun z hz => ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl
  · refine ⟨rq, ?_⟩
    simp only [Complex.real_smul, vadd_eq_add]
    linear_combination hqf
  · exact ⟨0, by simp⟩
  · refine ⟨rb, ?_⟩
    simp only [Complex.real_smul, vadd_eq_add]
    linear_combination hbf

/-- **M4-e: the second alternative of the dichotomy is impossible.** -/
theorem case2b_false {n : ℕ} (hn : 3 ≤ n) {S : Finset ℂ}
    (hcard : S.card = 2 ^ n)
    (hangle : ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
      EuclideanGeometry.angle p q r ≤ (1 - 1 / (n : ℝ)) * π)
    (hgen : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set ℂ))
    (C : RigidConfig n S) {i : Fin (2 * n)}
    (h2b : C.phi (pred2 n i) < C.phi i) :
    False := by
  classical
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hπ : (0 : ℝ) < π := Real.pi_pos
  obtain ⟨hp1, hp2⟩ := pi_div_n_mem hn
  have hdn : (π / n) * n = π := by field_simp
  have hkey3 : 3 * (π / n) ≤ π := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hn3) hp1.le]
  have hWid : (1 - 1 / (n : ℝ)) * π = π - π / n := by field_simp
  have hWlt : (1 - 1 / (n : ℝ)) * π < π := by rw [hWid]; linarith
  have hW0 : 0 < (1 - 1 / (n : ℝ)) * π := by rw [hWid]; linarith
  -- cyclic neighbours
  obtain ⟨si, hsi⟩ : ∃ z, z = finRotate (2 * n) i := ⟨_, rfl⟩
  obtain ⟨pi1, hpi1⟩ : ∃ z, z = (finRotate (2 * n)).symm i := ⟨_, rfl⟩
  obtain ⟨ppi, hppi⟩ : ∃ z, z = (finRotate (2 * n)).symm pi1 := ⟨_, rfl⟩
  have hppi2 : pred2 n i = ppi := by rw [hppi, hpi1, pred2, Equiv.trans_apply]
  have hsp : (finRotate (2 * n)).symm si = i := by rw [hsi, Equiv.symm_apply_apply]
  have hps : finRotate (2 * n) pi1 = i := by rw [hpi1, Equiv.apply_symm_apply]
  have hfppi : finRotate (2 * n) ppi = pi1 := by rw [hppi, Equiv.apply_symm_apply]
  have hsine : si ≠ i := by rw [hsi]; exact finRotate_ne_self (by omega) i
  have hpine : pi1 ≠ i := by
    intro h
    rw [h] at hps
    exact finRotate_ne_self (by omega) i hps
  -- polar forms at the vertex `w i`
  have hφi := C.phi_mem hn i
  have hφp := C.phi_mem hn (pred2 n i)
  rw [hppi2] at hφp h2b
  have hBform : C.w si - C.w i
      = ((C.len i : ℝ) : ℂ) * Complex.exp ((C.θ i : ℂ) * Complex.I) := by
    rw [hsi]; exact C.succ i
  obtain ⟨rc, hrc, hCform⟩ := C.skip_succ_form hn i
  rw [← hsi] at hCform
  have hDform : C.w pi1 - C.w i
      = ((‖C.w pi1 - C.w i‖ : ℝ) : ℂ)
        * Complex.exp (((C.θ i + (1 - 1 / (n : ℝ)) * π : ℝ) : ℂ) * Complex.I) := by
    rw [hpi1]; exact C.pred i
  obtain ⟨re, hre, hEform⟩ := C.skip_pred_form hn i
  rw [hppi2] at hEform
  -- Step A : the angular interval `(0, φ i)` at `w i` contains no point of `S`
  have hstepA : ∀ x ∈ S, ∀ rx t : ℝ, 0 < rx → 0 < t → t < C.phi i →
      x - C.w i = (rx : ℂ) * Complex.exp (((C.θ i + t : ℝ) : ℂ) * Complex.I)
      → False := by
    intro x hx rx t hrx ht0 hts hxf
    have hbv : C.w si ≠ C.w i := fun h => hsine (C.inj h)
    have hvbnorm : 0 < ‖C.w i - C.w si‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => hbv h.symm))
    have hcbnorm : 0 < ‖C.w (finRotate (2 * n) si) - C.w si‖ := C.len_pos hn si
    have hvb : C.w i - C.w si
        = ((‖C.w i - C.w si‖ : ℝ) : ℂ)
          * Complex.exp (((C.θ si + (1 - 1 / (n : ℝ)) * π : ℝ) : ℂ) * Complex.I) := by
      have h := C.pred si
      rw [hsp] at h
      exact h
    have hcb : C.w (finRotate (2 * n) si) - C.w si
        = ((‖C.w (finRotate (2 * n) si) - C.w si‖ : ℝ) : ℂ)
          * Complex.exp ((C.θ si : ℂ) * Complex.I) := C.succ si
    have hang : EuclideanGeometry.angle (C.w i) (C.w si)
        (C.w (finRotate (2 * n) si)) = (1 - 1 / (n : ℝ)) * π := by
      have h := angle_eq_abs_of_polar (v := C.w si) (θ := C.θ si)
        (t₁ := (1 - 1 / (n : ℝ)) * π) (t₂ := 0)
        hvbnorm hcbnorm (by rw [sub_zero, abs_of_pos hW0]; exact hWlt)
        hvb (by rw [add_zero]; exact hcb)
      rw [h, sub_zero, abs_of_pos hW0]
    refine no_interior_point (n := n) (u := Complex.exp ((C.θ si : ℂ) * Complex.I))
      hgen hangle (C.mem i) (C.mem si) (C.mem (finRotate (2 * n) si)) hx
      (C.len_pos hn i) hrc hrx (by rw [add_zero]; exact hBform) hCform hxf
      (Or.inl ⟨hφi.1, ht0, hts⟩)
      (by rw [abs_of_pos hφi.1]; linarith [hφi.2]) hang
      (window_half hWlt (C.win si)) (window_zero hcb) ?_
    rw [im_conj_exp_mul_polar hvb]
    exact mul_pos hvbnorm (Real.sin_pos_of_pos_of_lt_pi hW0 hWlt)
  -- Step B : the angular interval `(W - π/n + φ (pred² i), W)` at `w i` is empty
  have hstepB : ∀ x ∈ S, ∀ rx t : ℝ, 0 < rx →
      (1 - 1 / (n : ℝ)) * π - π / n + C.phi ppi < t →
      t < (1 - 1 / (n : ℝ)) * π →
      x - C.w i = (rx : ℂ) * Complex.exp (((C.θ i + t : ℝ) : ℂ) * Complex.I)
      → False := by
    intro x hx rx t hrx htlo hthi hxf
    have hDv : C.w pi1 ≠ C.w i := fun h => hpine (C.inj h)
    have hbrad : 0 < ‖C.w pi1 - C.w i‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hDv)
    have hvDnorm : 0 < ‖C.w i - C.w pi1‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => hDv h.symm))
    have hppine : ppi ≠ pi1 := by
      intro h
      rw [h] at hfppi
      exact finRotate_ne_self (by omega) pi1 hfppi
    have hEDnorm : 0 < ‖C.w ppi - C.w pi1‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => hppine (C.inj h)))
    have hvD : C.w i - C.w pi1
        = ((‖C.w i - C.w pi1‖ : ℝ) : ℂ)
          * Complex.exp ((C.θ pi1 : ℂ) * Complex.I) := by
      have h := C.succ pi1
      rw [hps] at h
      exact h
    have hED : C.w ppi - C.w pi1
        = ((‖C.w ppi - C.w pi1‖ : ℝ) : ℂ)
          * Complex.exp (((C.θ pi1 + (1 - 1 / (n : ℝ)) * π : ℝ) : ℂ) * Complex.I) := by
      have h := C.pred pi1
      rw [← hppi] at h
      exact h
    have hang : EuclideanGeometry.angle (C.w i) (C.w pi1) (C.w ppi)
        = (1 - 1 / (n : ℝ)) * π := by
      have h := angle_eq_abs_of_polar (v := C.w pi1) (θ := C.θ pi1) (t₁ := 0)
        (t₂ := (1 - 1 / (n : ℝ)) * π) hvDnorm hEDnorm
        (by rw [zero_sub, abs_neg, abs_of_pos hW0]; exact hWlt)
        (by rw [add_zero]; exact hvD) hED
      rw [h, zero_sub, abs_neg, abs_of_pos hW0]
    have hvDpolar : C.w i - C.w pi1
        = ((‖C.w i - C.w pi1‖ : ℝ) : ℂ)
          * Complex.exp ((((C.θ pi1 + (1 - 1 / (n : ℝ)) * π)
              + (-((1 - 1 / (n : ℝ)) * π)) : ℝ) : ℂ) * Complex.I) := by
      rw [show ((C.θ pi1 + (1 - 1 / (n : ℝ)) * π)
          + (-((1 - 1 / (n : ℝ)) * π)) : ℝ) = C.θ pi1 from by ring]
      exact hvD
    have hDform' : C.w pi1 - C.w i = ((‖C.w pi1 - C.w i‖ : ℝ) : ℂ)
        * Complex.exp ((((C.θ i + (1 - 1 / (n : ℝ)) * π) + 0 : ℝ) : ℂ)
          * Complex.I) := by
      rw [add_zero]
      exact hDform
    have hEform' : C.w ppi - C.w i = (re : ℂ)
        * Complex.exp ((((C.θ i + (1 - 1 / (n : ℝ)) * π)
            + (C.phi ppi - π / n) : ℝ) : ℂ) * Complex.I) := by
      rw [show ((C.θ i + (1 - 1 / (n : ℝ)) * π) + (C.phi ppi - π / n) : ℝ)
        = C.θ i + ((1 - 1 / (n : ℝ)) * π - π / n + C.phi ppi) from by ring]
      exact hEform
    have hxf' : x - C.w i = (rx : ℂ)
        * Complex.exp ((((C.θ i + (1 - 1 / (n : ℝ)) * π)
            + (t - (1 - 1 / (n : ℝ)) * π) : ℝ) : ℂ) * Complex.I) := by
      rw [show ((C.θ i + (1 - 1 / (n : ℝ)) * π) + (t - (1 - 1 / (n : ℝ)) * π) : ℝ)
        = C.θ i + t from by ring]
      exact hxf
    refine no_interior_point (n := n)
      (u := -Complex.exp (((C.θ pi1 + (1 - 1 / (n : ℝ)) * π : ℝ) : ℂ) * Complex.I))
      hgen hangle (C.mem i) (C.mem pi1) (C.mem ppi) hx hbrad hre hrx
      hDform' hEform' hxf'
      (Or.inr ⟨by linarith [hφp.2], by linarith, by linarith⟩)
      (by rw [abs_of_neg (by linarith [hφp.2])]; linarith [hφp.1]) hang ?_ ?_ ?_
    · intro q hq
      rw [im_conj_neg_mul]
      exact neg_nonneg.mpr (window_half' hWlt (C.win pi1) q hq)
    · rw [im_conj_neg_mul, window_zero hED, neg_zero]
    · rw [im_conj_neg_mul, im_conj_exp_mul_polar hvDpolar, Real.sin_neg,
        mul_neg, neg_neg]
      exact mul_pos hvDnorm (Real.sin_pos_of_pos_of_lt_pi hW0 hWlt)
  -- Step C : rotate so that `w (succ succ i)` points along the positive axis
  obtain ⟨urot, hurot⟩ : ∃ z : ℂ,
      z = Complex.exp (((-(C.θ i + C.phi i) : ℝ) : ℂ) * Complex.I) := ⟨_, rfl⟩
  have hurot0 : urot ≠ 0 := by rw [hurot]; exact Complex.exp_ne_zero _
  have hinjrot : Function.Injective (fun z => urot * z) :=
    fun a b h => mul_left_cancel₀ hurot0 h
  have hcard' : (S.image (fun z => urot * z)).card = 2 ^ n := by
    rw [Finset.card_image_of_injective _ hinjrot, hcard]
  have hangle' : ∀ p ∈ S.image (fun z => urot * z),
      ∀ q ∈ S.image (fun z => urot * z), ∀ r ∈ S.image (fun z => urot * z),
      p ≠ q → r ≠ q →
      EuclideanGeometry.angle p q r ≤ (1 - 1 / (n : ℝ)) * π := by
    intro p hp q hq r hr hpq hrq
    rw [Finset.mem_image] at hp hq hr
    obtain ⟨p', hp', rfl⟩ := hp
    obtain ⟨q', hq', rfl⟩ := hq
    obtain ⟨r', hr', rfl⟩ := hr
    rw [euclidean_angle_const_mul hurot0]
    exact hangle p' hp' q' hq' r' hr' (fun h => hpq (by rw [h]))
      (fun h => hrq (by rw [h]))
  have hpmem : urot * C.w i ∈ S.image (fun z => urot * z) :=
    Finset.mem_image_of_mem _ (C.mem i)
  have hi0 : n - 2 < n := by omega
  have hi1 : n - 1 < n := by omega
  have hii : (⟨n - 2, hi0⟩ : Fin n) ≠ ⟨n - 1, hi1⟩ := by
    intro h
    have h2 : n - 2 = n - 1 := congrArg Fin.val h
    omega
  have h3 := three_le_card_dir_edges hn0 _ hcard' hangle' hpmem hii
  rw [← not_lt] at h3
  refine h3 ?_
  refine lt_of_le_of_lt (Finset.card_le_card
    (?_ : _ ⊆ ({urot * C.w si, urot * C.w pi1} : Finset ℂ))) ?_
  · intro z hz
    rw [Finset.mem_filter, Finset.mem_image] at hz
    obtain ⟨⟨q, hq, rfl⟩, hzne, hcol⟩ := hz
    have hqv : q ≠ C.w i := fun h => hzne (by rw [h])
    obtain ⟨r, t, hr, ht0, htW, hqf⟩ := C.win i q hq hqv
    have hrot : urot * q - urot * C.w i
        = (r : ℂ) * Complex.exp (((t - C.phi i : ℝ) : ℂ) * Complex.I) := by
      rw [← mul_sub, hqf, hurot, ← conj_exp_eq]
      have h := conj_exp_mul_exp (C.θ i + C.phi i) (t - C.phi i)
      rw [show ((C.θ i + C.phi i) + (t - C.phi i) : ℝ) = C.θ i + t from by ring] at h
      linear_combination (r : ℂ) * h
    rw [hrot] at hcol
    by_cases hlt : t < C.phi i
    · -- the direction points slightly below the axis
      have ht0' : t = 0 := by
        rcases eq_or_lt_of_le ht0 with h | h
        · exact h.symm
        · exact (hstepA q hq r t hr h hlt hqf).elim
      have hqray : q - C.w i = (r : ℂ)
          * Complex.exp ((C.θ i : ℂ) * Complex.I) := by
        rw [hqf, ht0', add_zero]
      have : q = C.w si :=
        eq_of_same_ray hgen (C.mem i) (C.mem si) hq (C.len_pos hn i) hr
          hBform hqray
      rw [this]
      simp
    · -- the direction points at or above the axis
      rw [not_lt] at hlt
      have hnn : 0 ≤ t - C.phi i := by linarith
      have hub : t - C.phi i < π := by linarith [hφi.1]
      rw [dirIndex_of_polar_nonneg hr hnn hub] at hcol
      have hfl : (0 : ℤ) ≤ ⌊(n : ℝ) * ((t - C.phi i) / π)⌋ := by
        apply Int.floor_nonneg.mpr
        positivity
      have hbig : ((n : ℝ) - 2) ≤ (n : ℝ) * ((t - C.phi i) / π) := by
        have hval : ((n : ℤ) - 2 : ℤ) ≤ ⌊(n : ℝ) * ((t - C.phi i) / π)⌋ := by
          rcases hcol with h | h
          · have h' : (⌊(n : ℝ) * ((t - C.phi i) / π)⌋).toNat = n - 2 := h
            omega
          · have h' : (⌊(n : ℝ) * ((t - C.phi i) / π)⌋).toNat = n - 1 := h
            omega
        have := Int.le_floor.mp hval
        push_cast at this
        linarith
      have hgeo : (1 - 1 / (n : ℝ)) * π - π / n + C.phi i ≤ t := by
        rw [hWid]
        have hmul : ((n : ℝ) - 2) * π ≤ (n : ℝ) * (t - C.phi i) := by
          have hd : (n : ℝ) * ((t - C.phi i) / π) * π = (n : ℝ) * (t - C.phi i) := by
            field_simp
          nlinarith
        nlinarith
      have hteq : t = (1 - 1 / (n : ℝ)) * π := by
        rcases eq_or_lt_of_le htW with h | h
        · exact h
        · exact (hstepB q hq r t hr (by linarith) h hqf).elim
      have hqray : q - C.w i = (r : ℂ)
          * Complex.exp (((C.θ i + (1 - 1 / (n : ℝ)) * π : ℝ) : ℂ) * Complex.I) := by
        rw [hqf, hteq]
      have : q = C.w pi1 :=
        eq_of_same_ray hgen (C.mem i) (C.mem pi1) hq
          (norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => hpine (C.inj h)))) hr
          hDform hqray
      rw [this]
      simp
  · exact lt_of_le_of_lt (Finset.card_insert_le _ _) (by simp)

/-- The mirrored form of the dichotomy. -/
theorem RigidConfig.phi_dichotomy' {n : ℕ} {S : Finset ℂ} (C : RigidConfig n S) :
    (∀ i, C.phi (pred2 n i) = C.phi i) ∨ (∃ i, C.phi (pred2 n i) < C.phi i) := by
  by_cases h : ∀ i, C.phi (pred2 n i) = C.phi i
  · exact Or.inl h
  refine Or.inr ?_
  by_contra hcon
  refine h (fun i => ?_)
  have hle : ∀ j, C.phi j ≤ C.phi (pred2 n j) :=
    fun j => not_lt.mp (fun hj => hcon ⟨j, hj⟩)
  have hsum : ∑ j : Fin (2 * n), (C.phi (pred2 n j) - C.phi j) = 0 := by
    rw [Finset.sum_sub_distrib, Equiv.sum_comp (pred2 n) C.phi, sub_self]
  have hnn : ∀ j ∈ (Finset.univ : Finset (Fin (2 * n))),
      0 ≤ C.phi (pred2 n j) - C.phi j := fun j _ => sub_nonneg.mpr (hle j)
  exact sub_eq_zero.mp
    ((Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum i (Finset.mem_univ i))

/-- **M4: only the first alternative survives.**  The angles `φ` are constant
along the doubled cyclic predecessor. -/
theorem RigidConfig.phi_const {n : ℕ} (hn : 3 ≤ n) {S : Finset ℂ}
    (hcard : S.card = 2 ^ n)
    (hangle : ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
      EuclideanGeometry.angle p q r ≤ (1 - 1 / (n : ℝ)) * π)
    (hgen : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set ℂ))
    (C : RigidConfig n S) :
    ∀ i, C.phi (pred2 n i) = C.phi i := by
  rcases C.phi_dichotomy' with h | ⟨i, hi⟩
  · exact h
  · exact (case2b_false hn hcard hangle hgen C hi).elim

/-! ## M4d2: the regular `n`-gon in case 2a -/

lemma zeta_re (n : ℕ) : (zeta n).re = Real.cos (π / n) := by
  rw [zeta, Complex.exp_ofReal_mul_I_re]

/-- Positive combinations of `1` and `ζ` with the same argument are
proportional. -/
lemma mul_eq_of_arg_eq {n : ℕ} (hn : 3 ≤ n) {x₁ y₁ x₂ y₂ : ℝ}
    (hx₁ : 0 < x₁) (hy₁ : 0 < y₁) (hx₂ : 0 < x₂) (hy₂ : 0 < y₂)
    (h : Complex.arg ((x₁ : ℂ) + (y₁ : ℂ) * zeta n)
      = Complex.arg ((x₂ : ℂ) + (y₂ : ℂ) * zeta n)) :
    x₂ * y₁ = x₁ * y₂ := by
  obtain ⟨hp1, hp2⟩ := pi_div_n_mem hn
  have hsin : 0 < Real.sin (π / n) := Real.sin_pos_of_pos_of_lt_pi hp1 hp2
  have hre : ∀ x y : ℝ, ((x : ℂ) + (y : ℂ) * zeta n).re
      = x + y * Real.cos (π / n) := by
    intro x y
    rw [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, zeta_re]
  have him : ∀ x y : ℝ, ((x : ℂ) + (y : ℂ) * zeta n).im
      = y * Real.sin (π / n) := by
    intro x y
    rw [Complex.add_im, Complex.ofReal_im, zero_add, Complex.im_ofReal_mul, zeta_im]
  have hne : ∀ x y : ℝ, 0 < x → 0 < y → (x : ℂ) + (y : ℂ) * zeta n ≠ 0 := by
    intro x y _ hy hz
    have := him x y
    rw [hz, Complex.zero_im] at this
    exact absurd this.symm (ne_of_gt (mul_pos hy hsin))
  have hn₁ : 0 < ‖(x₁ : ℂ) + (y₁ : ℂ) * zeta n‖ :=
    norm_pos_iff.mpr (hne x₁ y₁ hx₁ hy₁)
  have hn₂ : 0 < ‖(x₂ : ℂ) + (y₂ : ℂ) * zeta n‖ :=
    norm_pos_iff.mpr (hne x₂ y₂ hx₂ hy₂)
  have hkey : ((‖(x₂ : ℂ) + (y₂ : ℂ) * zeta n‖ : ℝ) : ℂ)
        * ((x₁ : ℂ) + (y₁ : ℂ) * zeta n)
      = ((‖(x₁ : ℂ) + (y₁ : ℂ) * zeta n‖ : ℝ) : ℂ)
        * ((x₂ : ℂ) + (y₂ : ℂ) * zeta n) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I ((x₁ : ℂ) + (y₁ : ℂ) * zeta n)]
    conv_rhs => rw [← Complex.norm_mul_exp_arg_mul_I ((x₂ : ℂ) + (y₂ : ℂ) * zeta n)]
    rw [h]
    ring
  have hkim := congrArg Complex.im hkey
  rw [Complex.im_ofReal_mul, Complex.im_ofReal_mul, him, him] at hkim
  have hkre := congrArg Complex.re hkey
  rw [Complex.re_ofReal_mul, Complex.re_ofReal_mul, hre, hre] at hkre
  have hy : ‖(x₂ : ℂ) + (y₂ : ℂ) * zeta n‖ * y₁
      = ‖(x₁ : ℂ) + (y₁ : ℂ) * zeta n‖ * y₂ := by
    apply mul_right_cancel₀ (ne_of_gt hsin)
    linear_combination hkim
  have hx : ‖(x₂ : ℂ) + (y₂ : ℂ) * zeta n‖ * x₁
      = ‖(x₁ : ℂ) + (y₁ : ℂ) * zeta n‖ * x₂ := by
    linear_combination hkre - Real.cos (π / n) * hy
  apply mul_left_cancel₀ hn₂.ne'
  linear_combination x₂ * hy - y₂ * hx

/-- **M5 (step 2): the edge lengths alternate.** -/
theorem RigidConfig.len_parity {n : ℕ} (hn : 3 ≤ n) {S : Finset ℂ}
    (C : RigidConfig n S) (hconst : ∀ i, C.phi (pred2 n i) = C.phi i)
    (h0 : 0 < 2 * n) (h1 : 1 < 2 * n) :
    (∀ k : ℕ, ∀ hk : 2 * k < 2 * n, C.len ⟨2 * k, hk⟩ = C.len ⟨0, h0⟩) ∧
      (∀ k : ℕ, ∀ hk : 2 * k + 1 < 2 * n,
        C.len ⟨2 * k + 1, hk⟩ = C.len ⟨1, h1⟩) := by
  obtain ⟨r, hrdef⟩ : ∃ r : Fin (2 * n) → ℝ,
      r = fun i => C.len (finRotate (2 * n) i) / C.len i := ⟨_, rfl⟩
  have hlp : ∀ i, 0 < C.len i := fun i => C.len_pos hn i
  have hrpos : ∀ i, 0 < r i := by
    intro i; rw [hrdef]; exact div_pos (hlp _) (hlp i)
  have hsucc : ∀ j : ℕ, ∀ hj : j + 1 < 2 * n,
      C.len ⟨j + 1, hj⟩ = r ⟨j, by omega⟩ * C.len ⟨j, by omega⟩ := by
    intro j hj
    rw [hrdef]
    simp only
    rw [finRotate_val_of_lt ⟨j, by omega⟩ (by exact hj)]
    exact (div_mul_cancel₀ _ (hlp ⟨j, by omega⟩).ne').symm
  -- the ratio only depends on the parity
  have hstep : ∀ j : ℕ, ∀ hj : j + 2 < 2 * n,
      r ⟨j + 2, hj⟩ = r ⟨j, by omega⟩ := by
    intro j hj
    have hp : pred2 n ⟨j + 2, hj⟩ = ⟨j, by omega⟩ := by
      rw [pred2, Equiv.trans_apply,
        finRotate_symm_of_pos ⟨j + 2, hj⟩ (by show 0 < j + 2; omega)]
      rw [finRotate_symm_of_pos ⟨j + 2 - 1, by omega⟩ (by show 0 < j + 2 - 1; omega)]
      exact Fin.ext (by show j + 2 - 1 - 1 = j; omega)
    have hc := hconst ⟨j + 2, hj⟩
    rw [hp] at hc
    have hmul := mul_eq_of_arg_eq hn (hlp ⟨j, by omega⟩) (hlp (finRotate (2 * n) ⟨j, by omega⟩))
      (hlp ⟨j + 2, hj⟩) (hlp (finRotate (2 * n) ⟨j + 2, hj⟩)) hc
    rw [hrdef]
    simp only
    rw [div_eq_div_iff (hlp ⟨j + 2, hj⟩).ne' (hlp ⟨j, by omega⟩).ne']
    linear_combination -hmul
  have hre : ∀ m : ℕ, ∀ hm : 2 * m < 2 * n, r ⟨2 * m, hm⟩ = r ⟨0, h0⟩ := by
    intro m
    induction m with
    | zero => intro hm; rfl
    | succ m ih =>
      intro hm
      have hlt : 2 * m + 2 < 2 * n := by omega
      have := hstep (2 * m) hlt
      rw [show (⟨2 * (m + 1), hm⟩ : Fin (2 * n)) = ⟨2 * m + 2, hlt⟩ from
        Fin.ext (by show 2 * (m + 1) = 2 * m + 2; omega), this]
      exact ih (by omega)
  have hro : ∀ m : ℕ, ∀ hm : 2 * m + 1 < 2 * n, r ⟨2 * m + 1, hm⟩ = r ⟨1, h1⟩ := by
    intro m
    induction m with
    | zero => intro hm; rfl
    | succ m ih =>
      intro hm
      have hlt : (2 * m + 1) + 2 < 2 * n := by omega
      have := hstep (2 * m + 1) hlt
      rw [show (⟨2 * (m + 1) + 1, hm⟩ : Fin (2 * n)) = ⟨(2 * m + 1) + 2, hlt⟩ from
        Fin.ext (by show 2 * (m + 1) + 1 = 2 * m + 1 + 2; omega), this]
      exact ih (by omega)
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = r ⟨0, h0⟩ * r ⟨1, h1⟩ := ⟨_, rfl⟩
  have htpos : 0 < t := by rw [htdef]; exact mul_pos (hrpos _) (hrpos _)
  have hev : ∀ m : ℕ, ∀ hm : 2 * m < 2 * n,
      C.len ⟨2 * m, hm⟩ = t ^ m * C.len ⟨0, h0⟩ := by
    intro m
    induction m with
    | zero =>
      intro hm
      rw [show (⟨2 * 0, hm⟩ : Fin (2 * n)) = ⟨0, h0⟩ from
        Fin.ext (by show 2 * 0 = 0; omega), pow_zero, one_mul]
    | succ m ih =>
      intro hm
      have h2 : 2 * m + 1 < 2 * n := by omega
      have h3 : 2 * m < 2 * n := by omega
      have hodd : C.len ⟨2 * m + 1, h2⟩ = r ⟨0, h0⟩ * (t ^ m * C.len ⟨0, h0⟩) := by
        rw [hsucc (2 * m) h2, hre m h3, ih h3]
      have hlt : 2 * m + 1 + 1 < 2 * n := by omega
      rw [show (⟨2 * (m + 1), hm⟩ : Fin (2 * n)) = ⟨2 * m + 1 + 1, hlt⟩ from
        Fin.ext (by show 2 * (m + 1) = 2 * m + 1 + 1; omega),
        hsucc (2 * m + 1) hlt, hro m h2, hodd, htdef]
      ring
  -- closing the cycle
  have hlast : 2 * (n - 1) + 1 < 2 * n := by omega
  have hfl : finRotate (2 * n) ⟨2 * (n - 1) + 1, hlast⟩ = ⟨0, h0⟩ :=
    finRotate_val_of_last h0 _ (by show 2 * (n - 1) + 1 + 1 = 2 * n; omega)
  have hrlast : r ⟨2 * (n - 1) + 1, hlast⟩
      = C.len ⟨0, h0⟩ / C.len ⟨2 * (n - 1) + 1, hlast⟩ := by
    rw [hrdef]
    simp only
    rw [hfl]
  have hoddlast : C.len ⟨2 * (n - 1) + 1, hlast⟩
      = r ⟨0, h0⟩ * (t ^ (n - 1) * C.len ⟨0, h0⟩) := by
    rw [hsucc (2 * (n - 1)) hlast, hre (n - 1) (by omega), hev (n - 1) (by omega)]
  have hL0 : 0 < C.len ⟨0, h0⟩ := hlp _
  have htn : t ^ n = 1 := by
    have h := hro (n - 1) hlast
    rw [hrlast] at h
    have hL : C.len ⟨0, h0⟩
        = r ⟨1, h1⟩ * C.len ⟨2 * (n - 1) + 1, hlast⟩ := by
      rw [div_eq_iff (hlp ⟨2 * (n - 1) + 1, hlast⟩).ne'] at h
      exact h
    rw [hoddlast] at hL
    have hpow : t ^ n = t ^ (n - 1) * t := by
      rw [← pow_succ]
      congr 1
      omega
    apply mul_right_cancel₀ hL0.ne'
    rw [one_mul]
    linear_combination (C.len ⟨0, h0⟩) * hpow
      + ((t ^ (n - 1)) * C.len ⟨0, h0⟩) * htdef - hL
  have ht1 : t = 1 := by
    rcases lt_trichotomy t 1 with h | h | h
    · exfalso
      have hlt := pow_lt_one₀ htpos.le h (by omega : n ≠ 0)
      rw [htn] at hlt
      exact lt_irrefl _ hlt
    · exact h
    · exfalso
      have hgt := one_lt_pow₀ h (by omega : n ≠ 0)
      rw [htn] at hgt
      exact lt_irrefl _ hgt
  have hlen1 : C.len ⟨1, h1⟩ = r ⟨0, h0⟩ * C.len ⟨0, h0⟩ := by
    have h := hsucc 0 (by omega : 0 + 1 < 2 * n)
    simpa using h
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · rw [hev k hk, ht1, one_pow, one_mul]
  · rw [hsucc (2 * k) hk, hre k (by omega), hev k (by omega), ht1, one_pow,
      one_mul, hlen1]

lemma zeta_sq_ne_one {n : ℕ} (hn : 3 ≤ n) : zeta n ^ 2 ≠ 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hlo : 0 < ((2 : ℕ) : ℝ) * (π / n) := by
    push_cast
    positivity
  have hhi : ((2 : ℕ) : ℝ) * (π / n) < π := by
    push_cast
    rw [mul_div_assoc'] at *
    rw [div_lt_iff₀ hn0]
    nlinarith
  intro h
  have him : (zeta n ^ 2).im = Real.sin (((2 : ℕ) : ℝ) * (π / n)) := by
    rw [zeta_pow, Complex.exp_ofReal_mul_I_im]
  rw [h, Complex.one_im] at him
  exact absurd him.symm (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hlo hhi))

/-- **M5: in case 2a the even vertices form a regular `n`-gon.** -/
theorem regular_ngon {n : ℕ} (hn : 3 ≤ n) {S : Finset ℂ}
    (hcard : S.card = 2 ^ n)
    (hangle : ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
      EuclideanGeometry.angle p q r ≤ (1 - 1 / (n : ℝ)) * π)
    (hgen : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set ℂ))
    (C : RigidConfig n S) :
    ∃ O Rc : ℂ, Rc ≠ 0 ∧
      ∀ k : ℕ, ∀ hk : 2 * k < 2 * n,
        C.w ⟨2 * k, hk⟩ = O + Rc * (zeta n ^ 2) ^ k := by
  obtain ⟨hp1, hp2⟩ := pi_div_n_mem hn
  have h0 : 0 < 2 * n := by omega
  have h1 : 1 < 2 * n := by omega
  have hconst := C.phi_const hn hcard hangle hgen
  obtain ⟨hev, hod⟩ := C.len_parity hn hconst h0 h1
  obtain ⟨u₀, hu₀⟩ : ∃ z : ℂ, z = Complex.exp ((C.θ ⟨0, h0⟩ : ℂ) * Complex.I) :=
    ⟨_, rfl⟩
  have hu₀0 : u₀ ≠ 0 := by rw [hu₀]; exact Complex.exp_ne_zero _
  obtain ⟨Cc, hCc⟩ : ∃ z : ℂ, z = u₀ * ((C.len ⟨0, h0⟩ : ℂ)
      + (C.len ⟨1, h1⟩ : ℂ) * zeta n) := ⟨_, rfl⟩
  have hsin : 0 < Real.sin (π / n) := Real.sin_pos_of_pos_of_lt_pi hp1 hp2
  have hfac0 : (C.len ⟨0, h0⟩ : ℂ) + (C.len ⟨1, h1⟩ : ℂ) * zeta n ≠ 0 := by
    intro hz
    have him : ((C.len ⟨0, h0⟩ : ℂ) + (C.len ⟨1, h1⟩ : ℂ) * zeta n).im
        = C.len ⟨1, h1⟩ * Real.sin (π / n) := by
      rw [Complex.add_im, Complex.ofReal_im, zero_add, Complex.im_ofReal_mul, zeta_im]
    rw [hz, Complex.zero_im] at him
    exact absurd him.symm (ne_of_gt (mul_pos (C.len_pos hn ⟨1, h1⟩) hsin))
  have hCc0 : Cc ≠ 0 := by rw [hCc]; exact mul_ne_zero hu₀0 hfac0
  have hω : zeta n ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr (zeta_sq_ne_one hn)
  obtain ⟨Rc, hRc⟩ : ∃ z : ℂ, z = Cc / (zeta n ^ 2 - 1) := ⟨_, rfl⟩
  have hRc0 : Rc ≠ 0 := by rw [hRc]; exact div_ne_zero hCc0 hω
  have hRcω : Rc * (zeta n ^ 2 - 1) = Cc := by rw [hRc]; field_simp
  -- the step from one even vertex to the next
  have key : ∀ k : ℕ, ∀ hk : 2 * (k + 1) < 2 * n,
      C.w ⟨2 * (k + 1), hk⟩ - C.w ⟨2 * k, by omega⟩
        = Cc * (zeta n ^ 2) ^ k := by
    intro k hk
    have hk0 : 2 * k < 2 * n := by omega
    have hk1 : 2 * k + 1 < 2 * n := by omega
    have hk2 : 2 * k + 1 + 1 < 2 * n := by omega
    have he1 : C.w ⟨2 * k + 1, hk1⟩ - C.w ⟨2 * k, hk0⟩
        = (C.len ⟨2 * k, hk0⟩ : ℂ) * u₀ * zeta n ^ (2 * k) := by
      have h := C.edge_eq hn h0 ⟨2 * k, hk0⟩
      rw [finRotate_val_of_lt ⟨2 * k, hk0⟩ (by exact hk1), ← hu₀] at h
      exact h
    have he2 : C.w ⟨2 * k + 1 + 1, hk2⟩ - C.w ⟨2 * k + 1, hk1⟩
        = (C.len ⟨2 * k + 1, hk1⟩ : ℂ) * u₀ * zeta n ^ (2 * k + 1) := by
      have h := C.edge_eq hn h0 ⟨2 * k + 1, hk1⟩
      rw [finRotate_val_of_lt ⟨2 * k + 1, hk1⟩ (by exact hk2), ← hu₀] at h
      exact h
    rw [hev k hk0] at he1
    rw [hod k hk1] at he2
    have hpow1 : zeta n ^ (2 * k) = (zeta n ^ 2) ^ k := by rw [pow_mul]
    have hpow2 : zeta n ^ (2 * k + 1) = (zeta n ^ 2) ^ k * zeta n := by
      rw [pow_succ, hpow1]
    rw [show (⟨2 * (k + 1), hk⟩ : Fin (2 * n)) = ⟨2 * k + 1 + 1, hk2⟩ from
      Fin.ext (by show 2 * (k + 1) = 2 * k + 1 + 1; omega), hCc]
    rw [hpow1] at he1
    rw [hpow2] at he2
    linear_combination he1 + he2
  refine ⟨C.w ⟨0, h0⟩ - Rc, Rc, hRc0, ?_⟩
  intro k
  induction k with
  | zero =>
    intro hk
    rw [show (⟨2 * 0, hk⟩ : Fin (2 * n)) = ⟨0, h0⟩ from
      Fin.ext (by show 2 * 0 = 0; omega), pow_zero]
    ring
  | succ k ih =>
    intro hk
    have hk0 : 2 * k < 2 * n := by omega
    have hd := key k hk
    have hi := ih hk0
    linear_combination hd + hi - ((zeta n ^ 2) ^ k) * hRcω

/-! ## M4d3: interior point toolkit -/

/-- **P1: the angle is invariant under translation.** -/
lemma euclidean_angle_add_const (z p q r : ℂ) :
    EuclideanGeometry.angle (p + z) (q + z) (r + z)
      = EuclideanGeometry.angle p q r := by
  simp only [EuclideanGeometry.angle, vsub_eq_sub]
  congr 1 <;> ring

/-- **P2: a point strictly inside a triangle sees the three sides under
angles adding up to a full turn.** -/
theorem angle_sum_eq_two_pi_of_interior {a b c x : ℂ} {α β γ : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hsum : α + β + γ = 1)
    (hx : x = α • a + β • b + γ • c)
    (hnc : ¬ Collinear ℝ ({a, b, c} : Set ℂ)) :
    EuclideanGeometry.angle a x b + EuclideanGeometry.angle b x c
      + EuclideanGeometry.angle c x a = 2 * π := by
  have hαeq : α = 1 - β - γ := by linarith
  subst hαeq
  have hβγ : (0 : ℝ) < β + γ := by linarith
  have hβγne : β + γ ≠ 0 := ne_of_gt hβγ
  have hαC : (((1 - β - γ : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hα)
  have hβC : ((β : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hβ)
  have hγC : ((γ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hγ)
  have hβγC : ((β : ℝ) : ℂ) + ((γ : ℝ) : ℂ) ≠ 0 := by
    have h := Complex.ofReal_ne_zero.mpr hβγne
    push_cast at h
    exact h
  have hbcne : b ≠ c := ne₂₃_of_not_collinear hnc
  -- `d` is the point where the ray `a → x` meets the side `b c`
  obtain ⟨d, hd_def⟩ : ∃ d : ℂ, d = (β / (β + γ) : ℝ) • b + (γ / (β + γ) : ℝ) • c :=
    ⟨_, rfl⟩
  have hwbdc : Wbtw ℝ b d c := by
    rw [← mem_segment_iff_wbtw]
    exact ⟨β / (β + γ), γ / (β + γ), by positivity, by positivity, by field_simp,
      hd_def.symm⟩
  have hda : d ≠ a := by
    intro h
    apply hnc
    have hcol := hwbdc.collinear
    rw [h] at hcol
    rwa [Set.insert_comm] at hcol
  have hdiff_db : d - b = ((γ : ℝ) : ℂ) * (c - b) / (((β : ℝ) : ℂ) + ((γ : ℝ) : ℂ)) := by
    rw [hd_def]; simp only [Complex.real_smul]; push_cast; field_simp; ring
  have hdiff_dc : d - c = ((β : ℝ) : ℂ) * (b - c) / (((β : ℝ) : ℂ) + ((γ : ℝ) : ℂ)) := by
    rw [hd_def]; simp only [Complex.real_smul]; push_cast; field_simp; ring
  have hdb : d ≠ b := by
    rw [← sub_ne_zero, hdiff_db]
    exact div_ne_zero (mul_ne_zero hγC (sub_ne_zero.mpr hbcne.symm)) hβγC
  have hdc : d ≠ c := by
    rw [← sub_ne_zero, hdiff_dc]
    exact div_ne_zero (mul_ne_zero hβC (sub_ne_zero.mpr hbcne)) hβγC
  have hdiff_xa : x - a = (((β : ℝ) : ℂ) + ((γ : ℝ) : ℂ)) * (d - a) := by
    rw [hx, hd_def]; simp only [Complex.real_smul]; push_cast; field_simp; ring
  have hdiff_xd : x - d = (((1 - β - γ : ℝ)) : ℂ) * (a - d) := by
    rw [hx, hd_def]; simp only [Complex.real_smul]; push_cast; field_simp; ring
  have hxane : x ≠ a := by
    rw [← sub_ne_zero, hdiff_xa]
    exact mul_ne_zero hβγC (sub_ne_zero.mpr hda)
  have hxdne : x ≠ d := by
    rw [← sub_ne_zero, hdiff_xd]
    exact mul_ne_zero hαC (sub_ne_zero.mpr (Ne.symm hda))
  have hwaxd : Wbtw ℝ a x d := by
    rw [← mem_segment_iff_wbtw]
    refine ⟨1 - β - γ, β + γ, by linarith, by linarith, by ring, ?_⟩
    rw [hx, hd_def]; simp only [Complex.real_smul]; push_cast; field_simp; ring
  have hsaxd : Sbtw ℝ a x d := ⟨hwaxd, hxane, hxdne⟩
  have hsbdc : Sbtw ℝ b d c := ⟨hwbdc, hdb, hdc⟩
  have hpi : EuclideanGeometry.angle a x d = π := Sbtw.angle₁₂₃_eq_pi hsaxd
  have h1 : EuclideanGeometry.angle b x a + EuclideanGeometry.angle b x d = π :=
    EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_pi b hpi
  have h2 : EuclideanGeometry.angle c x a + EuclideanGeometry.angle c x d = π :=
    EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_pi c hpi
  have h3 : EuclideanGeometry.angle b x d + EuclideanGeometry.angle d x c
      = EuclideanGeometry.angle b x c :=
    EuclideanGeometry.angle_add_angle_eq_of_sbtw hsbdc
  have hc1 : EuclideanGeometry.angle a x b = EuclideanGeometry.angle b x a :=
    EuclideanGeometry.angle_comm a x b
  have hc2 : EuclideanGeometry.angle d x c = EuclideanGeometry.angle c x d :=
    EuclideanGeometry.angle_comm d x c
  linarith

/-- **P3 (arithmetic): `2n + 2 ≤ 2ⁿ` for `n ≥ 3`.** -/
lemma two_le_pow_sub (n : ℕ) (hn : 3 ≤ n) : 2 * n + 2 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h2 : 2 ≤ 2 ^ n := le_trans (by omega) ih
    have hpow : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by ring
    omega

/-- **P3: at the extremal cardinality there are at least two points of `S`
which are not vertices of the rigid configuration.** -/
theorem exists_two_interior {n : ℕ} (hn : 3 ≤ n) {S : Finset ℂ}
    (hcard : S.card = 2 ^ n) (C : RigidConfig n S) :
    ∃ q₁ ∈ S, ∃ q₂ ∈ S, q₁ ≠ q₂ ∧
      (∀ i, q₁ ≠ C.w i) ∧ (∀ i, q₂ ≠ C.w i) := by
  classical
  obtain ⟨V, hV⟩ : ∃ V : Finset ℂ, V = Finset.univ.image C.w := ⟨_, rfl⟩
  have hVcard : V.card = 2 * n := by
    rw [hV, Finset.card_image_of_injective _ C.inj, Finset.card_univ, Fintype.card_fin]
  have hVsub : V ⊆ S := by
    intro z hz
    rw [hV, Finset.mem_image] at hz
    obtain ⟨i, -, rfl⟩ := hz
    exact C.mem i
  have hsd : (S \ V).card = 2 ^ n - 2 * n := by
    rw [Finset.card_sdiff_of_subset hVsub, hcard, hVcard]
  have h2 : 1 < (S \ V).card := by
    have h := two_le_pow_sub n hn
    omega
  obtain ⟨q₁, hq₁, q₂, hq₂, hne⟩ := Finset.one_lt_card.mp h2
  rw [Finset.mem_sdiff] at hq₁ hq₂
  refine ⟨q₁, hq₁.1, q₂, hq₂.1, hne, ?_, ?_⟩
  · intro i h
    exact hq₁.2 (by rw [hV, Finset.mem_image]; exact ⟨i, Finset.mem_univ i, h.symm⟩)
  · intro i h
    exact hq₂.2 (by rw [hV, Finset.mem_image]; exact ⟨i, Finset.mem_univ i, h.symm⟩)

lemma finRotate_symm_ne_self {k : ℕ} (hk3 : 3 ≤ k) (i : Fin k) :
    (finRotate k).symm i ≠ i := by
  intro h
  refine finRotate_ne_self hk3 i ?_
  have h2 : finRotate k ((finRotate k).symm i) = finRotate k i := by rw [h]
  rw [Equiv.apply_symm_apply] at h2
  exact h2.symm

/-- **P4: at every vertex of the rigid configuration the two neighbouring
vertices subtend exactly the maximal angle `(1 - 1/n)·π`.** -/
lemma vertex_angle_eq {n : ℕ} (hn : 3 ≤ n) {S : Finset ℂ}
    (C : RigidConfig n S) (i : Fin (2 * n)) :
    EuclideanGeometry.angle (C.w (finRotate (2 * n) i)) (C.w i)
      (C.w ((finRotate (2 * n)).symm i)) = (1 - 1 / (n : ℝ)) * π := by
  have hπ := Real.pi_pos
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hinv : 0 < 1 / (n : ℝ) := by positivity
  have hinv1 : 1 / (n : ℝ) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  have hW0 : 0 ≤ (1 - 1 / (n : ℝ)) * π := by nlinarith
  have hWπ : (1 - 1 / (n : ℝ)) * π < π := by nlinarith
  have hsucc : C.w (finRotate (2 * n) i) - C.w i
      = ((‖C.w (finRotate (2 * n) i) - C.w i‖ : ℝ) : ℂ)
        * Complex.exp (((C.θ i + 0 : ℝ) : ℂ) * Complex.I) := by
    rw [add_zero]; exact C.succ i
  have hr₁ : 0 < ‖C.w (finRotate (2 * n) i) - C.w i‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (C.succ_ne hn i))
  have hr₂ : 0 < ‖C.w ((finRotate (2 * n)).symm i) - C.w i‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr
      (fun h => finRotate_symm_ne_self (by omega) i (C.inj h)))
  have habs : |(0 : ℝ) - (1 - 1 / (n : ℝ)) * π| = (1 - 1 / (n : ℝ)) * π := by
    rw [zero_sub, abs_neg, abs_of_nonneg hW0]
  have key := angle_eq_abs_of_polar hr₁ hr₂ (by rw [habs]; exact hWπ) hsucc (C.pred i)
  rw [key, habs]

lemma nonneg_of_mul_eq_nonneg {a b c : ℝ} (hc : 0 < c) (h : b * c = a) (ha : 0 ≤ a) :
    0 ≤ b := by
  by_contra hcon
  rw [not_le] at hcon
  nlinarith [mul_pos (neg_pos.mpr hcon) hc]

lemma finRotate_ne_finRotate_symm {k : ℕ} (hk3 : 3 ≤ k) (i : Fin k) :
    finRotate k i ≠ (finRotate k).symm i := by
  intro h
  have hik := i.isLt
  have hval : ((finRotate k i : Fin k) : ℕ) = (((finRotate k).symm i : Fin k) : ℕ) := by
    rw [h]
  rw [finRotate_val] at hval
  rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | h0
  · rw [finRotate_symm_of_zero (by omega) i h0] at hval
    simp only at hval
    rw [h0, Nat.mod_eq_of_lt (by omega)] at hval
    omega
  · rw [finRotate_symm_of_pos i h0] at hval
    simp only at hval
    rcases Nat.lt_or_ge ((i : ℕ) + 1) k with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at hval; omega
    · rw [show (i : ℕ) + 1 = k from by omega, Nat.mod_self] at hval; omega

/-- **P5 (core).**  A point `x` of `S` other than the three vertices `v`, `A`,
`B` of a maximal-angle corner lies beyond the chord `A B`. -/
theorem interior_beyond_chord_aux {n : ℕ} (hn : 3 ≤ n) {S : Finset ℂ}
    (hangle : ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
      EuclideanGeometry.angle p q r ≤ (1 - 1 / (n : ℝ)) * π)
    (hgen : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set ℂ))
    {v A B x : ℂ} {θ : ℝ}
    (hvS : v ∈ S) (hAS : A ∈ S) (hBS : B ∈ S) (hxS : x ∈ S)
    (hxv : x ≠ v) (hxA : x ≠ A) (hxB : x ≠ B)
    (hAv : A ≠ v) (hBv : B ≠ v) (hAB : A ≠ B)
    (hAf : A - v = ((‖A - v‖ : ℝ) : ℂ)
      * Complex.exp (((θ + 0 : ℝ) : ℂ) * Complex.I))
    (hBf : B - v = ((‖B - v‖ : ℝ) : ℂ)
      * Complex.exp (((θ + (1 - 1 / (n : ℝ)) * π : ℝ) : ℂ) * Complex.I))
    (hwin : ∃ r t : ℝ, 0 < r ∧ 0 ≤ t ∧ t ≤ (1 - 1 / (n : ℝ)) * π ∧
      x - v = (r : ℂ) * Complex.exp (((θ + t : ℝ) : ℂ) * Complex.I))
    (hangAvB : EuclideanGeometry.angle A v B = (1 - 1 / (n : ℝ)) * π) :
    ∃ p q : ℝ, 0 < p ∧ 0 < q ∧ 1 < p + q ∧
      x - v = p • (A - v) + q • (B - v) := by
  have hπ := Real.pi_pos
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : 0 < 1 / (n : ℝ) := by positivity
  have hn1 : 1 / (n : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hW0 : 0 < (1 - 1 / (n : ℝ)) * π := by nlinarith
  have hWπ : (1 - 1 / (n : ℝ)) * π < π := by nlinarith
  obtain ⟨rx, t, hrx, ht0, htW, hxf⟩ := hwin
  have hrA : 0 < ‖A - v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hAv)
  have hrB : 0 < ‖B - v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hBv)
  have hsinW : 0 < Real.sin ((1 - 1 / (n : ℝ)) * π) :=
    Real.sin_pos_of_pos_of_lt_pi hW0 hWπ
  have hDpos : 0 < ‖A - v‖ * ‖B - v‖ * Real.sin ((1 - 1 / (n : ℝ)) * π) :=
    mul_pos (mul_pos hrA hrB) hsinW
  have hD : ((starRingEnd ℂ) (A - v) * (B - v)).im
      = ‖A - v‖ * ‖B - v‖ * Real.sin ((1 - 1 / (n : ℝ)) * π) := by
    rw [im_conj_polar_mul hAf hBf, sub_zero]
  have hqarea : ((starRingEnd ℂ) (A - v) * (x - v)).im
      = ‖A - v‖ * rx * Real.sin t := by
    rw [im_conj_polar_mul hAf hxf, sub_zero]
  have hparea : ((starRingEnd ℂ) (B - v) * (x - v)).im
      = ‖B - v‖ * rx * Real.sin (t - (1 - 1 / (n : ℝ)) * π) := by
    rw [im_conj_polar_mul hBf hxf]
  have hDne : ((starRingEnd ℂ) (A - v) * (B - v)).im ≠ 0 := by
    rw [hD]; exact ne_of_gt hDpos
  obtain ⟨p, q, hdec, hqid, hpid⟩ :=
    exists_decomp_of_im_ne_zero (X := A - v) (Y := B - v) (z := x - v) hDne
  have hswapD : ((starRingEnd ℂ) (B - v) * (A - v)).im
      = -(‖A - v‖ * ‖B - v‖ * Real.sin ((1 - 1 / (n : ℝ)) * π)) := by
    rw [im_conj_mul_swap, hD]
  rw [hqarea, hD] at hqid
  rw [hparea, hswapD] at hpid
  -- the two barycentric weights are nonnegative
  have hsint : 0 ≤ Real.sin t :=
    Real.sin_nonneg_of_nonneg_of_le_pi ht0 (le_of_lt (lt_of_le_of_lt htW hWπ))
  have hsintW : Real.sin (t - (1 - 1 / (n : ℝ)) * π) ≤ 0 := by
    have h1 : 0 ≤ Real.sin ((1 - 1 / (n : ℝ)) * π - t) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have h2 : Real.sin (t - (1 - 1 / (n : ℝ)) * π)
        = -Real.sin ((1 - 1 / (n : ℝ)) * π - t) := by
      rw [← Real.sin_neg]; congr 1; ring
    linarith
  have hq0 : 0 ≤ q :=
    nonneg_of_mul_eq_nonneg hDpos hqid.symm
      (mul_nonneg (mul_nonneg hrA.le hrx.le) hsint)
  have hpid' : p * (‖A - v‖ * ‖B - v‖ * Real.sin ((1 - 1 / (n : ℝ)) * π))
      = ‖B - v‖ * rx * (-Real.sin (t - (1 - 1 / (n : ℝ)) * π)) := by
    linear_combination hpid
  have hp0 : 0 ≤ p :=
    nonneg_of_mul_eq_nonneg hDpos hpid'
      (mul_nonneg (mul_nonneg hrB.le hrx.le) (by linarith))
  have hdecC : x - v = ((p : ℝ) : ℂ) * (A - v) + ((q : ℝ) : ℂ) * (B - v) := by
    rw [hdec, Complex.real_smul, Complex.real_smul]
  -- both weights are strictly positive
  have hqpos : 0 < q := by
    rcases lt_or_eq_of_le hq0 with h | h
    · exact h
    exfalso
    have hz : x - v = ((p : ℝ) : ℂ) * (A - v) := by
      rw [hdecC, ← h]; push_cast; ring
    refine hgen x hxS v hvS A hAS hxv (Ne.symm hAv) hxA ?_
    rw [collinear_iff_of_mem (show v ∈ ({x, v, A} : Set ℂ) by simp)]
    refine ⟨A - v, fun z hz2 => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz2
    rcases hz2 with rfl | rfl | rfl
    · exact ⟨p, by simp only [Complex.real_smul, vadd_eq_add]; linear_combination hz⟩
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp only [Complex.real_smul, vadd_eq_add]; push_cast; ring⟩
  have hppos : 0 < p := by
    rcases lt_or_eq_of_le hp0 with h | h
    · exact h
    exfalso
    have hz : x - v = ((q : ℝ) : ℂ) * (B - v) := by
      rw [hdecC, ← h]; push_cast; ring
    refine hgen x hxS v hvS B hBS hxv (Ne.symm hBv) hxB ?_
    rw [collinear_iff_of_mem (show v ∈ ({x, v, B} : Set ℂ) by simp)]
    refine ⟨B - v, fun z hz2 => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz2
    rcases hz2 with rfl | rfl | rfl
    · exact ⟨q, by simp only [Complex.real_smul, vadd_eq_add]; linear_combination hz⟩
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp only [Complex.real_smul, vadd_eq_add]; push_cast; ring⟩
  -- trichotomy on the total weight
  rcases lt_trichotomy (p + q) 1 with hlt | heq | hgt
  · exfalso
    have hnc : ¬ Collinear ℝ ({A, v, B} : Set ℂ) :=
      hgen A hAS v hvS B hBS hAv (Ne.symm hBv) hAB
    have hxeq : x = p • A + (1 - p - q) • v + q • B := by
      simp only [Complex.real_smul]
      push_cast
      linear_combination hdecC
    have hlt2 := angle_lt_angle_of_interior hppos
      (show (0 : ℝ) < 1 - p - q by linarith) hqpos (by ring) hxeq hnc
    rw [hangAvB] at hlt2
    have hle := hangle A hAS x hxS B hBS (Ne.symm hxA) (Ne.symm hxB)
    linarith
  · exfalso
    have hpq : ((p : ℝ) : ℂ) + ((q : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_add, heq]; norm_num
    have hxAB : x - A = ((q : ℝ) : ℂ) * (B - A) := by
      linear_combination hdecC + (A - v) * hpq
    refine hgen x hxS A hAS B hBS hxA hAB hxB ?_
    rw [collinear_iff_of_mem (show A ∈ ({x, A, B} : Set ℂ) by simp)]
    refine ⟨B - A, fun z hz2 => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz2
    rcases hz2 with rfl | rfl | rfl
    · exact ⟨q, by simp only [Complex.real_smul, vadd_eq_add]; linear_combination hxAB⟩
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp only [Complex.real_smul, vadd_eq_add]; push_cast; ring⟩
  · exact ⟨p, q, hppos, hqpos, hgt, hdec⟩

set_option linter.unusedVariables false in
/-- **P5: every non-vertex point of `S` lies beyond the chord joining the two
neighbours of any vertex.** -/
theorem interior_beyond_chord {n : ℕ} (hn : 3 ≤ n) {S : Finset ℂ}
    (hcard : S.card = 2 ^ n)
    (hangle : ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
      EuclideanGeometry.angle p q r ≤ (1 - 1 / (n : ℝ)) * π)
    (hgen : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set ℂ))
    (C : RigidConfig n S) {x : ℂ} (hxS : x ∈ S) (hxV : ∀ i, x ≠ C.w i)
    (i : Fin (2 * n)) :
    ∃ p q : ℝ, 0 < p ∧ 0 < q ∧ 1 < p + q ∧
      x - C.w i = p • (C.w (finRotate (2 * n) i) - C.w i)
        + q • (C.w ((finRotate (2 * n)).symm i) - C.w i) :=
  interior_beyond_chord_aux (θ := C.θ i) hn hangle hgen (C.mem i) (C.mem _)
    (C.mem _) hxS (hxV i) (hxV _) (hxV _) (C.succ_ne hn i)
    (fun h => finRotate_symm_ne_self (by omega) i (C.inj h))
    (fun h => finRotate_ne_finRotate_symm (by omega) i (C.inj h))
    (by rw [add_zero]; exact C.succ i) (C.pred i)
    (C.win i x hxS (hxV i)) (vertex_angle_eq hn C i)

/-! ## M4d4: Lemma 6 and final assembly -/

/-- Product-to-sum identity for cosines. -/
lemma cos_mul_cos_eq (X Y : ℝ) :
    Real.cos X * Real.cos Y = (Real.cos (X + Y) + Real.cos (X - Y)) / 2 := by
  rw [Real.cos_add, Real.cos_sub]; ring

/-- **Q1 (core).**  The scalar heart of Lemma 6, in normalised variables. -/
lemma outside_disk_core {s a ρ ψ : ℝ} (hs0 : 0 < s)
    (has : s ≤ a) (hasπ : a + 2 * s ≤ π) (hρ : 0 < ρ)
    (hV1 : -s ≤ ψ) (hV2 : ψ ≤ s)
    (hW1 : Real.cos (a + s) < ρ * Real.cos (ψ - (a + s)))
    (hW2 : ρ * Real.cos (ψ - a) < Real.cos a) :
    Real.cos (ψ - (2 * a + s)) < ρ * Real.cos s := by
  have hπ := Real.pi_pos
  have hs3 : 3 * s ≤ π := by linarith
  have hcs : 0 < Real.cos s := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = ψ - (2 * a + s) := ⟨_, rfl⟩
  rw [← hD]
  rcases lt_or_ge (-(π / 2)) D with hii | hmid
  · -- branch (ii): `D` is close to zero
    have hca : 0 < Real.cos (D + a) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
    by_contra hcon
    rw [not_lt] at hcon
    have harg : ψ - (a + s) = D + a := by rw [hD]; ring
    rw [harg] at hW1
    have key : Real.cos s * Real.cos (a + s) < Real.cos D * Real.cos (D + a) := by
      have h1 := mul_lt_mul_of_pos_left hW1 hcs
      have h2 := mul_le_mul_of_nonneg_right hcon hca.le
      nlinarith [h1, h2]
    have hid1 : Real.cos s * Real.cos (a + s)
        = (Real.cos (a + 2 * s) + Real.cos a) / 2 := by
      have h1 : Real.cos (a + 2 * s) = Real.cos (s + (a + s)) := by congr 1; ring
      have h2 : Real.cos a = Real.cos (s - (a + s)) := by
        rw [show s - (a + s) = -a by ring, Real.cos_neg]
      rw [h1, h2, ← cos_mul_cos_eq]
    have hid2 : Real.cos D * Real.cos (D + a)
        = (Real.cos (2 * D + a) + Real.cos a) / 2 := by
      have h1 : Real.cos (2 * D + a) = Real.cos (D + (D + a)) := by congr 1; ring
      have h2 : Real.cos a = Real.cos (D - (D + a)) := by
        rw [show D - (D + a) = -a by ring, Real.cos_neg]
      rw [h1, h2, ← cos_mul_cos_eq]
    rw [hid1, hid2] at key
    have hx1 : a + 2 * s ≤ -(2 * D + a) := by linarith
    have hx2 : -(2 * D + a) ≤ π := by linarith
    have hcle := Real.cos_le_cos_of_nonneg_of_le_pi
      (show (0:ℝ) ≤ a + 2 * s by linarith) hx2 hx1
    rw [Real.cos_neg] at hcle
    linarith
  · rcases lt_or_ge D (-(3 * π / 2)) with hiii | hi
    · -- branch (iii): `D` is close to `-2π`
      have hs4 : s < π / 4 := by linarith
      have hcψa : Real.cos (ψ - a) < 0 := by
        have h := Real.cos_neg_of_pi_div_two_lt_of_lt
          (show π / 2 < a - ψ by linarith) (show a - ψ < π + π / 2 by linarith)
        rwa [show a - ψ = -(ψ - a) by ring, Real.cos_neg] at h
      have hdia : Real.cos s * Real.cos a ≤ Real.cos D * Real.cos (ψ - a) := by
        have hid1 : Real.cos s * Real.cos a
            = (Real.cos (a + s) + Real.cos (a - s)) / 2 := by
          have h1 : Real.cos (a + s) = Real.cos (s + a) := by congr 1; ring
          have h2 : Real.cos (a - s) = Real.cos (s - a) := by
            rw [show s - a = -(a - s) by ring, Real.cos_neg]
          rw [h1, h2, ← cos_mul_cos_eq]
        have hid2 : Real.cos D * Real.cos (ψ - a)
            = (Real.cos (2 * ψ - 3 * a - s) + Real.cos (a + s)) / 2 := by
          have h1 : Real.cos (2 * ψ - 3 * a - s) = Real.cos (D + (ψ - a)) := by
            congr 1; rw [hD]; ring
          have h2 : Real.cos (a + s) = Real.cos (D - (ψ - a)) := by
            rw [show D - (ψ - a) = -(a + s) by rw [hD]; ring, Real.cos_neg]
          rw [h1, h2, ← cos_mul_cos_eq]
        rw [hid1, hid2]
        have hu : Real.cos (a - s) ≤ Real.cos (2 * ψ - 3 * a - s) := by
          rw [← Real.cos_add_two_pi (2 * ψ - 3 * a - s)]
          rcases le_or_gt 0 (2 * ψ - 3 * a - s + 2 * π) with h | h
          · exact Real.cos_le_cos_of_nonneg_of_le_pi h (by linarith) (by linarith)
          · have h2 := Real.cos_le_cos_of_nonneg_of_le_pi
              (show (0:ℝ) ≤ -(2 * ψ - 3 * a - s + 2 * π) by linarith)
              (show a - s ≤ π by linarith)
              (show -(2 * ψ - 3 * a - s + 2 * π) ≤ a - s by linarith)
            rwa [Real.cos_neg] at h2
        linarith
      have h1 := mul_lt_mul_of_pos_left hW2 hcs
      nlinarith [h1, hdia, hcψa, hcs, hρ]
    · -- branch (i): `cos D ≤ 0`
      have hcD : Real.cos D ≤ 0 := by
        have h := Real.cos_nonpos_of_pi_div_two_le_of_le
          (show π / 2 ≤ -D by linarith) (show -D ≤ π + π / 2 by linarith)
        rwa [Real.cos_neg] at h
      nlinarith [mul_pos hρ hcs]

/-- **Q1.**  A point in the wedge `T_j` and in the Voronoi cell of the vertex `1`
lies outside the decision disk. -/
lemma outside_disk_key {n j : ℕ} (hn : 3 ≤ n) (hj1 : 1 ≤ j)
    (hj2 : j ≤ n - 2) {ρ ψ : ℝ} (hρ : 0 < ρ)
    (hV : |ψ| ≤ π / n)
    (hW1 : Real.cos (π * (j + 1) / n) < ρ * Real.cos (ψ - π * (j + 1) / n))
    (hW2 : ρ * Real.cos (ψ - π * j / n) < Real.cos (π * j / n)) :
    Real.cos (ψ - (2 * j + 1) * π / n) < ρ * Real.cos (π / n) := by
  have hπ := Real.pi_pos
  have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
  have hjn : (j : ℝ) + 2 ≤ (n : ℝ) := by
    have h : j + 2 ≤ n := by omega
    exact_mod_cast h
  have hs0 : (0 : ℝ) < π / n := div_pos hπ hnpos
  have hns : (n : ℝ) * (π / n) = π := by field_simp
  have has : π / n ≤ (j : ℝ) * (π / n) := by
    nlinarith [mul_nonneg (show (0:ℝ) ≤ (j : ℝ) - 1 by linarith) hs0.le]
  have hasπ : (j : ℝ) * (π / n) + 2 * (π / n) ≤ π := by
    nlinarith [mul_le_mul_of_nonneg_right hjn hs0.le]
  have e1 : π * ((j : ℝ) + 1) / n = (j : ℝ) * (π / n) + π / n := by ring
  have e2 : π * (j : ℝ) / n = (j : ℝ) * (π / n) := by ring
  have e3 : (2 * (j : ℝ) + 1) * π / n = 2 * ((j : ℝ) * (π / n)) + π / n := by ring
  rw [e1] at hW1
  rw [e2] at hW2
  rw [e3]
  exact outside_disk_core hs0 has hasπ hρ (by linarith [(abs_le.mp hV).1])
    (abs_le.mp hV).2 hW1 hW2


lemma im_conj_sub_polar_mul (u v ψ ρ β : ℝ) :
    ((Complex.exp ((u : ℂ) * Complex.I) - (ρ : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I))
        * (starRingEnd ℂ) (Complex.exp ((v : ℂ) * Complex.I)
            - (ρ : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I))
        * Complex.exp ((β : ℂ) * Complex.I)).im
      = Real.sin (u - v + β) - ρ * Real.sin (u - ψ + β)
        - ρ * Real.sin (ψ - v + β) + ρ ^ 2 * Real.sin β := by
  simp only [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.mul_im, Complex.mul_re, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  simp only [Real.sin_add, Real.sin_sub, Real.cos_sub]
  linear_combination (ρ ^ 2 * Real.sin β) * (Real.sin_sq_add_cos_sq ψ)

/-- **Q2a.**  The imaginary part of `Z = (A - z) * conj (B - z)`, where
`A = e^{i(a-s)}`, `B = e^{i(a+s)}` and `z = ρ e^{iψ}`. -/
lemma im_Z_eq (s a ψ ρ : ℝ) :
    ((Complex.exp (((a - s : ℝ) : ℂ) * Complex.I)
        - (ρ : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I))
      * (starRingEnd ℂ) (Complex.exp (((a + s : ℝ) : ℂ) * Complex.I)
        - (ρ : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I))).im
      = 2 * Real.sin s * (ρ * Real.cos (ψ - a) - Real.cos s) := by
  have h := im_conj_sub_polar_mul (a - s) (a + s) ψ ρ 0
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one,
    Real.sin_zero, mul_zero, add_zero] at h
  rw [h, show a - s - (a + s) = -(2 * s) by ring, Real.sin_neg]
  simp only [Real.sin_sub, Real.cos_sub, Real.sin_add, Real.cos_add, Real.sin_two_mul]
  ring

/-- **Q2a (rotated).**  The imaginary part of `Z · e^{2is}`. -/
lemma im_Z_mul_eq (s a ψ ρ : ℝ) :
    ((Complex.exp (((a - s : ℝ) : ℂ) * Complex.I)
        - (ρ : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I))
      * (starRingEnd ℂ) (Complex.exp (((a + s : ℝ) : ℂ) * Complex.I)
        - (ρ : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I))
      * Complex.exp ((((2 * s : ℝ)) : ℂ) * Complex.I)).im
      = 2 * ρ * Real.sin s * (ρ * Real.cos s - Real.cos (ψ - a)) := by
  rw [im_conj_sub_polar_mul (a - s) (a + s) ψ ρ (2 * s),
    show a - s - (a + s) + 2 * s = 0 by ring,
    show a - s - ψ + 2 * s = a + s - ψ by ring,
    show ψ - (a + s) + 2 * s = ψ - a + s by ring, Real.sin_zero]
  simp only [Real.sin_sub, Real.cos_sub, Real.sin_add, Real.cos_add, Real.sin_two_mul]
  ring

set_option linter.unusedVariables false in
/-- **Q2b.**  A `cot`-comparison: if `Z` lies in the lower half-plane but
`Z·e^{iβ}` lies in the upper half-plane, then `-arg Z < β`. -/
lemma angle_lt_of_im_neg_of_im_mul_pos {Z : ℂ} {β : ℝ}
    (hβ0 : 0 < β) (hβπ : β < π) (hIm : Z.im < 0)
    (hpos : 0 < (Z * Complex.exp ((β : ℂ) * Complex.I)).im) :
    -(Complex.arg Z) < β := by
  have hZ0 : Z ≠ 0 := by
    intro h
    rw [h, Complex.zero_im] at hIm
    exact lt_irrefl 0 hIm
  have hnorm : 0 < ‖Z‖ := norm_pos_iff.mpr hZ0
  have harglt : Complex.arg Z < 0 := Complex.arg_neg_iff.mpr hIm
  have hargπ : -π < Complex.arg Z := Complex.neg_pi_lt_arg Z
  rw [Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im] at hpos
  have hsin : 0 < Real.sin (β + Complex.arg Z) := by
    rw [Real.sin_add, Complex.cos_arg hZ0, Complex.sin_arg,
      show Real.sin β * (Z.re / ‖Z‖) + Real.cos β * (Z.im / ‖Z‖)
        = (Z.re * Real.sin β + Z.im * Real.cos β) / ‖Z‖ from by ring]
    exact div_pos (by linarith) hnorm
  have hkey : 0 < β + Complex.arg Z := by
    by_contra hc
    rw [not_lt] at hc
    have h1 : 0 ≤ Real.sin (-(β + Complex.arg Z)) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    rw [Real.sin_neg] at h1
    linarith
  linarith

/-- **Q2c (core).**  A point of the plane which is inside the chord of the arc
from `e^{i(a-s)}` to `e^{i(a+s)}` but outside the decision disk sees that chord
under an angle smaller than `2s`. -/
lemma central_angle_lt_core {s a ψ ρ : ℝ} (hs0 : 0 < s) (hs2 : 2 * s < π)
    (hρ : 0 < ρ)
    (hch : ρ * Real.cos (ψ - a) < Real.cos s)
    (hout : Real.cos (ψ - a) < ρ * Real.cos s) :
    EuclideanGeometry.angle (Complex.exp (((a - s : ℝ) : ℂ) * Complex.I))
        ((ρ : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I))
        (Complex.exp (((a + s : ℝ) : ℂ) * Complex.I)) < 2 * s := by
  have hπ := Real.pi_pos
  have hsin : 0 < Real.sin s := Real.sin_pos_of_pos_of_lt_pi hs0 (by linarith)
  obtain ⟨A, hA⟩ : ∃ A : ℂ, A = Complex.exp (((a - s : ℝ) : ℂ) * Complex.I) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℂ, B = Complex.exp (((a + s : ℝ) : ℂ) * Complex.I) := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z = (ρ : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I) := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : ℂ, Z = (A - z) * (starRingEnd ℂ) (B - z) := ⟨_, rfl⟩
  rw [← hA, ← hB, ← hz]
  have himZ : Z.im = 2 * Real.sin s * (ρ * Real.cos (ψ - a) - Real.cos s) := by
    rw [hZ, hA, hB, hz]; exact im_Z_eq s a ψ ρ
  have hZneg : Z.im < 0 := by rw [himZ]; nlinarith
  have himZω : (Z * Complex.exp (((2 * s : ℝ) : ℂ) * Complex.I)).im
      = 2 * ρ * Real.sin s * (ρ * Real.cos s - Real.cos (ψ - a)) := by
    rw [hZ, hA, hB, hz]; exact im_Z_mul_eq s a ψ ρ
  have hZωpos : 0 < (Z * Complex.exp (((2 * s : ℝ) : ℂ) * Complex.I)).im := by
    rw [himZω]
    nlinarith [mul_pos (mul_pos hρ hsin) (sub_pos.mpr hout)]
  have hkey := angle_lt_of_im_neg_of_im_mul_pos (Z := Z) (β := 2 * s)
    (by linarith) hs2 hZneg hZωpos
  have hZ0 : Z ≠ 0 := by
    intro h
    rw [h, Complex.zero_im] at hZneg
    exact lt_irrefl 0 hZneg
  have hAz : A - z ≠ 0 := by
    intro h
    exact hZ0 (by rw [hZ, h, zero_mul])
  have hBz : B - z ≠ 0 := by
    intro h
    exact hZ0 (by rw [hZ, h, map_zero, mul_zero])
  have hbridge : EuclideanGeometry.angle A z B
      = InnerProductGeometry.angle (A - z) (B - z) := by
    simp [EuclideanGeometry.angle, vsub_eq_sub]
  have hW : (starRingEnd ℂ) (A - z) * (B - z) = (starRingEnd ℂ) Z := by
    rw [hZ, map_mul, Complex.conj_conj]
  have hargconj : Complex.arg ((starRingEnd ℂ) Z) = -Complex.arg Z := by
    rw [Complex.arg_conj, if_neg]
    intro h
    have := Complex.arg_neg_iff.mpr hZneg
    linarith [h ▸ this]
  rw [hbridge, angle_eq_abs_arg hAz hBz, hW, hargconj,
    abs_of_nonneg (by linarith [Complex.arg_neg_iff.mpr hZneg] : (0:ℝ) ≤ -Complex.arg Z)]
  exact hkey


lemma conj_zeta_pow_mul (n m : ℕ) :
    (starRingEnd ℂ) (zeta n ^ m) * zeta n ^ m = 1 := by
  rw [zeta_pow, mul_comm]
  exact exp_mul_conj_exp _

lemma conj_zeta_mul (n : ℕ) : (starRingEnd ℂ) (zeta n) * zeta n = 1 := by
  have h := conj_zeta_pow_mul n 1
  rwa [pow_one] at h

lemma zeta_pow_two_pow_n {n : ℕ} (hn : 3 ≤ n) : (zeta n ^ 2) ^ n = 1 := by
  have hn0 : (n : ℝ) ≠ 0 := by
    have h : (0 : ℕ) < n := by omega
    positivity
  rw [← pow_mul, mul_comm 2 n, zeta_pow,
    show ((n * 2 : ℕ) : ℝ) * (π / n) = 2 * π from by push_cast; field_simp,
    show ((2 * π : ℝ) : ℂ) * Complex.I = 2 * π * Complex.I from by push_cast; ring]
  exact Complex.exp_two_pi_mul_I

/-- The normalised linear functional cutting off the `k`-th edge of the
regular `n`-gon. -/
noncomputable def edgeFun (n k : ℕ) (u : ℂ) : ℝ :=
  ((starRingEnd ℂ) (zeta n * (zeta n ^ 2) ^ k) * u).re

lemma edgeFun_vertex (n k : ℕ) :
    edgeFun n k ((zeta n ^ 2) ^ k) = Real.cos (π / n) := by
  unfold edgeFun
  rw [← pow_mul, map_mul, mul_assoc, conj_zeta_pow_mul, mul_one, Complex.conj_re,
    zeta_re]

lemma edgeFun_vertex_succ (n k : ℕ) :
    edgeFun n k ((zeta n ^ 2) ^ (k + 1)) = Real.cos (π / n) := by
  unfold edgeFun
  rw [← pow_mul, ← pow_mul]
  have h : (starRingEnd ℂ) (zeta n * zeta n ^ (2 * k)) * zeta n ^ (2 * (k + 1))
      = zeta n := by
    rw [map_mul, show 2 * (k + 1) = 2 * k + 2 from by ring, pow_add,
      show (starRingEnd ℂ) (zeta n) * (starRingEnd ℂ) (zeta n ^ (2 * k))
          * (zeta n ^ (2 * k) * zeta n ^ 2)
        = ((starRingEnd ℂ) (zeta n) * zeta n)
          * ((starRingEnd ℂ) (zeta n ^ (2 * k)) * zeta n ^ (2 * k)) * zeta n from by
        ring, conj_zeta_mul, conj_zeta_pow_mul]
    ring
  rw [h, zeta_re]

lemma edgeFun_add (n k : ℕ) (u v : ℂ) :
    edgeFun n k (u + v) = edgeFun n k u + edgeFun n k v := by
  unfold edgeFun
  rw [mul_add, Complex.add_re]

lemma edgeFun_sub (n k : ℕ) (u v : ℂ) :
    edgeFun n k (u - v) = edgeFun n k u - edgeFun n k v := by
  unfold edgeFun
  rw [mul_sub, Complex.sub_re]

lemma edgeFun_smul (n k : ℕ) (r : ℝ) (u : ℂ) :
    edgeFun n k ((r : ℂ) * u) = r * edgeFun n k u := by
  unfold edgeFun
  rw [show (starRingEnd ℂ) (zeta n * (zeta n ^ 2) ^ k) * ((r : ℂ) * u)
      = (r : ℂ) * ((starRingEnd ℂ) (zeta n * (zeta n ^ 2) ^ k) * u) from by ring,
    Complex.re_ofReal_mul]

/-- The odd vertices of the rigid configuration lie strictly beyond the chords
of the even `n`-gon. -/
lemma re_div_gt_cos {n : ℕ} (hn : 3 ≤ n) {l0 l1 : ℝ} (h0 : 0 < l0) (h1 : 0 < l1) :
    Real.cos (π / n) < (((l1 : ℂ) + (l0 : ℂ) * zeta n)
      / ((l0 : ℂ) + (l1 : ℂ) * zeta n)).re := by
  obtain ⟨hp1, hp2⟩ := pi_div_n_mem hn
  have hσ : 0 < Real.sin (π / n) := Real.sin_pos_of_pos_of_lt_pi hp1 hp2
  have hpy : Real.sin (π / n) ^ 2 + Real.cos (π / n) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq _
  have hDre : ((l0 : ℂ) + (l1 : ℂ) * zeta n).re = l0 + l1 * Real.cos (π / n) := by
    rw [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, zeta_re]
  have hDim : ((l0 : ℂ) + (l1 : ℂ) * zeta n).im = l1 * Real.sin (π / n) := by
    rw [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, zeta_im, zero_add]
  have hNre : ((l1 : ℂ) + (l0 : ℂ) * zeta n).re = l1 + l0 * Real.cos (π / n) := by
    rw [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, zeta_re]
  have hNim : ((l1 : ℂ) + (l0 : ℂ) * zeta n).im = l0 * Real.sin (π / n) := by
    rw [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, zeta_im, zero_add]
  have hD : ((l0 : ℂ) + (l1 : ℂ) * zeta n) ≠ 0 := by
    intro hz
    have := hDim
    rw [hz, Complex.zero_im] at this
    nlinarith
  have hns : 0 < Complex.normSq ((l0 : ℂ) + (l1 : ℂ) * zeta n) :=
    Complex.normSq_pos.mpr hD
  have hnsval : Complex.normSq ((l0 : ℂ) + (l1 : ℂ) * zeta n)
      = (l0 + l1 * Real.cos (π / n)) * (l0 + l1 * Real.cos (π / n))
        + l1 * Real.sin (π / n) * (l1 * Real.sin (π / n)) := by
    rw [Complex.normSq_apply, hDre, hDim]
  have hdiff : (l1 + l0 * Real.cos (π / n)) * (l0 + l1 * Real.cos (π / n))
      + l0 * Real.sin (π / n) * (l1 * Real.sin (π / n))
      - Real.cos (π / n) * ((l0 + l1 * Real.cos (π / n)) * (l0 + l1 * Real.cos (π / n))
        + l1 * Real.sin (π / n) * (l1 * Real.sin (π / n)))
      = 2 * l0 * l1 * Real.sin (π / n) ^ 2 := by
    linear_combination (-(l1 ^ 2 * Real.cos (π / n)) - l0 * l1) * hpy
  rw [Complex.div_re, hNre, hNim, hDre, hDim, ← add_div, lt_div_iff₀ hns,
    hnsval]
  nlinarith [hdiff, mul_pos (mul_pos h0 h1) (mul_pos hσ hσ)]

/-- The odd vertices of a rigid configuration lie strictly beyond the chord
joining their two even neighbours. -/
lemma odd_vertex_beyond {n : ℕ} (hn : 3 ≤ n) {S : Finset ℂ}
    (hcard : S.card = 2 ^ n)
    (hangle : ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
      EuclideanGeometry.angle p q r ≤ (1 - 1 / (n : ℝ)) * π)
    (hgen : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set ℂ))
    (C : RigidConfig n S) {O Rc : ℂ} (hRc : Rc ≠ 0)
    (hvert : ∀ k : ℕ, ∀ hk : 2 * k < 2 * n,
      C.w ⟨2 * k, hk⟩ = O + Rc * (zeta n ^ 2) ^ k)
    (k : ℕ) (hk1 : 2 * k + 1 < 2 * n) :
    Real.cos (π / n) < edgeFun n k ((C.w ⟨2 * k + 1, hk1⟩ - O) / Rc) := by
  obtain ⟨hp1, hp2⟩ := pi_div_n_mem hn
  have hsin : 0 < Real.sin (π / n) := Real.sin_pos_of_pos_of_lt_pi hp1 hp2
  have h0 : 0 < 2 * n := by omega
  have h1 : 1 < 2 * n := by omega
  have h2 : 2 < 2 * n := by omega
  have hk0 : 2 * k < 2 * n := by omega
  have hconst := C.phi_const hn hcard hangle hgen
  obtain ⟨hev, hod⟩ := C.len_parity hn hconst h0 h1
  obtain ⟨l0, hl0⟩ : ∃ r : ℝ, r = C.len ⟨0, h0⟩ := ⟨_, rfl⟩
  obtain ⟨l1, hl1⟩ : ∃ r : ℝ, r = C.len ⟨1, h1⟩ := ⟨_, rfl⟩
  have hl0p : 0 < l0 := by rw [hl0]; exact C.len_pos hn _
  have hl1p : 0 < l1 := by rw [hl1]; exact C.len_pos hn _
  obtain ⟨u₀, hu₀⟩ : ∃ z : ℂ, z = Complex.exp ((C.θ ⟨0, h0⟩ : ℂ) * Complex.I) :=
    ⟨_, rfl⟩
  have hedge : ∀ (m : ℕ) (hm : m < 2 * n) (hm1 : m + 1 < 2 * n),
      C.w ⟨m + 1, hm1⟩ - C.w ⟨m, hm⟩
        = (C.len ⟨m, hm⟩ : ℂ) * u₀ * zeta n ^ m := by
    intro m hm hm1
    have h := C.edge_eq hn h0 ⟨m, hm⟩
    rw [finRotate_val_of_lt ⟨m, hm⟩ (by exact hm1), ← hu₀] at h
    exact h
  have hD : ((l0 : ℂ) + (l1 : ℂ) * zeta n) ≠ 0 := by
    intro hz
    have him : ((l0 : ℂ) + (l1 : ℂ) * zeta n).im = l1 * Real.sin (π / n) := by
      rw [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, zeta_im,
        zero_add]
    rw [hz, Complex.zero_im] at him
    exact absurd him.symm (ne_of_gt (mul_pos hl1p hsin))
  -- the closing relation between `u₀`, the two lengths and the circumradius
  have hstar : u₀ * ((l0 : ℂ) + (l1 : ℂ) * zeta n) = Rc * (zeta n ^ 2 - 1) := by
    have ha := hedge 0 h0 h1
    have hb := hedge 1 h1 h2
    rw [← hl0, pow_zero, show (⟨0 + 1, h1⟩ : Fin (2 * n)) = ⟨1, h1⟩ from
      Fin.ext rfl] at ha
    rw [← hl1, pow_one] at hb
    have hv0 : C.w ⟨0, h0⟩ = O + Rc := by
      have h := hvert 0 (by omega)
      rw [show (⟨2 * 0, (by omega : 2 * 0 < 2 * n)⟩ : Fin (2 * n)) = ⟨0, h0⟩ from
        Fin.ext (by show 2 * 0 = 0; omega), pow_zero, mul_one] at h
      exact h
    have hv1 : C.w ⟨2, h2⟩ = O + Rc * zeta n ^ 2 := by
      have h := hvert 1 (by omega)
      rw [show (⟨2 * 1, (by omega : 2 * 1 < 2 * n)⟩ : Fin (2 * n)) = ⟨2, h2⟩ from
        Fin.ext (by show 2 * 1 = 2; omega), pow_one] at h
      exact h
    rw [hv0] at ha
    rw [hv1] at hb
    linear_combination -ha - hb
  -- the odd vertex in normalised coordinates
  have hpk : zeta n ^ (2 * k) = (zeta n ^ 2) ^ k := pow_mul (zeta n) 2 k
  have hnormB : (C.w ⟨2 * k + 1, hk1⟩ - O) / Rc
      = (zeta n ^ 2) ^ k * ((l0 : ℂ) * u₀ / Rc + 1) := by
    have hE0 := hedge (2 * k) hk0 hk1
    rw [hev k hk0, ← hl0, hpk] at hE0
    have hvk := hvert k hk0
    have hz : C.w ⟨2 * k + 1, hk1⟩ - O
        = (l0 : ℂ) * u₀ * (zeta n ^ 2) ^ k + Rc * (zeta n ^ 2) ^ k := by
      linear_combination hE0 + hvk
    rw [hz]
    field_simp
  have hfin : edgeFun n k ((C.w ⟨2 * k + 1, hk1⟩ - O) / Rc)
      = (((l1 : ℂ) + (l0 : ℂ) * zeta n) / ((l0 : ℂ) + (l1 : ℂ) * zeta n)).re := by
    rw [hnormB]
    unfold edgeFun
    congr 1
    have hcj : (starRingEnd ℂ) ((zeta n ^ 2) ^ k) * (zeta n ^ 2) ^ k = 1 := by
      rw [← pow_mul]; exact conj_zeta_pow_mul n (2 * k)
    rw [map_mul, show (starRingEnd ℂ) (zeta n) * (starRingEnd ℂ) ((zeta n ^ 2) ^ k)
        * ((zeta n ^ 2) ^ k * ((l0 : ℂ) * u₀ / Rc + 1))
        = ((starRingEnd ℂ) ((zeta n ^ 2) ^ k) * (zeta n ^ 2) ^ k)
          * ((starRingEnd ℂ) (zeta n) * ((l0 : ℂ) * u₀ / Rc + 1)) from by ring,
      hcj, one_mul, eq_div_iff hD]
    have h1' : ((l0 : ℂ) * u₀ / Rc + 1) * ((l0 : ℂ) + (l1 : ℂ) * zeta n)
        = ((l0 : ℂ) * (u₀ * ((l0 : ℂ) + (l1 : ℂ) * zeta n))
          + Rc * ((l0 : ℂ) + (l1 : ℂ) * zeta n)) / Rc := by
      field_simp
    have h2' : ((l0 : ℂ) * (Rc * (zeta n ^ 2 - 1))
        + Rc * ((l0 : ℂ) + (l1 : ℂ) * zeta n)) / Rc
        = (l0 : ℂ) * zeta n ^ 2 + (l1 : ℂ) * zeta n := by
      field_simp
      ring
    calc (starRingEnd ℂ) (zeta n) * ((l0 : ℂ) * u₀ / Rc + 1)
          * ((l0 : ℂ) + (l1 : ℂ) * zeta n)
        = (starRingEnd ℂ) (zeta n) * (((l0 : ℂ) * u₀ / Rc + 1)
          * ((l0 : ℂ) + (l1 : ℂ) * zeta n)) := by ring
      _ = (starRingEnd ℂ) (zeta n) * ((l0 : ℂ) * zeta n ^ 2 + (l1 : ℂ) * zeta n) := by
          rw [h1', hstar, h2']
      _ = (l1 : ℂ) + (l0 : ℂ) * zeta n := by
          linear_combination ((l0 : ℂ) * zeta n + (l1 : ℂ)) * conj_zeta_mul n
  rw [hfin]
  exact re_div_gt_cos hn hl0p hl1p

/-- **Q4.**  Every non-vertex point of `S` lies strictly inside the regular
`n`-gon formed by the even vertices. -/
theorem ngon_interior {n : ℕ} (hn : 3 ≤ n) {S : Finset ℂ}
    (hcard : S.card = 2 ^ n)
    (hangle : ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
      EuclideanGeometry.angle p q r ≤ (1 - 1 / (n : ℝ)) * π)
    (hgen : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set ℂ))
    (C : RigidConfig n S) {O Rc : ℂ} (hRc : Rc ≠ 0)
    (hvert : ∀ k : ℕ, ∀ hk : 2 * k < 2 * n,
      C.w ⟨2 * k, hk⟩ = O + Rc * (zeta n ^ 2) ^ k)
    {x : ℂ} (hxS : x ∈ S) (hxV : ∀ i, x ≠ C.w i) (k : ℕ) (hk : k < n) :
    edgeFun n k ((x - O) / Rc) < Real.cos (π / n) := by
  have h0 : 0 < 2 * n := by omega
  have hk0 : 2 * k < 2 * n := by omega
  have hk1 : 2 * k + 1 < 2 * n := by omega
  obtain ⟨p, q, hp, hq, hpq, hdec⟩ :=
    interior_beyond_chord hn hcard hangle hgen C hxS hxV ⟨2 * k + 1, hk1⟩
  have hA : C.w (finRotate (2 * n) ⟨2 * k + 1, hk1⟩)
      = O + Rc * (zeta n ^ 2) ^ (k + 1) := by
    rcases lt_or_ge (2 * k + 1 + 1) (2 * n) with hlt | hge
    · have hidx : finRotate (2 * n) ⟨2 * k + 1, hk1⟩
          = ⟨2 * (k + 1), by omega⟩ := by
        rw [finRotate_val_of_lt ⟨2 * k + 1, hk1⟩ (by exact hlt)]
        exact Fin.ext (by show 2 * k + 1 + 1 = 2 * (k + 1); omega)
      rw [hidx, hvert (k + 1) (by omega)]
    · have hkn : k + 1 = n := by omega
      have hidx : finRotate (2 * n) ⟨2 * k + 1, hk1⟩ = ⟨0, h0⟩ :=
        finRotate_val_of_last h0 ⟨2 * k + 1, hk1⟩
          (by show 2 * k + 1 + 1 = 2 * n; omega)
      have hv := hvert 0 (by omega)
      rw [show (⟨2 * 0, (by omega : 2 * 0 < 2 * n)⟩ : Fin (2 * n)) = ⟨0, h0⟩ from
        Fin.ext (by show 2 * 0 = 0; omega), pow_zero, mul_one] at hv
      rw [hidx, hv, hkn, zeta_pow_two_pow_n hn, mul_one]
  have hB : C.w ((finRotate (2 * n)).symm ⟨2 * k + 1, hk1⟩)
      = O + Rc * (zeta n ^ 2) ^ k := by
    have hidx : (finRotate (2 * n)).symm ⟨2 * k + 1, hk1⟩ = ⟨2 * k, hk0⟩ := by
      rw [finRotate_symm_of_pos ⟨2 * k + 1, hk1⟩ (by show 0 < 2 * k + 1; omega)]
      exact Fin.ext (by show 2 * k + 1 - 1 = 2 * k; omega)
    rw [hidx, hvert k hk0]
  obtain ⟨b, hb⟩ : ∃ z : ℂ, z = (C.w ⟨2 * k + 1, hk1⟩ - O) / Rc := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ z : ℂ, z = (x - O) / Rc := ⟨_, rfl⟩
  have e1 : x - C.w ⟨2 * k + 1, hk1⟩ = Rc * (u - b) := by
    rw [hu, hb]; field_simp; ring
  have e2 : O + Rc * (zeta n ^ 2) ^ (k + 1) - C.w ⟨2 * k + 1, hk1⟩
      = Rc * ((zeta n ^ 2) ^ (k + 1) - b) := by
    rw [hb]; field_simp; ring
  have e3 : O + Rc * (zeta n ^ 2) ^ k - C.w ⟨2 * k + 1, hk1⟩
      = Rc * ((zeta n ^ 2) ^ k - b) := by
    rw [hb]; field_simp; ring
  rw [hA, hB, Complex.real_smul, Complex.real_smul, e1, e2, e3] at hdec
  have hdec' : u - b = (p : ℂ) * ((zeta n ^ 2) ^ (k + 1) - b)
      + (q : ℂ) * ((zeta n ^ 2) ^ k - b) :=
    mul_left_cancel₀ hRc (by rw [hdec]; ring)
  have hEq : edgeFun n k u - edgeFun n k b
      = p * (edgeFun n k ((zeta n ^ 2) ^ (k + 1)) - edgeFun n k b)
        + q * (edgeFun n k ((zeta n ^ 2) ^ k) - edgeFun n k b) := by
    rw [← edgeFun_sub, hdec', edgeFun_add, edgeFun_smul, edgeFun_smul,
      edgeFun_sub, edgeFun_sub]
  rw [edgeFun_vertex_succ, edgeFun_vertex] at hEq
  have hBgt : Real.cos (π / n) < edgeFun n k b := by
    rw [hb]; exact odd_vertex_beyond hn hcard hangle hgen C hRc hvert k hk1
  rw [← hu]
  nlinarith [hEq, hBgt, hpq,
    mul_pos (show (0:ℝ) < p + q - 1 by linarith)
      (show (0:ℝ) < edgeFun n k b - Real.cos (π / n) by linarith)]


lemma omega_pow_mod {n : ℕ} (hn : 3 ≤ n) (k : ℕ) :
    (zeta n ^ 2) ^ (k % n) = (zeta n ^ 2) ^ k := by
  conv_rhs => rw [← Nat.mod_add_div k n]
  rw [pow_add, pow_mul, zeta_pow_two_pow_n hn, one_pow, mul_one]

lemma vertex_mem {n : ℕ} (hn : 3 ≤ n) {S : Finset ℂ} (C : RigidConfig n S)
    {O Rc : ℂ}
    (hvert : ∀ k : ℕ, ∀ hk : 2 * k < 2 * n,
      C.w ⟨2 * k, hk⟩ = O + Rc * (zeta n ^ 2) ^ k) (k : ℕ) :
    O + Rc * (zeta n ^ 2) ^ k ∈ S := by
  have hlt : k % n < n := Nat.mod_lt _ (by omega)
  have h := hvert (k % n) (by omega)
  rw [omega_pow_mod hn k] at h
  rw [← h]
  exact C.mem _

lemma vertex_eq_w {n : ℕ} (hn : 3 ≤ n) {S : Finset ℂ} (C : RigidConfig n S)
    {O Rc : ℂ}
    (hvert : ∀ k : ℕ, ∀ hk : 2 * k < 2 * n,
      C.w ⟨2 * k, hk⟩ = O + Rc * (zeta n ^ 2) ^ k) (k : ℕ) :
    O + Rc * (zeta n ^ 2) ^ k
      = C.w ⟨2 * (k % n), by have := Nat.mod_lt k (show 0 < n by omega); omega⟩ := by
  have h := hvert (k % n) (by have := Nat.mod_lt k (show 0 < n by omega); omega)
  rw [omega_pow_mod hn k] at h
  exact h.symm

lemma re_conj_zeta_pow_mul (n m : ℕ) (z : ℂ) :
    ((starRingEnd ℂ) (zeta n ^ m) * z).re
      = ‖z‖ * Real.cos (Complex.arg z - m * (π / n)) := by
  rw [zeta_pow, re_conj_exp_mul]

lemma not_collinear_of_im_ne_zero {a b c : ℂ}
    (h : ((starRingEnd ℂ) (b - a) * (c - a)).im ≠ 0) :
    ¬ Collinear ℝ ({a, b, c} : Set ℂ) := by
  intro hcol
  rw [collinear_iff_of_mem (show a ∈ ({a, b, c} : Set ℂ) by simp)] at hcol
  obtain ⟨v, hv⟩ := hcol
  obtain ⟨r1, h1⟩ := hv b (by simp)
  obtain ⟨r2, h2⟩ := hv c (by simp)
  apply h
  have e1 : b - a = (r1 : ℂ) * v := by
    rw [h1]; simp [Complex.real_smul]
  have e2 : c - a = (r2 : ℂ) * v := by
    rw [h2]; simp [Complex.real_smul]
  rw [e1, e2, map_mul, Complex.conj_ofReal,
    show (r1 : ℂ) * (starRingEnd ℂ) v * ((r2 : ℂ) * v)
      = ((r1 * r2 : ℝ) : ℂ) * ((starRingEnd ℂ) v * v) from by push_cast; ring,
    Complex.im_ofReal_mul, im_conj_self, mul_zero]

lemma cos_sub_sub_cos_add (A B : ℝ) :
    Real.cos (A - B) - Real.cos (A + B) = 2 * Real.sin A * Real.sin B := by
  rw [Real.cos_sub, Real.cos_add]; ring

/-- **Q3b (scalar).**  A sign change in the wedge indicator. -/
theorem exists_sign_change {n : ℕ} (hn : 3 ≤ n) {P : ℕ → ℝ}
    (h1 : 0 < P 1) (hlast : P (n - 1) < 0)
    (hne : ∀ j : ℕ, 1 ≤ j → j ≤ n - 1 → P j ≠ 0) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ n - 2 ∧ 0 < P j ∧ P (j + 1) < 0 := by
  classical
  have hex : ∃ i : ℕ, P (i + 1) < 0 :=
    ⟨n - 2, by rwa [show n - 2 + 1 = n - 1 from by omega]⟩
  obtain ⟨j, hjdef⟩ : ∃ j : ℕ, j = Nat.find hex := ⟨_, rfl⟩
  have hjspec : P (j + 1) < 0 := by rw [hjdef]; exact Nat.find_spec hex
  have hjle : j ≤ n - 2 := by
    rw [hjdef]
    exact Nat.find_le (by rwa [show n - 2 + 1 = n - 1 from by omega])
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · exfalso
      have hP1 : P 1 < 0 := by rw [show (1 : ℕ) = j + 1 from by omega]; exact hjspec
      linarith
    · exact h
  have hprev : ¬ P (j - 1 + 1) < 0 := by
    rw [hjdef]; exact Nat.find_min hex (by omega)
  rw [show j - 1 + 1 = j from by omega] at hprev
  exact ⟨j, hj1, hjle, lt_of_le_of_ne (not_lt.mp hprev)
    (Ne.symm (hne j hj1 (by omega))), hjspec⟩

lemma zeta_even_pow (n k : ℕ) : (zeta n ^ 2) ^ k = zeta n ^ (2 * k) :=
  (pow_mul (zeta n) 2 k).symm

lemma zeta_odd_pow (n k : ℕ) : zeta n * (zeta n ^ 2) ^ k = zeta n ^ (2 * k + 1) := by
  rw [zeta_even_pow, pow_add, pow_one]; ring

lemma zeta_pow_periodic {n : ℕ} (hn : 3 ≤ n) (t : ℕ) :
    zeta n ^ (2 * t) = zeta n ^ (2 * (t % n)) := by
  rw [← zeta_even_pow, ← zeta_even_pow, omega_pow_mod hn t]

lemma re_zeta_pow (n j : ℕ) : (zeta n ^ j).re = Real.cos (j * (π / n)) := by
  rw [zeta_pow, Complex.exp_ofReal_mul_I_re]

lemma zeta_pow_ne_zero (n j : ℕ) : zeta n ^ j ≠ 0 := pow_ne_zero _ (zeta_ne_zero n)

/-- The oriented area attached to a chord from the vertex `1`. -/
lemma im_conj_sub_one_mul (χ : ℝ) (w : ℂ) :
    ((starRingEnd ℂ) (Complex.exp (((2 * χ : ℝ) : ℂ) * Complex.I) - 1) * (w - 1)).im
      = 2 * Real.sin χ * (Real.cos χ
          - ((starRingEnd ℂ) (Complex.exp ((χ : ℂ) * Complex.I)) * w).re) := by
  simp only [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.sin_two_mul, Real.cos_two_mul']
  simp only [Complex.mul_im, Complex.mul_re, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.one_re, Complex.one_im]
  linear_combination w.im * (Real.sin_sq_add_cos_sq χ)

lemma zeta_two_pow_ne_one {n : ℕ} (hn : 3 ≤ n) {j : ℕ} (hj1 : 1 ≤ j)
    (hj2 : j ≤ n - 1) : (zeta n ^ 2) ^ j ≠ 1 := by
  intro hcon
  have hπ := Real.pi_pos
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
  have hjn : (j : ℝ) + 1 ≤ (n : ℝ) := by
    have h : j + 1 ≤ n := by omega
    exact_mod_cast h
  have hpn : (0 : ℝ) < π / n := div_pos hπ hnpos
  have hnn : (n : ℝ) * (π / n) = π := by field_simp
  have hpow : (zeta n ^ 2) ^ j
      = Complex.exp (((2 * (j : ℝ) * (π / n) : ℝ) : ℂ) * Complex.I) := by
    rw [zeta_even_pow, zeta_pow]
    congr 2
    push_cast
    ring
  rw [hpow] at hcon
  have hre : Real.cos (2 * (j : ℝ) * (π / n)) = 1 := by
    have h := congrArg Complex.re hcon
    rwa [Complex.exp_ofReal_mul_I_re, Complex.one_re] at h
  have hlo : (0 : ℝ) < 2 * (j : ℝ) * (π / n) := by
    have : (0:ℝ) < (j:ℝ) := by linarith
    positivity
  have hhi : 2 * (j : ℝ) * (π / n) < 2 * π := by
    nlinarith [mul_pos hpn (show (0:ℝ) < 1 by norm_num)]
  have := (Real.cos_eq_one_iff_of_lt_of_lt (by linarith) hhi).mp hre
  linarith

set_option maxHeartbeats 1000000 in
/-- **Q5 (Lemma 6).**  A non-central interior point of `S` sees some pair of
vertices of the regular `n`-gon under an angle exceeding `(1 - 1/n)·π`. -/
theorem regular_ngon_interior_sees_wide {n : ℕ} (hn : 3 ≤ n) {S : Finset ℂ}
    (hcard : S.card = 2 ^ n)
    (hangle : ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
      EuclideanGeometry.angle p q r ≤ (1 - 1 / (n : ℝ)) * π)
    (hgen : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set ℂ))
    (C : RigidConfig n S) {O Rc : ℂ} (hRc : Rc ≠ 0)
    (hvert : ∀ k : ℕ, ∀ hk : 2 * k < 2 * n,
      C.w ⟨2 * k, hk⟩ = O + Rc * (zeta n ^ 2) ^ k)
    {x : ℂ} (hxS : x ∈ S) (hxV : ∀ i, x ≠ C.w i) (hxO : x ≠ O) :
    ∃ k l : ℕ, (1 - 1 / (n : ℝ)) * π
      < EuclideanGeometry.angle (O + Rc * (zeta n ^ 2) ^ k) x
          (O + Rc * (zeta n ^ 2) ^ l) := by
  classical
  have hπ := Real.pi_pos
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  obtain ⟨s, hsdef⟩ : ∃ r : ℝ, r = π / n := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hsdef]; exact div_pos hπ hnpos
  have hns : (n : ℝ) * s = π := by rw [hsdef]; field_simp
  have hs3 : 3 * s ≤ π := by nlinarith
  have hsinS : 0 < Real.sin s := Real.sin_pos_of_pos_of_lt_pi hs0 (by linarith)
  have hcosS : 0 < Real.cos s :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hWeq : (1 - 1 / (n : ℝ)) * π = π - s := by
    rw [hsdef]; field_simp
  -- the normalised point
  obtain ⟨z, hz⟩ : ∃ w : ℂ, w = (x - O) / Rc := ⟨_, rfl⟩
  have hz0 : z ≠ 0 := by rw [hz]; exact div_ne_zero (sub_ne_zero.mpr hxO) hRc
  -- the edge conditions
  have hedgeZ : ∀ k : ℕ, ((starRingEnd ℂ) (zeta n ^ (2 * k + 1)) * z).re
      < Real.cos s := by
    intro k
    rw [← zeta_odd_pow]
    have h := ngon_interior hn hcard hangle hgen C hRc hvert hxS hxV (k % n)
      (Nat.mod_lt _ (by omega))
    unfold edgeFun at h
    rw [omega_pow_mod hn k] at h
    rw [hz, hsdef]
    exact h
  -- the Voronoi maximum
  obtain ⟨m, hmmem, hmmax⟩ := Finset.exists_max_image (Finset.range n)
    (fun k => ((starRingEnd ℂ) (zeta n ^ (2 * k)) * z).re)
    ⟨0, Finset.mem_range.mpr (by omega)⟩
  have hmax : ∀ t : ℕ, ((starRingEnd ℂ) (zeta n ^ (2 * t)) * z).re
      ≤ ((starRingEnd ℂ) (zeta n ^ (2 * m)) * z).re := by
    intro t
    rw [zeta_pow_periodic hn t]
    exact hmmax (t % n) (Finset.mem_range.mpr (Nat.mod_lt _ (by omega)))
  obtain ⟨z', hz'⟩ : ∃ w : ℂ, w = (starRingEnd ℂ) (zeta n ^ (2 * m)) * z :=
    ⟨_, rfl⟩
  have hconv : ∀ j : ℕ, (starRingEnd ℂ) (zeta n ^ j) * z'
      = (starRingEnd ℂ) (zeta n ^ (j + 2 * m)) * z := by
    intro j
    rw [hz', ← mul_assoc, ← map_mul, ← pow_add]
  have hz'0 : z' ≠ 0 := by
    intro h
    apply hz0
    have hb : zeta n ^ (2 * m) * z' = z := by
      rw [hz', ← mul_assoc, mul_comm (zeta n ^ (2 * m)), conj_zeta_pow_mul, one_mul]
    rw [← hb, h, mul_zero]
  obtain ⟨ρ, hρdef⟩ : ∃ r : ℝ, r = ‖z'‖ := ⟨_, rfl⟩
  obtain ⟨ψ, hψdef⟩ : ∃ r : ℝ, r = Complex.arg z' := ⟨_, rfl⟩
  have hρ : 0 < ρ := by rw [hρdef]; exact norm_pos_iff.mpr hz'0
  have hpolar : ∀ j : ℕ, ((starRingEnd ℂ) (zeta n ^ j) * z').re
      = ρ * Real.cos (ψ - j * s) := by
    intro j
    rw [re_conj_zeta_pow_mul, hρdef, hψdef, hsdef]
  -- the edge conditions in the rotated frame
  have hedgeP : ∀ k : ℕ, ρ * Real.cos (ψ - (2 * (k : ℝ) + 1) * s) < Real.cos s := by
    intro k
    have h : ((starRingEnd ℂ) (zeta n ^ (2 * k + 1)) * z').re < Real.cos s := by
      rw [hconv (2 * k + 1), show 2 * k + 1 + 2 * m = 2 * (k + m) + 1 from by ring]
      exact hedgeZ (k + m)
    rw [hpolar (2 * k + 1),
      show ((2 * k + 1 : ℕ) : ℝ) = 2 * (k : ℝ) + 1 from by push_cast; ring] at h
    exact h
  -- the Voronoi condition in the rotated frame
  have hz're : z'.re = ρ * Real.cos ψ := by
    have h := hpolar 0
    simpa using h
  have hvorP : ∀ t : ℕ, ρ * Real.cos (ψ - (2 * (t : ℝ)) * s) ≤ ρ * Real.cos ψ := by
    intro t
    have h : ((starRingEnd ℂ) (zeta n ^ (2 * t)) * z').re ≤ z'.re := by
      rw [hconv (2 * t), show 2 * t + 2 * m = 2 * (t + m) from by ring, hz']
      exact hmax (t + m)
    rw [hpolar (2 * t), hz're,
      show ((2 * t : ℕ) : ℝ) = 2 * (t : ℝ) from by push_cast; ring] at h
    exact h
  have hψπ : ψ ≤ π := by rw [hψdef]; exact Complex.arg_le_pi z'
  have hψπ' : -π < ψ := by rw [hψdef]; exact Complex.neg_pi_lt_arg z'
  have hV2 : ψ ≤ s := by
    by_contra hcon
    rw [not_le] at hcon
    have hsn : 0 < Real.sin (ψ - s) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have hid : Real.cos (ψ - 2 * s) - Real.cos ψ
        = 2 * Real.sin (ψ - s) * Real.sin s := by
      have h := cos_sub_sub_cos_add (ψ - s) s
      rw [show ψ - s - s = ψ - 2 * s from by ring,
        show ψ - s + s = ψ from by ring] at h
      linarith
    have h1 := hvorP 1
    rw [show (2 * ((1 : ℕ) : ℝ)) * s = 2 * s from by push_cast; ring] at h1
    nlinarith [mul_pos hsn hsinS]
  have hV1 : -s ≤ ψ := by
    by_contra hcon
    rw [not_le] at hcon
    have hsn : 0 < Real.sin (-(ψ + s)) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have hid : Real.cos (ψ + 2 * s) - Real.cos ψ
        = 2 * Real.sin (-(ψ + s)) * Real.sin s := by
      have h := cos_sub_sub_cos_add (ψ + s) s
      rw [show ψ + s - s = ψ from by ring,
        show ψ + s + s = ψ + 2 * s from by ring] at h
      rw [Real.sin_neg]
      linarith
    have h1 := hvorP (n - 1)
    rw [show (2 * (((n - 1 : ℕ)) : ℝ)) * s = 2 * π - 2 * s from by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]; push_cast; linear_combination 2 * hns,
      show ψ - (2 * π - 2 * s) = (ψ + 2 * s) - 2 * π from by ring,
      Real.cos_sub_two_pi] at h1
    nlinarith [mul_pos hsn hsinS]

  -- the point in the original frame
  have hxeq : x = O + Rc * zeta n ^ (2 * m) * z' := by
    have h1 : Rc * zeta n ^ (2 * m) * z' = x - O := by
      rw [hz', hz,
        show Rc * zeta n ^ (2 * m)
            * ((starRingEnd ℂ) (zeta n ^ (2 * m)) * ((x - O) / Rc))
          = ((starRingEnd ℂ) (zeta n ^ (2 * m)) * zeta n ^ (2 * m))
            * (Rc * ((x - O) / Rc)) from by ring, conj_zeta_pow_mul, one_mul]
      field_simp
    rw [h1]; ring
  -- the wedge indicator
  obtain ⟨P, hPdef⟩ : ∃ P : ℕ → ℝ,
      P = fun j : ℕ => Real.cos ((j : ℝ) * s)
        - ρ * Real.cos (ψ - (j : ℝ) * s) := ⟨_, rfl⟩
  have hP1 : 0 < P 1 := by
    have h := hedgeP 0
    rw [show (2 * ((0 : ℕ) : ℝ) + 1) * s = s from by push_cast; ring] at h
    simp only [hPdef, Nat.cast_one, one_mul]
    linarith
  have hlastEq : ((n - 1 : ℕ) : ℝ) * s = π - s := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]; push_cast; linear_combination hns
  have hPlast : P (n - 1) < 0 := by
    have h := hedgeP (n - 1)
    rw [show (2 * (((n - 1 : ℕ)) : ℝ) + 1) * s = 2 * π - s from by
        rw [Nat.cast_sub (by omega : 1 ≤ n)]; push_cast; linear_combination 2 * hns,
      show ψ - (2 * π - s) = (ψ + s) - 2 * π from by ring, Real.cos_sub_two_pi] at h
    simp only [hPdef]
    rw [hlastEq, Real.cos_pi_sub, show ψ - (π - s) = (ψ + s) - π from by ring,
      Real.cos_sub_pi]
    linarith
  -- the oriented area of the chord from the vertex `1`
  have hDj : ∀ j : ℕ, ((starRingEnd ℂ) ((zeta n ^ 2) ^ j - 1) * (z' - 1)).im
      = 2 * Real.sin ((j : ℝ) * s) * P j := by
    intro j
    have h1 : (zeta n ^ 2) ^ j
        = Complex.exp (((2 * ((j : ℝ) * s) : ℝ) : ℂ) * Complex.I) := by
      rw [zeta_even_pow, zeta_pow]; congr 2; push_cast [hsdef]; ring
    have h2 : zeta n ^ j = Complex.exp ((((j : ℝ) * s : ℝ) : ℂ) * Complex.I) := by
      rw [zeta_pow]; congr 2; push_cast [hsdef]; ring
    rw [h1, im_conj_sub_one_mul, ← h2, hpolar j]
    simp only [hPdef]
  have hPne : ∀ j : ℕ, 1 ≤ j → j ≤ n - 1 → P j ≠ 0 := by
    intro j hj1 hj2 hPj
    have hD0 : ((starRingEnd ℂ) ((zeta n ^ 2) ^ j - 1) * (z' - 1)).im = 0 := by
      rw [hDj j, hPj, mul_zero]
    have hne1 : (zeta n ^ 2) ^ j - 1 ≠ 0 :=
      sub_ne_zero.mpr (zeta_two_pow_ne_one hn hj1 hj2)
    obtain ⟨t, ht⟩ : ∃ t : ℝ, z' - 1 = t • ((zeta n ^ 2) ^ j - 1) :=
      ⟨_, eq_smul_of_im_conj_eq_zero hne1 hD0⟩
    have h3 : z' - 1 = (t : ℂ) * ((zeta n ^ 2) ^ j - 1) := by
      rw [ht, Complex.real_smul]
    obtain ⟨A, hA⟩ : ∃ w : ℂ, w = O + Rc * (zeta n ^ 2) ^ m := ⟨_, rfl⟩
    obtain ⟨B, hB⟩ : ∃ w : ℂ, w = O + Rc * (zeta n ^ 2) ^ (m + j) := ⟨_, rfl⟩
    have hAS : A ∈ S := by rw [hA]; exact vertex_mem hn C hvert m
    have hBS : B ∈ S := by rw [hB]; exact vertex_mem hn C hvert (m + j)
    have hxA : x ≠ A := by rw [hA, vertex_eq_w hn C hvert m]; exact hxV _
    have hxB : x ≠ B := by
      rw [hB, vertex_eq_w hn C hvert (m + j)]; exact hxV _
    have hAe : A = O + Rc * zeta n ^ (2 * m) := by rw [hA, zeta_even_pow]
    have hBA : B - A = Rc * zeta n ^ (2 * m) * ((zeta n ^ 2) ^ j - 1) := by
      rw [hA, hB, ← zeta_even_pow, pow_add]; ring
    have hAB : A ≠ B := by
      intro hAeq
      have hz2 : B - A = 0 := by rw [hAeq]; ring
      rw [hBA] at hz2
      rcases mul_eq_zero.mp hz2 with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · exact hRc h''
        · exact zeta_pow_ne_zero n (2 * m) h''
      · exact hne1 h'
    have hxAeq : x - A = (t : ℂ) * (B - A) := by
      rw [hBA]
      linear_combination hxeq - hAe + (Rc * zeta n ^ (2 * m)) * h3
    refine hgen x hxS A hAS B hBS hxA hAB hxB ?_
    rw [collinear_iff_of_mem (show A ∈ ({x, A, B} : Set ℂ) by simp)]
    refine ⟨B - A, fun w hw => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · refine ⟨t, ?_⟩
      simp only [Complex.real_smul, vadd_eq_add]
      linear_combination hxAeq
    · refine ⟨0, ?_⟩
      simp
    · refine ⟨1, ?_⟩
      simp only [Complex.real_smul, vadd_eq_add]
      push_cast
      ring
  obtain ⟨j, hj1, hj2, hPj, hPj1⟩ := exists_sign_change hn hP1 hPlast hPne
  have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
  have hjn2 : (j : ℝ) + 2 ≤ (n : ℝ) := by
    have h : j + 2 ≤ n := by omega
    exact_mod_cast h
  have hsj : 0 < Real.sin ((j : ℝ) * s) := by
    refine Real.sin_pos_of_pos_of_lt_pi (by nlinarith) ?_
    nlinarith
  have hsj1 : 0 < Real.sin (((j : ℝ) + 1) * s) := by
    refine Real.sin_pos_of_pos_of_lt_pi (by nlinarith) ?_
    nlinarith
  simp only [hPdef] at hPj hPj1
  rw [show (((j + 1 : ℕ)) : ℝ) = (j : ℝ) + 1 from by push_cast; ring] at hPj1
  -- Q1: outside the decision disk
  have hout : Real.cos (ψ - (2 * ((j : ℝ) * s) + s)) < ρ * Real.cos s := by
    refine outside_disk_core hs0 (by nlinarith) (by nlinarith) hρ hV1 hV2 ?_ ?_
    · rw [show (j : ℝ) * s + s = ((j : ℝ) + 1) * s from by ring]; linarith
    · linarith
  -- Q2: the central angle is small
  have hch : ρ * Real.cos (ψ - (2 * ((j : ℝ) * s) + s)) < Real.cos s := by
    have h := hedgeP j
    rw [show (2 * (j : ℝ) + 1) * s = 2 * ((j : ℝ) * s) + s from by ring] at h
    exact h
  have hQ2 := central_angle_lt_core hs0 (by linarith) hρ hch hout
  have hvj : Complex.exp (((2 * ((j : ℝ) * s) + s - s : ℝ) : ℂ) * Complex.I)
      = (zeta n ^ 2) ^ j := by
    rw [zeta_even_pow, zeta_pow]; congr 2; push_cast [hsdef]; ring
  have hvj1 : Complex.exp (((2 * ((j : ℝ) * s) + s + s : ℝ) : ℂ) * Complex.I)
      = (zeta n ^ 2) ^ (j + 1) := by
    rw [zeta_even_pow, zeta_pow]; congr 2; push_cast [hsdef]; ring
  have hz'polar : (ρ : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I) = z' := by
    rw [hρdef, hψdef]; exact Complex.norm_mul_exp_arg_mul_I z'
  rw [hvj, hvj1, hz'polar] at hQ2
  -- Q3c: the barycentric decomposition inside the triangle
  have hcm : (starRingEnd ℂ) (zeta n ^ j) * (zeta n ^ 2) ^ (j + 1)
      = zeta n ^ (j + 2) := by
    rw [zeta_even_pow, show 2 * (j + 1) = j + (j + 2) from by ring, pow_add,
      ← mul_assoc, conj_zeta_pow_mul, one_mul]
  have hXY : ((starRingEnd ℂ) ((zeta n ^ 2) ^ j - 1)
      * ((zeta n ^ 2) ^ (j + 1) - 1)).im
      = 2 * Real.sin ((j : ℝ) * s)
        * (2 * Real.sin (((j : ℝ) + 1) * s) * Real.sin s) := by
    have h1 : (zeta n ^ 2) ^ j
        = Complex.exp (((2 * ((j : ℝ) * s) : ℝ) : ℂ) * Complex.I) := by
      rw [zeta_even_pow, zeta_pow]; congr 2; push_cast [hsdef]; ring
    have h2 : zeta n ^ j = Complex.exp ((((j : ℝ) * s : ℝ) : ℂ) * Complex.I) := by
      rw [zeta_pow]; congr 2; push_cast [hsdef]; ring
    have h3 : Real.cos ((j : ℝ) * s) - Real.cos (((j : ℝ) + 2) * s)
        = 2 * Real.sin (((j : ℝ) + 1) * s) * Real.sin s := by
      have h := cos_sub_sub_cos_add (((j : ℝ) + 1) * s) s
      rw [show ((j : ℝ) + 1) * s - s = (j : ℝ) * s from by ring,
        show ((j : ℝ) + 1) * s + s = ((j : ℝ) + 2) * s from by ring] at h
      exact h
    conv_lhs => rw [h1]
    rw [im_conj_sub_one_mul, ← h2, hcm, re_zeta_pow,
      show (((j + 2 : ℕ)) : ℝ) * (π / n) = ((j : ℝ) + 2) * s from by
        rw [← hsdef]; push_cast; ring, h3]
  have hXYpos : 0 < ((starRingEnd ℂ) ((zeta n ^ 2) ^ j - 1)
      * ((zeta n ^ 2) ^ (j + 1) - 1)).im := by
    rw [hXY]
    have h1 : 0 < 2 * Real.sin (((j : ℝ) + 1) * s) * Real.sin s := by
      have h2 := mul_pos hsj1 hsinS
      linarith
    have h3 := mul_pos hsj h1
    linarith
  obtain ⟨p, q, hdec, hqid, hpid⟩ := exists_decomp_of_im_ne_zero
    (X := (zeta n ^ 2) ^ j - 1) (Y := (zeta n ^ 2) ^ (j + 1) - 1) (z := z' - 1)
    (ne_of_gt hXYpos)
  rw [hDj j] at hqid
  rw [hDj (j + 1),
    show (((j + 1 : ℕ)) : ℝ) = (j : ℝ) + 1 from by push_cast; ring] at hpid
  simp only [hPdef] at hqid hpid
  rw [show (((j + 1 : ℕ)) : ℝ) = (j : ℝ) + 1 from by push_cast; ring] at hpid
  have hq : 0 < q := by
    have hL : 0 < 2 * Real.sin ((j : ℝ) * s)
        * (Real.cos ((j : ℝ) * s) - ρ * Real.cos (ψ - (j : ℝ) * s)) := by
      have h := mul_pos hsj hPj; linarith
    rw [hqid] at hL
    nlinarith [hXYpos]
  have hp : 0 < p := by
    rw [im_conj_mul_swap] at hpid
    have hL : 2 * Real.sin (((j : ℝ) + 1) * s)
        * (Real.cos (((j : ℝ) + 1) * s)
          - ρ * Real.cos (ψ - ((j : ℝ) + 1) * s)) < 0 := by
      nlinarith [mul_pos hsj1 (neg_pos.mpr hPj1)]
    rw [hpid] at hL
    nlinarith [hXYpos]
  -- the total weight is less than one
  have hdecC : z' - 1 = (p : ℂ) * ((zeta n ^ 2) ^ j - 1)
      + (q : ℂ) * ((zeta n ^ 2) ^ (j + 1) - 1) := by
    rw [hdec, Complex.real_smul, Complex.real_smul]
  have hE1 : edgeFun n j 1 = Real.cos ((2 * (j : ℝ) + 1) * s) := by
    unfold edgeFun
    rw [zeta_odd_pow, mul_one, Complex.conj_re, re_zeta_pow,
      show (((2 * j + 1 : ℕ)) : ℝ) * (π / n) = (2 * (j : ℝ) + 1) * s from by
        rw [← hsdef]; push_cast; ring]
  have hEz' : edgeFun n j z' = ρ * Real.cos (ψ - (2 * (j : ℝ) + 1) * s) := by
    unfold edgeFun
    rw [zeta_odd_pow, hpolar (2 * j + 1),
      show (((2 * j + 1 : ℕ)) : ℝ) * s = (2 * (j : ℝ) + 1) * s from by
        push_cast; ring]
  have hlin : edgeFun n j z' - edgeFun n j 1
      = p * (edgeFun n j ((zeta n ^ 2) ^ j) - edgeFun n j 1)
        + q * (edgeFun n j ((zeta n ^ 2) ^ (j + 1)) - edgeFun n j 1) := by
    rw [← edgeFun_sub, hdecC, edgeFun_add, edgeFun_smul, edgeFun_smul,
      edgeFun_sub, edgeFun_sub]
  rw [edgeFun_vertex, edgeFun_vertex_succ, hE1, hEz', ← hsdef] at hlin
  have hcos1 : Real.cos ((2 * (j : ℝ) + 1) * s) < Real.cos s := by
    rcases le_or_gt ((2 * (j : ℝ) + 1) * s) π with hle | hgt
    · exact Real.cos_lt_cos_of_nonneg_of_le_pi hs0.le hle (by nlinarith)
    · rw [← Real.cos_two_pi_sub ((2 * (j : ℝ) + 1) * s)]
      exact Real.cos_lt_cos_of_nonneg_of_le_pi hs0.le (by linarith) (by nlinarith)
  have hpq1 : p + q < 1 := by
    have hlt : ρ * Real.cos (ψ - (2 * (j : ℝ) + 1) * s) < Real.cos s := by
      have h := hedgeP j
      exact h
    nlinarith [hlin, hcos1, hlt]
  -- the full turn at the interior point
  have hnc : ¬ Collinear ℝ
      ({(1 : ℂ), (zeta n ^ 2) ^ j, (zeta n ^ 2) ^ (j + 1)} : Set ℂ) := by
    refine not_collinear_of_im_ne_zero ?_
    exact ne_of_gt hXYpos
  have hxeq2 : z' = (1 - p - q) • (1 : ℂ) + p • ((zeta n ^ 2) ^ j)
      + q • ((zeta n ^ 2) ^ (j + 1)) := by
    simp only [Complex.real_smul]
    push_cast
    linear_combination hdecC
  have hsum := angle_sum_eq_two_pi_of_interior (a := (1 : ℂ))
    (b := (zeta n ^ 2) ^ j) (c := (zeta n ^ 2) ^ (j + 1)) (x := z')
    (α := 1 - p - q) (β := p) (γ := q)
    (by linarith) hp hq (by ring) hxeq2 hnc
  -- transfer back to the original frame
  have hRcm : Rc * zeta n ^ (2 * m) ≠ 0 :=
    mul_ne_zero hRc (zeta_pow_ne_zero n (2 * m))
  have htrans : ∀ w₁ w₂ : ℂ,
      EuclideanGeometry.angle (O + Rc * zeta n ^ (2 * m) * w₁) x
          (O + Rc * zeta n ^ (2 * m) * w₂)
        = EuclideanGeometry.angle w₁ z' w₂ := by
    intro w₁ w₂
    conv_lhs => rw [hxeq]
    rw [show O + Rc * zeta n ^ (2 * m) * w₁
        = Rc * zeta n ^ (2 * m) * w₁ + O from by ring,
      show O + Rc * zeta n ^ (2 * m) * z'
        = Rc * zeta n ^ (2 * m) * z' + O from by ring,
      show O + Rc * zeta n ^ (2 * m) * w₂
        = Rc * zeta n ^ (2 * m) * w₂ + O from by ring,
      euclidean_angle_add_const, euclidean_angle_const_mul hRcm]
  have hv0 : O + Rc * (zeta n ^ 2) ^ m = O + Rc * zeta n ^ (2 * m) * 1 := by
    rw [zeta_even_pow]; ring
  have hvA : O + Rc * (zeta n ^ 2) ^ (m + j)
      = O + Rc * zeta n ^ (2 * m) * ((zeta n ^ 2) ^ j) := by
    rw [← zeta_even_pow, pow_add]; ring
  have hvB : O + Rc * (zeta n ^ 2) ^ (m + j + 1)
      = O + Rc * zeta n ^ (2 * m) * ((zeta n ^ 2) ^ (j + 1)) := by
    rw [← zeta_even_pow, show m + j + 1 = m + (j + 1) from by omega, pow_add]
    ring
  rcases le_or_gt (EuclideanGeometry.angle (1 : ℂ) z' ((zeta n ^ 2) ^ j))
    (π - s) with hc1 | hc1
  · refine ⟨m + j + 1, m, ?_⟩
    rw [hWeq, hvB, hv0, htrans]
    have hc2 : EuclideanGeometry.angle ((zeta n ^ 2) ^ j) z'
        ((zeta n ^ 2) ^ (j + 1)) < 2 * s := hQ2
    linarith [hsum]
  · refine ⟨m, m + j, ?_⟩
    rw [hWeq, hv0, hvA, htrans]
    exact hc1


/-- **Q6 (general position).**  A maximal-angle bound forces general position. -/
lemma hgen_of_hangle {n : ℕ} (hn : 3 ≤ n) {S : Finset ℂ}
    (hangle : ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
      EuclideanGeometry.angle p q r ≤ (1 - 1 / (n : ℝ)) * π) :
    ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set ℂ) := by
  intro a ha b hb c hc hab hbc hac hcol
  have hπ := Real.pi_pos
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hW : (1 - 1 / (n : ℝ)) * π < π := by
    have h1 : 0 < 1 / (n : ℝ) := by positivity
    nlinarith
  rcases exists_angle_eq_pi_of_collinear hab hbc hac hcol with h | h | h
  · have hle := hangle a ha b hb c hc hab (Ne.symm hbc)
    rw [h] at hle; linarith
  · have hle := hangle b hb a ha c hc (Ne.symm hab) (Ne.symm hac)
    rw [h] at hle; linarith
  · have hle := hangle a ha c hc b hb hac hbc
    rw [h] at hle; linarith

/-- **Erdős–Szekeres (1960).**  Among `2ⁿ` points of the plane some three
determine an angle exceeding `(1 - 1/n)·π`. -/
theorem erdos_szekeres_1960 {n : ℕ} (hn : 3 ≤ n) (S : Finset ℂ)
    (hcard : S.card = 2 ^ n) :
    ∃ p ∈ S, ∃ q ∈ S, ∃ r ∈ S, p ≠ q ∧ r ≠ q ∧
      (1 - 1 / (n : ℝ)) * π < EuclideanGeometry.angle p q r := by
  by_contra hcon
  have hangle : ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
      EuclideanGeometry.angle p q r ≤ (1 - 1 / (n : ℝ)) * π := by
    intro p hp q hq r hr hpq hrq
    by_contra h
    rw [not_le] at h
    exact hcon ⟨p, hp, q, hq, r, hr, hpq, hrq, h⟩
  have hgen := hgen_of_hangle hn hangle
  obtain ⟨C⟩ := exists_rigidConfig hn hcard hangle
  obtain ⟨O, Rc, hRc, hvert⟩ := regular_ngon hn hcard hangle hgen C
  obtain ⟨q₁, hq₁, q₂, hq₂, hne, hV₁, hV₂⟩ := exists_two_interior hn hcard C
  obtain ⟨x, hxS, hxV, hxO⟩ : ∃ x : ℂ, x ∈ S ∧ (∀ i, x ≠ C.w i) ∧ x ≠ O := by
    rcases eq_or_ne q₁ O with h | h
    · exact ⟨q₂, hq₂, hV₂, by rw [← h]; exact Ne.symm hne⟩
    · exact ⟨q₁, hq₁, hV₁, h⟩
  obtain ⟨k, l, hkl⟩ := regular_ngon_interior_sees_wide hn hcard hangle hgen C
    hRc hvert hxS hxV hxO
  have hAS : O + Rc * (zeta n ^ 2) ^ k ∈ S := vertex_mem hn C hvert k
  have hBS : O + Rc * (zeta n ^ 2) ^ l ∈ S := vertex_mem hn C hvert l
  have hxA : O + Rc * (zeta n ^ 2) ^ k ≠ x := by
    rw [vertex_eq_w hn C hvert k]; exact Ne.symm (hxV _)
  have hxB : O + Rc * (zeta n ^ 2) ^ l ≠ x := by
    rw [vertex_eq_w hn C hvert l]; exact Ne.symm (hxV _)
  exact absurd (hangle _ hAS x hxS _ hBS hxA hxB) (not_le.mpr hkl)

end Erdos504
