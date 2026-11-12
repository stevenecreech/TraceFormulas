import TraceFormulas.Geometry.Iwasawa
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.LinearAlgebra.BilinearForm.Basic

/-!
# Invariant tangent geometry on the upper half-plane

The derivative is the genuine complex derivative of the fractional action.
Real bilinear forms describe tangent inner products without assuming conformality.
Area density covariance is treated separately from measure invariance; the
change-of-variables and Riemannian volume bridges remain to be formalized.
-/
noncomputable section
open UpperHalfPlane
namespace TraceFormulas.Hyperbolic

/-- Complex scalar multiplying tangent vectors under the Möbius action. -/
def mobiusDerivative (g : RealGroup) (z : ℍ) : ℂ := 1 / factor g z ^ 2

theorem hasDerivAt_fractional_action (g : RealGroup) (z : ℍ) :
    HasDerivAt (fun w : ℂ => ((g 0 0 : ℂ) * w + g 0 1) / factor g w)
      (mobiusDerivative g z) (z : ℂ) := by
  have hnum : HasDerivAt (fun w : ℂ => (g 0 0 : ℂ) * w + g 0 1) (g 0 0 : ℂ) (z : ℂ) := by
    simpa only [mul_one] using
      HasDerivAt.add_const (g 0 1 : ℂ) ((hasDerivAt_id (z : ℂ)).const_mul (g 0 0 : ℂ))
  have hden : HasDerivAt (fun w : ℂ => factor g w) (g 1 0 : ℂ) (z : ℂ) := by
    simpa only [mul_one, factor] using
      HasDerivAt.add_const (g 1 1 : ℂ) ((hasDerivAt_id (z : ℂ)).const_mul (g 1 0 : ℂ))
  have h := hnum.div hden (factor_ne_zero g z)
  have hdet : (g 0 0 : ℂ) * (g 1 1 : ℂ) - (g 0 1 : ℂ) * (g 1 0 : ℂ) = 1 := by
    exact_mod_cast (show g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 by
      simpa only [Matrix.det_fin_two] using g.property)
  have hcancel : (g 0 0 : ℂ) * factor g z -
      ((g 0 0 : ℂ) * z + g 0 1) * (g 1 0 : ℂ) = 1 := by
    calc
      _ = (g 0 0 : ℂ) * (g 1 1 : ℂ) - (g 0 1 : ℂ) * (g 1 0 : ℂ) := by
        simp only [factor]; ring
      _ = 1 := hdet
  simpa only [mul_one, hcancel, mobiusDerivative] using h

/-- Squared tangent length; complex normSq is the ordinary Euclidean squared norm. -/
def tangentEnergy (z : ℍ) (v : ℂ) : ℝ := Complex.normSq v / z.im ^ 2

/-- The density relative to Lebesgue area, not a new definition of a measure. -/
def areaDensity (z : ℍ) : ℝ := 1 / z.im ^ 2

theorem tangentEnergy_positive (z : ℍ) (v : ℂ) (hv : v ≠ 0) :
    0 < tangentEnergy z v :=
  div_pos (Complex.normSq_pos.mpr hv) (sq_pos_of_pos z.im_pos)

theorem tangentEnergy_at_I (v : ℂ) :
    tangentEnergy UpperHalfPlane.I v = Complex.normSq v := by
  simp [tangentEnergy]

theorem derivative_normSq (g : RealGroup) (z : ℍ) :
    Complex.normSq (mobiusDerivative g z) = 1 / Complex.normSq (factor g z) ^ 2 := by
  simp [mobiusDerivative, map_pow, Complex.normSq_div]

theorem tangentEnergy_invariant (g : RealGroup) (z : ℍ) (v : ℂ) :
    tangentEnergy (g • z) (mobiusDerivative g z * v) = tangentEnergy z v := by
  have hn := (Complex.normSq_pos.mpr (factor_ne_zero g z)).ne'
  rw [tangentEnergy, Complex.normSq_mul, derivative_normSq, action_im, tangentEnergy]
  field_simp

theorem areaDensity_covariant (g : RealGroup) (z : ℍ) :
    areaDensity (g • z) * Complex.normSq (mobiusDerivative g z) = areaDensity z := by
  have hn := (Complex.normSq_pos.mpr (factor_ne_zero g z)).ne'
  rw [areaDensity, action_im, derivative_normSq, areaDensity]
  field_simp
  ring

theorem sectionMatrix_derivative (z : ℍ) :
    mobiusDerivative (sectionMatrix z) UpperHalfPlane.I = (z.im : ℂ) := by
  simp [mobiusDerivative, factor, sectionMatrix, translation, dilation,
    Matrix.mul_apply, Fin.sum_univ_two, ← inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt z.im_pos.le]

/-- The pointwise density law forces the density up to its value at i.
No smoothness is required for this algebraic implication. -/
theorem density_unique (ρ : ℍ → ℝ)
    (hρ : ∀ (g : RealGroup) (z : ℍ),
      ρ (g • z) * Complex.normSq (mobiusDerivative g z) = ρ z) (z : ℍ) :
    ρ z = ρ UpperHalfPlane.I / z.im ^ 2 := by
  have h := hρ (sectionMatrix z) UpperHalfPlane.I
  rw [sectionMatrix_smul_I, sectionMatrix_derivative, Complex.normSq_ofReal] at h
  apply (eq_div_iff (pow_ne_zero 2 z.im_pos.ne')).mpr
  simpa only [pow_two] using h

/-- Quarter-turn invariance forces a symmetric real bilinear form to be scalar Euclidean. -/
theorem bilinear_rotation_unique (B : LinearMap.BilinForm ℝ ℂ)
    (hsym : ∀ v w, B v w = B w v)
    (hrot : ∀ v w, B (Complex.I * v) (Complex.I * w) = B v w) (v w : ℂ) :
    B v w = B 1 1 * (v * star w).re := by
  have hdiag : B Complex.I Complex.I = B 1 1 := by simpa using hrot 1 1
  have hcross : B 1 Complex.I = 0 := by
    have h := hrot 1 Complex.I
    simp only [mul_one, Complex.I_mul_I, LinearMap.BilinForm.neg_right] at h
    rw [hsym Complex.I 1] at h
    linarith
  have hcross' : B Complex.I 1 = 0 := by rw [hsym, hcross]
  have decomp (u : ℂ) : u = u.re • (1 : ℂ) + u.im • Complex.I := by
    apply Complex.ext <;> simp
  calc
    B v w = B (v.re • (1 : ℂ) + v.im • Complex.I)
        (w.re • (1 : ℂ) + w.im • Complex.I) := by rw [← decomp, ← decomp]
    _ = B 1 1 * (v * star w).re := by
      simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
        LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
        hdiag, hcross, hcross', mul_zero, add_zero, zero_add,
        Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
      ring

/-- A genuine stabilizer matrix induces a quarter-turn on tangent vectors. -/
theorem quarter_rotation_derivative :
    mobiusDerivative (rotation (Real.pi / 4)) UpperHalfPlane.I = Complex.I := by
  unfold mobiusDerivative
  apply (div_eq_iff (pow_ne_zero 2 (factor_ne_zero _ _))).mpr
  apply Complex.ext <;>
    simp [factor, rotation, UpperHalfPlane.coe_I, Real.cos_pi_div_four,
      Real.sin_pi_div_four, pow_two, Complex.mul_re, Complex.mul_im]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

/-- Invariance of a real bilinear tensor under the actual fractional derivative. -/
def IsInvariantBilinearField (B : ℍ → LinearMap.BilinForm ℝ ℂ) : Prop :=
  ∀ (g : RealGroup) (z : ℍ) (v w : ℂ),
    B (g • z) (mobiusDerivative g z * v) (mobiusDerivative g z * w) = B z v w

/-- Symmetry and invariance force the coefficient formula without a conformality assumption.
Smoothness is unnecessary for this uniqueness direction. -/
theorem invariantBilinearField_unique (B : ℍ → LinearMap.BilinForm ℝ ℂ)
    (hsym : ∀ z v w, B z v w = B z w v) (hinv : IsInvariantBilinearField B)
    (z : ℍ) (v w : ℂ) :
    B z v w = (B UpperHalfPlane.I 1 1 / z.im ^ 2) * (v * star w).re := by
  have hrot : ∀ v w, B UpperHalfPlane.I (Complex.I * v) (Complex.I * w) =
      B UpperHalfPlane.I v w := by
    intro v w
    have h := hinv (rotation (Real.pi / 4)) UpperHalfPlane.I v w
    rw [rotation_fixes_I, quarter_rotation_derivative] at h
    exact h
  have h := hinv (sectionMatrix z) UpperHalfPlane.I v w
  rw [sectionMatrix_smul_I, sectionMatrix_derivative, ← Complex.real_smul,
    ← Complex.real_smul, LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.smul_right] at h
  rw [bilinear_rotation_unique _ (hsym UpperHalfPlane.I) hrot] at h
  calc
    B z v w = (B UpperHalfPlane.I 1 1 * (v * star w).re) / z.im ^ 2 := by
      apply (eq_div_iff (pow_ne_zero 2 z.im_pos.ne')).mpr
      nlinarith [h]
    _ = _ := by ring

/-- The normalized tangent inner product as an actual real bilinear form. -/
def tangentForm (z : ℍ) : LinearMap.BilinForm ℝ ℂ where
  toFun v :=
    { toFun := fun w => (v.re * w.re + v.im * w.im) / z.im ^ 2
      map_add' := by intro w u; simp only [Complex.add_re, Complex.add_im]; ring
      map_smul' := by intro a w; simp only [Complex.smul_re, Complex.smul_im, smul_eq_mul, RingHom.id_apply]; ring }
  map_add' := by
    intro v w
    ext u
    change ((v + w).re * u.re + (v + w).im * u.im) / z.im ^ 2 = _
    simp only [Complex.add_re, Complex.add_im]
    change ((v.re + w.re) * u.re + (v.im + w.im) * u.im) / z.im ^ 2 =
      (v.re * u.re + v.im * u.im) / z.im ^ 2 + (w.re * u.re + w.im * u.im) / z.im ^ 2
    ring
  map_smul' := by
    intro a v
    ext w
    change ((a • v).re * w.re + (a • v).im * w.im) / z.im ^ 2 =
      a * ((v.re * w.re + v.im * w.im) / z.im ^ 2)
    simp only [Complex.smul_re, Complex.smul_im, smul_eq_mul]
    ring

theorem tangentForm_apply (z : ℍ) (v w : ℂ) :
    tangentForm z v w = (v * star w).re / z.im ^ 2 := by
  simp [tangentForm, Complex.mul_re, Complex.star_def]

theorem tangentForm_symmetric (z : ℍ) (v w : ℂ) :
    tangentForm z v w = tangentForm z w v := by
  change (v.re * w.re + v.im * w.im) / z.im ^ 2 =
    (w.re * v.re + w.im * v.im) / z.im ^ 2
  ring

theorem tangentForm_self (z : ℍ) (v : ℂ) : tangentForm z v v = tangentEnergy z v := by
  simp [tangentForm, tangentEnergy, Complex.normSq_apply]

theorem tangentForm_positive (z : ℍ) (v : ℂ) (hv : v ≠ 0) :
    0 < tangentForm z v v := by
  rw [tangentForm_self]
  exact tangentEnergy_positive z v hv

theorem real_pairing_complex_scale (a v w : ℂ) :
    (a * v * star (a * w)).re = Complex.normSq a * (v * star w).re := by
  simp only [Complex.star_def, map_mul, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  ring

theorem tangentForm_invariant : IsInvariantBilinearField tangentForm := by
  intro g z v w
  have hn := (Complex.normSq_pos.mpr (factor_ne_zero g z)).ne'
  rw [tangentForm_apply, real_pairing_complex_scale, derivative_normSq, action_im,
    tangentForm_apply]
  field_simp

/-- The same cancellation in unsquared tangent lengths (Euclidean modulus is ‖v‖). -/
theorem tangent_norm_invariant (g : RealGroup) (z : ℍ) (v : ℂ) :
    ‖mobiusDerivative g z * v‖ / (g • z).im = ‖v‖ / z.im := by
  have he := tangentEnergy_invariant g z v
  simp only [tangentEnergy, Complex.normSq_eq_norm_sq, ← div_pow] at he
  exact (sq_eq_sq₀ (div_nonneg (norm_nonneg _) (g • z).im_pos.le)
    (div_nonneg (norm_nonneg _) z.im_pos.le)).mp he

/-- The gradient of a real linear differential in the fixed complex coordinates. -/
def gradientFromDifferential (z : ℍ) (ell : ℂ →ₗ[ℝ] ℝ) : ℂ :=
  z.im ^ 2 • ((ell 1 : ℂ) + (ell Complex.I : ℂ) * Complex.I)

theorem gradientFromDifferential_duality (z : ℍ) (ell : ℂ →ₗ[ℝ] ℝ) (v : ℂ) :
    tangentForm z (gradientFromDifferential z ell) v = ell v := by
  have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
    apply Complex.ext <;> simp
  have hel : ell v = v.re * ell 1 + v.im * ell Complex.I := by
    conv_lhs => rw [hv]
    simp only [map_add, map_smul, smul_eq_mul]
  rw [hel]
  change (((gradientFromDifferential z ell).re * v.re +
    (gradientFromDifferential z ell).im * v.im) / z.im ^ 2) = _
  simp only [gradientFromDifferential, Complex.smul_re, Complex.smul_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero,
    mul_one, sub_zero, zero_mul, zero_add, add_zero, smul_eq_mul]
  field_simp
  ring

/-- Temporary two-point quantity J in the geodesic proof, before the later u-normalization. -/
def distanceRatio (z w : ℍ) : ℝ := Complex.normSq ((z : ℂ) - w) / (z.im * w.im)

theorem distanceRatio_invariant (g : RealGroup) (z w : ℍ) :
    distanceRatio (g • z) (g • w) = distanceRatio z w := by
  have hz := (Complex.normSq_pos.mpr (factor_ne_zero g z)).ne'
  have hw := (Complex.normSq_pos.mpr (factor_ne_zero g w)).ne'
  simp only [distanceRatio, action_difference, Complex.normSq_div,
    Complex.normSq_mul, action_im]
  field_simp

end TraceFormulas.Hyperbolic
