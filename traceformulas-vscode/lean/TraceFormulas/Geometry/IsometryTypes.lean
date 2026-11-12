import TraceFormulas.Geometry.DiskGeometry

/-!
# Algebraic ingredients for the three types of real Möbius transformations

The discriminant uses the actual matrix trace. Fixed-point statements concern
Mathlib's genuine upper-half-plane action. Normal-form displacement calculations
use the previously defined point-pair invariant; they are not definitions of
translation length. Boundary fixed-point classification, full conjugacy normal
forms, and infima of hyperbolic distances remain separate obligations.
-/
noncomputable section
open UpperHalfPlane
namespace TraceFormulas.Hyperbolic

/-- The characteristic-polynomial discriminant of a real determinant-one matrix. -/
def typeDiscriminant (g : RealGroup) : ℝ :=
  (Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℝ)) ^ 2 - 4

theorem typeDiscriminant_entries (g : RealGroup) :
    typeDiscriminant g = (g 0 0 + g 1 1) ^ 2 - 4 := by
  simp [typeDiscriminant, Matrix.trace_fin_two]

theorem typeDiscriminant_neg (g : RealGroup) :
    typeDiscriminant (-g) = typeDiscriminant g := by
  simp [typeDiscriminant]

theorem typeDiscriminant_quadratic (g : RealGroup) :
    typeDiscriminant g = (g 1 1 - g 0 0) ^ 2 + 4 * g 0 1 * g 1 0 := by
  have hd : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.property
  rw [typeDiscriminant_entries]
  nlinarith

/-- Clearing the nonzero denominator gives exactly the manuscript's quadratic. -/
theorem fixes_iff_quadratic (g : RealGroup) (z : ℍ) :
    g • z = z ↔ (g 1 0 : ℂ) * (z : ℂ)^2 +
      ((g 1 1 : ℂ) - g 0 0) * z - g 0 1 = 0 := by
  rw [← UpperHalfPlane.ext_iff', action_formula,
    div_eq_iff (factor_ne_zero g z)]
  simp only [factor]
  constructor <;> intro h <;> linear_combination -h

/-- An interior fixed point determines the discriminant through its height. -/
theorem fixedPoint_discriminant (g : RealGroup) (z : ℍ) (h : g • z = z) :
    typeDiscriminant g = -4 * (g 1 0 * z.im) ^ 2 := by
  have heq := (fixes_iff_quadratic g z).mp h
  have hr := congrArg Complex.re heq
  have hi := congrArg Complex.im heq
  simp [Complex.mul_re, Complex.mul_im, pow_two] at hr hi
  have him : 2 * g 1 0 * z.re + (g 1 1 - g 0 0) = 0 := by
    have hy := z.im_pos
    nlinarith
  rw [typeDiscriminant_quadratic]
  linear_combination -4 * (g 1 0) * hr +
    (g 1 1 - g 0 0 + 2 * g 1 0 * z.re) * him

/-- The elliptic normal-form proof after its fixed point has been supplied. -/
theorem conjugate_fixedPoint_rotation (g : RealGroup) (p : ℍ) (hp : g • p = p) :
    ∃ θ : ℝ, (sectionMatrix p)⁻¹ * g * sectionMatrix p = rotation θ := by
  apply (fixes_I_iff_rotation _).mp
  rw [mul_smul, mul_smul, sectionMatrix_smul_I, hp]
  calc
    _ = (sectionMatrix p)⁻¹ • (sectionMatrix p • I) :=
      congrArg (fun q : ℍ => (sectionMatrix p)⁻¹ • q) (sectionMatrix_smul_I p).symm
    _ = I := inv_smul_smul _ _

theorem translation_fixed_iff (t : ℝ) (z : ℍ) :
    translation t • z = z ↔ t = 0 := by
  rw [← UpperHalfPlane.ext_iff', translation_action]
  constructor
  · intro h
    have hr := congrArg Complex.re h
    simpa using hr
  · intro h
    simp [h]

theorem dilation_fixed_iff (y : ℝ) (hy : 0 < y) (z : ℍ) :
    dilation y hy • z = z ↔ y = 1 := by
  rw [← UpperHalfPlane.ext_iff', dilation_action]
  constructor
  · intro h
    have hi := congrArg Complex.im h
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, coe_im] at hi
    nlinarith [z.im_pos]
  · intro h
    simp [h]

theorem translation_pointPair (t : ℝ) (z : ℍ) :
    pointPair z (translation t • z) = t ^ 2 / (4 * z.im ^ 2) := by
  have him : (translation t • z).im = z.im := by
    change Complex.im ((translation t • z : ℍ) : ℂ) = _
    rw [translation_action]
    simp
  simp only [pointPair, translation_action, him]
  simp [Complex.normSq_apply, pow_two]
  ring

theorem dilation_pointPair (y : ℝ) (hy : 0 < y) (z : ℍ) :
    pointPair z (dilation y hy • z) =
      (y - 1) ^ 2 / (4 * y) * (1 + z.re ^ 2 / z.im ^ 2) := by
  have him : (dilation y hy • z).im = y * z.im := by
    change Complex.im ((dilation y hy • z : ℍ) : ℂ) = _
    rw [dilation_action]
    simp
  have hz := ne_of_gt z.im_pos
  have hn := ne_of_gt hy
  simp only [pointPair, dilation_action, him]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, zero_add, add_zero, sub_zero, coe_re, coe_im]
  field_simp
  ring

theorem dilation_pointPair_lower (y : ℝ) (hy : 0 < y) (z : ℍ) :
    (y - 1) ^ 2 / (4 * y) ≤ pointPair z (dilation y hy • z) := by
  rw [dilation_pointPair]
  have hc : 0 ≤ (y - 1) ^ 2 / (4 * y) := by positivity
  have hz : 0 ≤ z.re ^ 2 / z.im ^ 2 := by positivity
  nlinarith [mul_nonneg hc hz]

/-- The minimal point-pair displacement occurs exactly on the imaginary axis. -/
theorem dilation_pointPair_min_iff (y : ℝ) (hy : 0 < y) (hne : y ≠ 1) (z : ℍ) :
    pointPair z (dilation y hy • z) = (y - 1) ^ 2 / (4 * y) ↔ z.re = 0 := by
  rw [dilation_pointPair]
  have hc : 0 < (y - 1) ^ 2 / (4 * y) :=
    div_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hne)) (by positivity)
  constructor
  · intro h
    have hq : z.re ^ 2 / z.im ^ 2 = 0 := by nlinarith
    have hz : z.im ^ 2 ≠ 0 := by positivity
    have hr : z.re ^ 2 = 0 := (div_eq_zero_iff.mp hq).resolve_right hz
    nlinarith [sq_nonneg z.re]
  · intro h
    simp [h]

end TraceFormulas.Hyperbolic
