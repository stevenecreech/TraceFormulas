import TraceFormulas.Geometry.IsometryTypes

/-!
# Section 1.5: fixed points, normal forms and displacement (partial coverage)

The actual Möbius action and matrix trace are used. The checked algebraic
statements below are ingredients of the prose proofs, not a formalization of
the complete boundary classification or of translation length as a metric infimum.
See compare.tex for the exact outstanding statements and proof-route differences.
-/
noncomputable section
open UpperHalfPlane TraceFormulas.Hyperbolic
namespace TraceFormulas.Volume01.A.Chapter01.Section05

/-! Definition hyperbolic.types and classification hyperbolic.fixed-point-classification. -/
theorem discriminant_lift_independent (g : RealGroup) :
    typeDiscriminant (-g) = typeDiscriminant g := typeDiscriminant_neg g

theorem quadratic_discriminant (g : RealGroup) :
    typeDiscriminant g = (g 1 1 - g 0 0) ^ 2 + 4 * g 0 1 * g 1 0 :=
  typeDiscriminant_quadratic g

theorem fixed_point_equation (g : RealGroup) (z : ℍ) :
    g • z = z ↔ (g 1 0 : ℂ) * (z : ℂ)^2 +
      ((g 1 1 : ℂ) - g 0 0) * z - g 0 1 = 0 := fixes_iff_quadratic g z

theorem interior_fixed_point_discriminant (g : RealGroup) (z : ℍ) (h : g • z = z) :
    typeDiscriminant g = -4 * (g 1 0 * z.im) ^ 2 := fixedPoint_discriminant g z h

/-! hyperbolic.elliptic-normal-form: normalizing an already supplied fixed point. -/
theorem fixed_point_conjugates_to_rotation (g : RealGroup) (p : ℍ) (hp : g • p = p) :
    ∃ θ : ℝ, (sectionMatrix p)⁻¹ * g * sectionMatrix p = rotation θ :=
  conjugate_fixedPoint_rotation g p hp

/-! Normal forms: exact interior fixed-point conditions, including the identity cases. -/
theorem translation_has_fixed_point_iff (t : ℝ) (z : ℍ) :
    translation t • z = z ↔ t = 0 := translation_fixed_iff t z

theorem dilation_has_fixed_point_iff (y : ℝ) (hy : 0 < y) (z : ℍ) :
    dilation y hy • z = z ↔ y = 1 := dilation_fixed_iff y hy z

/-! hyperbolic.parabolic-length: the point-pair calculation, not yet the metric infimum. -/
theorem translation_point_pair (t : ℝ) (z : ℍ) :
    pointPair z (translation t • z) = t ^ 2 / (4 * z.im ^ 2) := translation_pointPair t z

/-! hyperbolic.hyperbolic-length: the calculation and minimizing set in dilation coordinates. -/
theorem dilation_point_pair (y : ℝ) (hy : 0 < y) (z : ℍ) :
    pointPair z (dilation y hy • z) =
      (y - 1) ^ 2 / (4 * y) * (1 + z.re ^ 2 / z.im ^ 2) := dilation_pointPair y hy z

theorem dilation_displacement_lower_bound (y : ℝ) (hy : 0 < y) (z : ℍ) :
    (y - 1) ^ 2 / (4 * y) ≤ pointPair z (dilation y hy • z) :=
  dilation_pointPair_lower y hy z

theorem dilation_minimizers_are_on_imaginary_axis (y : ℝ) (hy : 0 < y)
    (hne : y ≠ 1) (z : ℍ) :
    pointPair z (dilation y hy • z) = (y - 1) ^ 2 / (4 * y) ↔ z.re = 0 :=
  dilation_pointPair_min_iff y hy hne z

end TraceFormulas.Volume01.A.Chapter01.Section05
