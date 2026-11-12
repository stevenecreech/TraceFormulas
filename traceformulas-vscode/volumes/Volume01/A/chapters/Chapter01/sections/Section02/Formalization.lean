import TraceFormulas.Geometry.Iwasawa

/-!
# Section 1.2: elementary motions, coordinates and Iwasawa factorization

The formulas use the book's sqrt(y) diagonal parameter and its rotation sign.
The x and y coordinates, inverse position action and uniqueness of x, y and the
rotation matrix are included. The explicit angle formulas, angle classes modulo
2π, topological quotient equivalence and angular derivative remain open.
Haar measure is developed in Section 1.8 and is not claimed here.
-/
noncomputable section
open UpperHalfPlane TraceFormulas.Hyperbolic
namespace TraceFormulas.Volume01.A.Chapter01.Section02

/-! Elementary motions: hyperbolic.iwasawa-coordinates. -/
theorem n_translates (x : ℝ) (z : ℍ) :
    ((translation x • z : ℍ) : ℂ) = (z : ℂ) + x :=
  translation_action x z

theorem a_scales (y : ℝ) (hy : 0 < y) (z : ℍ) :
    ((dilation y hy • z : ℍ) : ℂ) = (y : ℂ) * z :=
  dilation_action y hy z

theorem k_fixes_base_point (θ : ℝ) : rotation θ • UpperHalfPlane.I = UpperHalfPlane.I :=
  rotation_fixes_I θ

theorem every_point_from_i (z : ℍ) : sectionMatrix z • UpperHalfPlane.I = z :=
  sectionMatrix_smul_I z

theorem upper_half_plane_transitive (z w : ℍ) : ∃ g : RealGroup, g • z = w :=
  transitive_action z w

/-! Stabilizer: hyperbolic.stabilizer. The orthogonal-group interface remains open. -/
theorem stabilizer_is_rotations (g : RealGroup) :
    g • UpperHalfPlane.I = UpperHalfPlane.I ↔ ∃ θ : ℝ, g = rotation θ :=
  fixes_I_iff_rotation g

theorem stabilizer_entry_equations (g : RealGroup) :
    g • UpperHalfPlane.I = UpperHalfPlane.I ↔
      g 0 0 = g 1 1 ∧ g 0 1 = -(g 1 0) :=
  fixes_I_iff_entries g

/-! Position matrix used in hyperbolic.iwasawa. -/
theorem inverse_position_action (z w : ℍ) :
    (((sectionMatrix z)⁻¹ • w : ℍ) : ℂ) =
      ((w : ℂ) - (z.re : ℂ)) / (z.im : ℂ) :=
  sectionMatrix_inverse_action z w

/-! Explicit coordinates: hyperbolic.iwasawa-explicit-coordinates (x and y only). -/
theorem orbit_point_coordinates (g : RealGroup) :
    (g • UpperHalfPlane.I).re =
        (g 0 0 * g 1 0 + g 0 1 * g 1 1) / ((g 1 0) ^ 2 + (g 1 1) ^ 2) ∧
    (g • UpperHalfPlane.I).im = 1 / ((g 1 0) ^ 2 + (g 1 1) ^ 2) :=
  base_point_coordinates g

/-! Algebraic ingredient for hyperbolic.quotient-description; topology remains open. -/
theorem same_point_modulo_stabilizer (g h : RealGroup) :
    g • UpperHalfPlane.I = h • UpperHalfPlane.I ↔
      h⁻¹ * g ∈ MulAction.stabilizer RealGroup UpperHalfPlane.I :=
  same_point_iff_stabilizer g h

/-! Factorization: hyperbolic.iwasawa. Uniqueness of angle classes remains open. -/
theorem iwasawa_factorization_exists (g : RealGroup) :
    ∃ θ : ℝ, g = translation (g • UpperHalfPlane.I).re *
      dilation (g • UpperHalfPlane.I).im (g • UpperHalfPlane.I).im_pos * rotation θ :=
  iwasawa_existence g

theorem unique_iwasawa_factors (x x' y y' : ℝ) (hy : 0 < y) (hy' : 0 < y') (θ θ' : ℝ)
    (h : translation x * dilation y hy * rotation θ =
      translation x' * dilation y' hy' * rotation θ') :
    x = x' ∧ y = y' ∧ rotation θ = rotation θ' :=
  iwasawa_unique x x' y y' hy hy' θ θ' h

end TraceFormulas.Volume01.A.Chapter01.Section02
