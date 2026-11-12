import TraceFormulas.Geometry.RealMobius

/-!
# Section 1.1: checked portions of the real Möbius action

Uses Mathlib's actual determinant-one matrices and upper half-plane action.
The sphere action and scalar normalization, three-orbit classification, derivative,
and PSL action construction remain to be formalized.
The difference formula follows the edited common-denominator proof.
The cocycle and central-character compatibility belong to later modular-forms chapters.
The section status is in-progress; compilation does not approve correspondence.
-/
noncomputable section
open UpperHalfPlane TraceFormulas.Hyperbolic
namespace TraceFormulas.Volume01.A.Chapter01.Section01

theorem fractional_action (g : RealGroup) (z : ℍ) :
    ((g • z : ℍ) : ℂ) = ((g 0 0 : ℂ) * z + g 0 1) / factor g z :=
  action_formula g z

theorem denominator_nonzero (g : RealGroup) (z : ℍ) : factor g z ≠ 0 :=
  factor_ne_zero g z

theorem imaginary_part (g : RealGroup) (z : ℍ) :
    (g • z).im = z.im / Complex.normSq (factor g z) :=
  action_im g z

theorem difference_formula (g : RealGroup) (z w : ℍ) :
    ((g • z : ℍ) : ℂ) - ((g • w : ℍ) : ℂ) =
      ((z : ℂ) - w) / (factor g z * factor g w) :=
  action_difference g z w

theorem center_exactly_signs (g : RealGroup) :
    g ∈ Subgroup.center RealGroup ↔ g = 1 ∨ g = -1 :=
  center_iff g

theorem kernel_exactly_signs (g : RealGroup) :
    (∀ z : ℍ, g • z = z) ↔ g = 1 ∨ g = -1 :=
  action_kernel_iff g

theorem kernel_is_center (g : RealGroup) :
    (∀ z : ℍ, g • z = z) ↔ g ∈ Subgroup.center RealGroup :=
  action_kernel_eq_center g


theorem nonreal_imaginary_part (g : RealGroup) (z : ℂ) (hz : z.im ≠ 0) :
    factor g z ≠ 0 ∧
      (((g 0 0 : ℂ) * z + g 0 1) / factor g z).im = z.im / Complex.normSq (factor g z) :=
  Hyperbolic.nonreal_imaginary_part g z hz

end TraceFormulas.Volume01.A.Chapter01.Section01

