import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! Real determinant-one Möbius transformations on Mathlib's actual upper half-plane.
The sphere action and its three-orbit classification remain separate obligations.
-/
noncomputable section
open scoped MatrixGroups
open UpperHalfPlane
namespace TraceFormulas.Hyperbolic

abbrev RealGroup := SL(2, ℝ)

/-- The fractional denominator; used as an automorphy factor in later chapters. -/
def factor (g : RealGroup) (z : ℂ) : ℂ := (g 1 0 : ℂ) * z + g 1 1

theorem factor_ne_zero (g : RealGroup) (z : ℍ) : factor g z ≠ 0 := by
  exact UpperHalfPlane.denom_ne_zero (g : GL (Fin 2) ℝ) z

theorem action_formula (g : RealGroup) (z : ℍ) :
    ((g • z : ℍ) : ℂ) = ((g 0 0 : ℂ) * z + g 0 1) / factor g z := by
  simpa [factor] using UpperHalfPlane.coe_specialLinearGroup_apply g z

theorem center_iff (g : RealGroup) :
    g ∈ Subgroup.center RealGroup ↔ g = 1 ∨ g = -1 := by
  constructor
  · intro h
    obtain ⟨r, hr, hm⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h
    have hs : r ^ 2 = 1 := by simpa using hr
    rcases sq_eq_one_iff.mp hs with hr | hr
    · subst r
      left
      apply Subtype.ext
      simpa using hm.symm
    · subst r
      right
      apply Subtype.ext
      simpa only [map_neg, map_one, Matrix.SpecialLinearGroup.coe_neg,
        Matrix.SpecialLinearGroup.coe_one] using hm.symm
  · rintro (rfl | rfl)
    · exact (Subgroup.center RealGroup).one_mem
    · apply Subgroup.mem_center_iff.mpr
      intro h
      simp

/-- The kernel calculation uses i and 2i to determine the matrix entries. -/
theorem action_kernel_iff (g : RealGroup) :
    (∀ z : ℍ, g • z = z) ↔ g = 1 ∨ g = -1 := by
  constructor
  · intro h
    have equation (z : ℍ) :
        (g 0 0 : ℂ) * z + g 0 1 = (z : ℂ) * factor g z := by
      apply (div_eq_iff (factor_ne_zero g z)).mp
      rw [← action_formula, h]
    have h1 := equation UpperHalfPlane.I
    have h2 := equation (⟨2 * Complex.I, by norm_num⟩ : ℍ)
    have hr1 := congrArg Complex.re h1
    have hi1 := congrArg Complex.im h1
    have hr2 := congrArg Complex.re h2
    simp [factor, UpperHalfPlane.coe_I] at hr1 hi1 hr2
    have hc : g 1 0 = 0 := by linarith
    have hb : g 0 1 = 0 := by linarith
    have hd : g 1 1 = g 0 0 := by linarith
    have hdet := g.property
    rw [Matrix.det_fin_two] at hdet
    have ha : (g 0 0) ^ 2 = 1 := by simpa [hc, hb, hd, pow_two] using hdet
    rcases sq_eq_one_iff.mp ha with ha | ha
    · left
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hc, hb, hd, ha]
    · right
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hc, hb, hd, ha]
  · rintro (rfl | rfl) z
    · exact one_smul _ z
    · apply UpperHalfPlane.ext
      simp [action_formula, factor]

theorem action_kernel_eq_center (g : RealGroup) :
    (∀ z : ℍ, g • z = z) ↔ g ∈ Subgroup.center RealGroup :=
  (action_kernel_iff g).trans (center_iff g).symm


theorem action_im (g : RealGroup) (z : ℍ) :
    (g • z).im = z.im / Complex.normSq (factor g z) := by
  change Complex.im ((g • z : ℍ) : ℂ) = _
  rw [action_formula]
  simpa [factor, UpperHalfPlane.num, UpperHalfPlane.denom] using
    UpperHalfPlane.moebius_im (g : GL (Fin 2) ℝ) (z : ℂ)

/-- Subtract the two fractions over a common denominator, then use determinant one. -/
theorem action_difference (g : RealGroup) (z w : ℍ) :
    ((g • z : ℍ) : ℂ) - ((g • w : ℍ) : ℂ) =
      ((z : ℂ) - w) / (factor g z * factor g w) := by
  rw [action_formula, action_formula,
    div_sub_div _ _ (factor_ne_zero g z) (factor_ne_zero g w)]
  have hdet : (g 0 0 : ℂ) * (g 1 1 : ℂ) - (g 0 1 : ℂ) * (g 1 0 : ℂ) = 1 := by
    exact_mod_cast (show g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 by
      simpa only [Matrix.det_fin_two] using g.property)
  congr 1
  calc
    _ = ((g 0 0 : ℂ) * (g 1 1 : ℂ) - (g 0 1 : ℂ) * (g 1 0 : ℂ)) *
        ((z : ℂ) - w) := by simp only [factor]; ring
    _ = (z : ℂ) - w := by rw [hdet, one_mul]

/-- Kept for the later modular-forms chapter; not a Section 1.1 prose claim. -/
theorem factor_cocycle (g h : RealGroup) (z : ℍ) :
    factor (g * h) z = factor g ((h • z : ℍ) : ℂ) * factor h z := by
  have hc := UpperHalfPlane.denom_cocycle (g : GL (Fin 2) ℝ)
    (h : GL (Fin 2) ℝ) z.im_ne_zero
  simpa [factor, UpperHalfPlane.denom, UpperHalfPlane.num, action_formula] using hc


/-- The finite-chart imaginary-part identity applies in both nonreal half-planes. -/
theorem nonreal_imaginary_part (g : RealGroup) (z : ℂ) (hz : z.im ≠ 0) :
    factor g z ≠ 0 ∧
      (((g 0 0 : ℂ) * z + g 0 1) / factor g z).im = z.im / Complex.normSq (factor g z) := by
  constructor
  · exact UpperHalfPlane.denom_ne_zero_of_im (g : GL (Fin 2) ℝ) hz
  · simpa [factor, UpperHalfPlane.num, UpperHalfPlane.denom] using
      UpperHalfPlane.moebius_im (g : GL (Fin 2) ℝ) z

end TraceFormulas.Hyperbolic


