import TraceFormulas.Geometry.CuspCoordinate
import Mathlib.NumberTheory.Modular

/-!
# Section 1.7: the exponential cusp parameter (partial)

The book's e(z) is Mathlib's qParam 1 z, restricted to the upper half-plane
when it is denoted q(z). These results establish the exponential identities,
translation fibers, punctured-disk range and limit. Stabilizers, width as a
property of a group, quotient topology, path lengths and area remain gaps.
-/
noncomputable section
open Complex Function.Periodic UpperHalfPlane
open scoped MatrixGroups Topology
namespace TraceFormulas.Volume01.A.Chapter01.Section07

theorem parameter_formula (z : ℂ) :
    qParam 1 z = Complex.exp (2 * Real.pi * Complex.I * z) := by
  simp only [qParam, Complex.ofReal_one, div_one]

theorem parameter_nonzero (z : ℂ) : qParam 1 z ≠ 0 :=
  CuspCoordinate.parameter_ne_zero 1 z

theorem parameter_radius (z : ℍ) :
    ‖qParam 1 (z : ℂ)‖ = Real.exp (-2 * Real.pi * z.im) := by
  simpa only [div_one] using norm_qParam 1 (z : ℂ)

theorem parameter_integer_period (z : ℂ) (n : ℤ) :
    qParam 1 (z + n) = qParam 1 z := by
  simpa only [Complex.ofReal_one, mul_one] using
    CuspCoordinate.parameter_translate 1 (by norm_num) z n

theorem parameter_modular_translation (z : ℍ) (n : ℤ) :
    qParam 1 ((ModularGroup.T ^ n • z : ℍ) : ℂ) = qParam 1 (z : ℂ) := by
  rw [ModularGroup.coe_T_zpow_smul_eq]
  exact parameter_integer_period (z : ℂ) n

theorem parameter_equal_iff (z w : ℍ) :
    qParam 1 (z : ℂ) = qParam 1 (w : ℂ) ↔ ∃ n : ℤ, (z : ℂ) = w + n := by
  simpa only [Complex.ofReal_one, mul_one] using
    CuspCoordinate.parameter_fibers 1 (by norm_num) (z : ℂ) (w : ℂ)

theorem parameter_radius_iff_height (Y : ℝ) (z : ℍ) :
    ‖qParam 1 (z : ℂ)‖ < Real.exp (-2 * Real.pi * Y) ↔ Y < z.im := by
  simpa only [div_one] using norm_qParam_lt_iff (h := 1) (by norm_num) Y (z : ℂ)

theorem parameter_surjective (Y : ℝ) (hY : 0 ≤ Y) (q : ℂ) (hq : q ≠ 0)
    (hbound : ‖q‖ < Real.exp (-2 * Real.pi * Y)) :
    ∃ z : ℍ, Y < z.im ∧ qParam 1 (z : ℂ) = q := by
  obtain ⟨z, hz, heq⟩ := CuspCoordinate.parameter_surjective_above 1
    (by norm_num) Y q hq (by simpa only [div_one] using hbound)
  exact ⟨⟨z, lt_of_le_of_lt hY hz⟩, hz, heq⟩

theorem parameter_tends_to_puncture :
    Filter.Tendsto (qParam 1) (Filter.comap Complex.im Filter.atTop) (𝓝[≠] (0 : ℂ)) :=
  qParam_tendsto (by norm_num)

end TraceFormulas.Volume01.A.Chapter01.Section07
