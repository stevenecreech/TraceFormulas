import Mathlib.Analysis.Complex.Periodic

/-!
# Exponential coordinates for a positive translation period

Mathlib's `Function.Periodic.qParam h z` is the actual complex exponential
`exp (2 * π * I * z / h)`. Its fibers and inverse below concern complex numbers;
they do not assume or formalize a modular quotient homeomorphism.
-/
noncomputable section
open Complex Function.Periodic
namespace TraceFormulas.CuspCoordinate

theorem parameter_ne_zero (h : ℝ) (z : ℂ) : qParam h z ≠ 0 :=
  Complex.exp_ne_zero _

theorem parameter_translate (h : ℝ) (hh : h ≠ 0) (z : ℂ) (n : ℤ) :
    qParam h (z + n * h) = qParam h z := by
  have hc : (h : ℂ) ≠ 0 := by exact_mod_cast hh
  unfold qParam
  have ha : 2 * (Real.pi : ℂ) * I * (z + n * h) / h =
      2 * (Real.pi : ℂ) * I * z / h + n * (2 * Real.pi * I) := by
    field_simp
    ring
  rw [ha, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem parameter_fibers (h : ℝ) (hh : h ≠ 0) (z w : ℂ) :
    qParam h z = qParam h w ↔ ∃ n : ℤ, z = w + n * h := by
  constructor
  · intro heq
    obtain ⟨m, hm⟩ := qParam_left_inv_mod_period hh z
    obtain ⟨n, hn⟩ := qParam_left_inv_mod_period hh w
    refine ⟨n - m, ?_⟩
    calc
      z = invQParam h (qParam h z) - m * h := by rw [hm]; ring
      _ = w + (n - m : ℤ) * h := by rw [heq, hn]; push_cast; ring
  · rintro ⟨n, rfl⟩
    exact parameter_translate h hh w n

theorem parameter_surjective_above (h : ℝ) (hh : 0 < h) (Y : ℝ)
    (q : ℂ) (hq : q ≠ 0) (hbound : ‖q‖ < Real.exp (-2 * Real.pi * Y / h)) :
    ∃ z : ℂ, Y < z.im ∧ qParam h z = q := by
  have heq := qParam_right_inv hh.ne' hq
  refine ⟨invQParam h q, ?_, heq⟩
  apply (norm_qParam_lt_iff hh Y (invQParam h q)).mp
  rwa [heq]

end TraceFormulas.CuspCoordinate
