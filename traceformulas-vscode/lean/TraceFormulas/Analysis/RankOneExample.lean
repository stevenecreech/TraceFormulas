import TraceFormulas.Analysis.FiniteKernelTrace
import TraceFormulas.Analysis.KernelRepresentatives
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The rank-one kernel on the unit interval

The manuscript's function sqrt(3) x is constructed as an actual complex L²
class for Lebesgue measure restricted to [0,1]. The finite-rank operator and
its trace are the objects defined in the shared kernel library, rather than
numbers introduced to reproduce the desired example.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace TraceFormulas

def rankOneFunction (x : ℝ) : ℂ := (Real.sqrt 3 : ℂ) * (x : ℂ)

theorem rankOneFunction_continuous : Continuous rankOneFunction :=
  continuous_const.mul Complex.continuous_ofReal

theorem rankOneFunction_memLp : MemLp rankOneFunction 2 unitIntervalMeasure := by
  apply MemLp.of_bound rankOneFunction_continuous.aestronglyMeasurable (Real.sqrt 3)
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with x hx
  simp only [rankOneFunction, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg 3), abs_of_nonneg hx.1]
  exact mul_le_of_le_one_right (Real.sqrt_nonneg 3) hx.2

def rankOneLp : Lp ℂ 2 unitIntervalMeasure := rankOneFunction_memLp.toLp rankOneFunction

theorem rankOneLp_ae : (rankOneLp : ℝ → ℂ) =ᵐ[unitIntervalMeasure] rankOneFunction :=
  rankOneFunction_memLp.coeFn_toLp

theorem integral_unitInterval_sq :
    (∫ x : ℝ, x ^ 2 ∂unitIntervalMeasure) = 1 / 3 := by
  change (∫ x : ℝ in Set.Icc 0 1, x ^ 2) = 1 / 3
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_pow]
  norm_num

theorem integral_unitInterval_complex_sq :
    (∫ x : ℝ, (x : ℂ) ^ 2 ∂unitIntervalMeasure) = 1 / 3 := by
  calc
    (∫ x : ℝ, (x : ℂ) ^ 2 ∂unitIntervalMeasure) =
        ∫ x : ℝ, ((x ^ 2 : ℝ) : ℂ) ∂unitIntervalMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => (Complex.ofReal_pow x 2).symm)
    _ = (((∫ x : ℝ, x ^ 2 ∂unitIntervalMeasure) : ℝ) : ℂ) :=
      integral_complex_ofReal (μ := unitIntervalMeasure) (f := fun x : ℝ => x ^ 2)
    _ = 1 / 3 := by rw [integral_unitInterval_sq]; norm_num

theorem rankOneFunction_mul_star (x y : ℝ) :
    rankOneFunction x * star (rankOneFunction y) = 3 * (x : ℂ) * (y : ℂ) := by
  have hs : (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ) = 3 := by
    norm_cast
    exact Real.mul_self_sqrt (by norm_num)
  simp only [rankOneFunction, star_mul, Complex.star_def, Complex.conj_ofReal]
  calc
    (Real.sqrt 3 : ℂ) * x * ((y : ℂ) * (Real.sqrt 3 : ℂ)) =
        ((Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ)) * ((x : ℂ) * (y : ℂ)) := by ring
    _ = 3 * (x : ℂ) * (y : ℂ) := by rw [hs]; ring

theorem integral_rankOneFunction_square :
    (∫ x, rankOneFunction x * star (rankOneFunction x) ∂unitIntervalMeasure) = 1 := by
  simp_rw [rankOneFunction_mul_star, mul_assoc, ← pow_two]
  rw [integral_const_mul, integral_unitInterval_complex_sq]
  norm_num

theorem rankOneLp_inner_self : inner ℂ rankOneLp rankOneLp = 1 := by
  change bookInner rankOneLp rankOneLp = 1
  rw [← integral_l2_mul_star]
  calc
    (∫ x, rankOneLp x * star (rankOneLp x) ∂unitIntervalMeasure) =
        ∫ x, rankOneFunction x * star (rankOneFunction x) ∂unitIntervalMeasure := by
      apply integral_congr_ae
      filter_upwards [rankOneLp_ae] with x hx
      rw [hx]
    _ = 1 := integral_rankOneFunction_square

theorem rankOneLp_norm : ‖rankOneLp‖ = 1 := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), rankOneLp_inner_self]
  norm_num

def rankOneFamily : Fin 1 → Lp ℂ 2 unitIntervalMeasure := fun _ => rankOneLp

theorem rankOneFamily_orthonormal : Orthonormal ℂ rankOneFamily :=
  ⟨fun _ => rankOneLp_norm, Subsingleton.pairwise⟩

def rankOneOperator (α : ℂ) :
    Lp ℂ 2 unitIntervalMeasure →L[ℂ] Lp ℂ 2 unitIntervalMeasure :=
  finiteOperator rankOneFamily (fun _ _ => α)

theorem rankOneOperator_eigen (α : ℂ) : rankOneOperator α rankOneLp = α • rankOneLp := by
  simpa [rankOneOperator, rankOneFamily, Fin.sum_univ_one] using
    (finiteOperator_basis rankOneFamily_orthonormal (fun _ _ => α) (0 : Fin 1))

theorem rankOneOperator_zero_orthogonal (α : ℂ) (f : Lp ℂ 2 unitIntervalMeasure)
    (hf : f ∈ (Submodule.span ℂ (Set.range rankOneFamily))ᗮ) :
    rankOneOperator α f = 0 :=
  finiteOperator_eq_zero_of_mem_orthogonal rankOneFamily (fun _ _ => α) f hf

theorem rankOne_kernel_formula (α : ℂ) (x y : ℝ) :
    finiteKernel (fun _ : Fin 1 => rankOneFunction) (fun _ _ => α) x y =
      3 * α * (x : ℂ) * (y : ℂ) := by
  simp only [finiteKernel, Fin.sum_univ_one]
  rw [mul_assoc, rankOneFunction_mul_star]
  ring

theorem rankOneOperator_trace (α : ℂ) :
    finiteRankTrace (rankOneOperator α).toLinearMap = α := by
  rw [rankOneOperator, finiteRankTrace_finiteOperator rankOneFamily_orthonormal]
  simp [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_one]

theorem rankOne_diagonal_integral (α : ℂ) :
    (∫ x : ℝ, 3 * α * (x : ℂ) * (x : ℂ) ∂unitIntervalMeasure) = α := by
  simp_rw [mul_assoc, ← pow_two]
  rw [integral_const_mul, integral_const_mul, integral_unitInterval_complex_sq]
  ring

theorem rankOne_trace_identity (α : ℂ) :
    (∫ x : ℝ, 3 * α * (x : ℂ) * (x : ℂ) ∂unitIntervalMeasure) =
      finiteRankTrace (rankOneOperator α).toLinearMap := by
  rw [rankOne_diagonal_integral, rankOneOperator_trace]

/-- The explicit integral action in the manuscript holds for the actual L² operator. -/
theorem rankOneOperator_integral (α : ℂ) (f : Lp ℂ 2 unitIntervalMeasure) :
    (fun x => rankOneOperator α f x) =ᵐ[unitIntervalMeasure]
      fun x => 3 * α * (x : ℂ) * (∫ y : ℝ, (y : ℂ) * f y ∂unitIntervalMeasure) := by
  filter_upwards [finiteOperator_eq_integral_ae rankOneFamily (fun _ _ => α) f,
    rankOneLp_ae] with x hx hxrep
  change rankOneOperator α f x = _ at hx
  rw [hx]
  calc
    (∫ y, finiteKernel (fun i => (rankOneFamily i : ℝ → ℂ))
        (fun _ _ => α) x y * f y ∂unitIntervalMeasure) =
        ∫ y, finiteKernel (fun _ : Fin 1 => rankOneFunction)
          (fun _ _ => α) x y * f y ∂unitIntervalMeasure := by
      apply integral_congr_ae
      filter_upwards [rankOneLp_ae] with y hyrep
      simp only [finiteKernel, rankOneFamily, Fin.sum_univ_one, hxrep, hyrep]
    _ = ∫ y : ℝ, 3 * α * (x : ℂ) * (y : ℂ) * f y ∂unitIntervalMeasure := by
      simp_rw [rankOne_kernel_formula]
    _ = 3 * α * (x : ℂ) * (∫ y : ℝ, (y : ℂ) * f y ∂unitIntervalMeasure) := by
      simpa only [mul_assoc] using
        (integral_const_mul (3 * α * (x : ℂ)) (fun y : ℝ => (y : ℂ) * f y))

end TraceFormulas
