import TraceFormulas.Analysis.RelativeKernel
import TraceFormulas.Analysis.WeightedKernel
import TraceFormulas.Analysis.FiniteCountingKernel
import TraceFormulas.Analysis.FiniteProjection
import TraceFormulas.LinearAlgebra.FiniteKernelMeasurements

/-!
# Counting-measure specialization

These bridges identify the explicit matrix calculations with actual kernel
integrals on a finite counting-measure space. No normalization factor is used.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace TraceFormulas

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- In the point-indicator basis the finite kernel is exactly the matrix entry. -/
theorem finiteKernel_indicators (A : Matrix ι ι ℂ) (x y : ι) :
    finiteKernel (fun j => Pi.single j 1) A x y = A x y :=
  finiteKernel_pointIndicators A x y

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem indicator_period_count (i j : ι) :
    (∫ x, Pi.single i (1 : ℂ) x * star (Pi.single j (1 : ℂ) x) ∂Measure.count) =
      if i = j then (1 : ℂ) else 0 := by
  simp [Pi.single_apply, eq_comm]

omit [DecidableEq ι] in
theorem ordinaryKernelIntegral_count (A : Matrix ι ι ℂ) :
    (∫ x, A x x ∂Measure.count) = Matrix.trace A := by
  simp [Matrix.trace, Matrix.diag_apply]

omit [DecidableEq ι] in
theorem relativeKernelPairing_count (A : Matrix ι ι ℂ) (p q : ι → ℂ) :
    relativeKernelPairing Measure.count A p q = relativeMatrixPairing A p q := by
  simp only [relativeKernelPairing, integral_count, relativeMatrixPairing,
    Matrix.mulVec, dotProduct, Finset.sum_mul]

theorem weightedKernelIntegral_count (A : Matrix ι ι ℂ) (w : ι → ℂ) :
    weightedKernelIntegral Measure.count A w = weightedMatrixTrace A w := by
  simp only [weightedKernelIntegral, integral_count, weightedMatrixTrace_eq_sum]

/-- Every function on the finite counting space defines an actual L² class. -/
def countingL2 (f : ι → ℂ) : Lp ℂ 2 (Measure.count : Measure ι) :=
  (MemLp.of_discrete : MemLp f 2 Measure.count).toLp f

omit [DecidableEq ι] in
theorem countingL2_coe (f : ι → ℂ) (x : ι) : countingL2 f x = f x := by
  exact Measure.ae_count_iff.mp (MemLp.coeFn_toLp (MemLp.of_discrete : MemLp f 2 Measure.count)) x

/-- The L² class of the indicator of one point. -/
def countingIndicator (i : ι) : Lp ℂ 2 (Measure.count : Measure ι) :=
  countingL2 (Pi.single i 1)

theorem countingIndicator_orthonormal : Orthonormal ℂ (countingIndicator (ι := ι)) := by
  rw [orthonormal_iff_ite]
  intro i j
  change bookInner (countingIndicator j) (countingIndicator i) = _
  rw [← integral_l2_mul_star]
  simpa only [countingIndicator, countingL2_coe, eq_comm] using indicator_period_count j i

theorem countingIndicator_expansion (f : Lp ℂ 2 (Measure.count : Measure ι)) :
    f = ∑ i, f i • countingIndicator i := by
  apply Lp.ext
  filter_upwards [coeFn_l2_sum_smul (countingIndicator (ι := ι)) (fun i => f i)] with x hx
  rw [hx]
  simp [countingIndicator, countingL2_coe, Pi.single_apply]

theorem countingIndicator_span :
    Submodule.span ℂ (Set.range (countingIndicator (ι := ι))) = ⊤ := by
  apply top_unique
  intro f _
  rw [countingIndicator_expansion f]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_range_self i))

theorem countingIndicator_projection (f : Lp ℂ 2 (Measure.count : Measure ι)) :
    (finiteSpanProjection (countingIndicator (ι := ι)) f : Lp ℂ 2 Measure.count) = f := by
  letI : FiniteDimensional ℂ
    (Submodule.span ℂ (Set.range (countingIndicator (ι := ι)))) :=
      FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  apply Submodule.orthogonalProjection_eq_self_iff.mpr
  rw [countingIndicator_span]
  exact Submodule.mem_top

end TraceFormulas
