import TraceFormulas.Analysis.FiniteKernel

/-! # The counting-measure kernel really is the matrix -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace TraceFormulas

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem finiteKernel_pointIndicators (A : Matrix ι ι ℂ) (x y : ι) :
    finiteKernel (fun i => Pi.single i (1 : ℂ)) A x y = A x y := by
  simp [finiteKernel, Pi.single_apply]

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem counting_kernel_integral_eq_mulVec (A : Matrix ι ι ℂ) (f : ι → ℂ) (x : ι) :
    (∫ y, finiteKernel (fun i => Pi.single i (1 : ℂ)) A x y * f y ∂Measure.count) =
      A.mulVec f x := by
  simp [finiteKernel_pointIndicators, Matrix.mulVec, dotProduct]

theorem counting_kernel_diagonal_integral (A : Matrix ι ι ℂ) :
    (∫ x, finiteKernel (fun i => Pi.single i (1 : ℂ)) A x x ∂Measure.count) =
      Matrix.trace A := by
  simp [finiteKernel_pointIndicators, Matrix.trace, Matrix.diag_apply]

end TraceFormulas
