import TraceFormulas.Analysis.FiniteKernel
import TraceFormulas.Analysis.FiniteRankTrace
import TraceFormulas.LinearAlgebra.MatrixTrace

/-!
# Actual operator traces and finite kernel diagonals

The operator is the continuous linear map from `FiniteOrthonormal`, and its
trace is the canonical trace on its actual finite-dimensional range. The
span-basis calculation links these objects to the matrix trace, rather than
defining the operator trace to be the desired diagonal integral.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace TraceFormulas

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Fintype ι] [DecidableEq ι]
variable {u : ι → E}

theorem finiteOperator_toMatrix (hu : Orthonormal ℂ u) (A : Matrix ι ι ℂ) :
    LinearMap.toMatrix (Basis.span hu.linearIndependent) (Basis.span hu.linearIndependent)
      (supportedEndomorphism (finiteOperator u A).toLinearMap
        (Submodule.span ℂ (Set.range u)) (finiteOperator_range_le u A)) = A := by
  classical
  ext i j
  rw [LinearMap.toMatrix_apply, spanBasis_repr hu]
  change bookInner
    (finiteOperator u A ((Basis.span hu.linearIndependent j : Submodule.span ℂ (Set.range u)) : E))
    (u i) = A i j
  rw [Basis.span_apply, finiteOperator_basis hu, coefficient_of_sum hu]

theorem finiteRankTrace_finiteOperator (hu : Orthonormal ℂ u) (A : Matrix ι ι ℂ) :
    finiteRankTrace (finiteOperator u A).toLinearMap = Matrix.trace A := by
  classical
  letI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range u)) :=
    Module.Finite.of_basis (Basis.span hu.linearIndependent)
  rw [finiteRankTrace_eq_supported_trace _ (Submodule.span ℂ (Set.range u))
      (finiteOperator_range_le u A),
    LinearMap.trace_eq_matrix_trace ℂ (Basis.span hu.linearIndependent),
    finiteOperator_toMatrix hu]

theorem finiteOperator_diagonal (u : ι → E) (eigenvalue : ι → ℂ) (f : E) :
    finiteOperator u (Matrix.diagonal eigenvalue) f =
      ∑ j, (eigenvalue j * bookInner f (u j)) • u j := by
  classical
  simp [finiteOperator_apply, Matrix.diagonal]

theorem finite_spectral_operator_eq_diagonal (hu : Orthonormal ℂ u)
    (T : E →ₗ[ℂ] E) (eigenvalue : ι → ℂ)
    (heigen : ∀ j, T (u j) = eigenvalue j • u j)
    (hzero : ∀ r ∈ (Submodule.span ℂ (Set.range u))ᗮ, T r = 0) :
    T = (finiteOperator u (Matrix.diagonal eigenvalue)).toLinearMap := by
  ext f
  rw [finite_spectral_operator_expansion hu T eigenvalue heigen hzero]
  exact (finiteOperator_diagonal u eigenvalue f).symm

theorem finiteRankTrace_spectral_operator (hu : Orthonormal ℂ u)
    (T : E →ₗ[ℂ] E) (eigenvalue : ι → ℂ)
    (heigen : ∀ j, T (u j) = eigenvalue j • u j)
    (hzero : ∀ r ∈ (Submodule.span ℂ (Set.range u))ᗮ, T r = 0) :
    finiteRankTrace T = ∑ j, eigenvalue j := by
  rw [finite_spectral_operator_eq_diagonal hu T eigenvalue heigen hzero,
    finiteRankTrace_finiteOperator hu]
  exact Matrix.trace_diagonal eigenvalue

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- The integral equals the trace of the actual finite-rank operator. -/
theorem integral_finiteKernel_eq_operator_trace
    (u : ι → Lp ℂ 2 μ) (hu : Orthonormal ℂ u) (A : Matrix ι ι ℂ) :
    (∫ x, finiteKernel (fun i => (u i : X → ℂ)) A x x ∂μ) =
      finiteRankTrace (finiteOperator u A).toLinearMap := by
  rw [integral_finiteKernel_diagonal_eq_matrix_trace u hu, finiteRankTrace_finiteOperator hu]

/-- The general, possibly non-diagonalizable spectral equality uses characteristic
polynomial roots with their algebraic multiplicities. -/
theorem finiteKernel_trace_identity
    (u : ι → Lp ℂ 2 μ) (hu : Orthonormal ℂ u) (A : Matrix ι ι ℂ) :
    (∫ x, finiteKernel (fun i => (u i : X → ℂ)) A x x ∂μ) =
      finiteRankTrace (finiteOperator u A).toLinearMap ∧
    finiteRankTrace (finiteOperator u A).toLinearMap = A.charpoly.roots.sum := by
  exact ⟨integral_finiteKernel_eq_operator_trace u hu A,
    (finiteRankTrace_finiteOperator hu A).trans (matrix_trace_eq_sum_roots A)⟩

end TraceFormulas
