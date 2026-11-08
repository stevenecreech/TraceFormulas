import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Trace

/-!
# Matrix traces and characteristic-polynomial roots

These declarations use Mathlib's matrix multiplication, matrix trace,
characteristic polynomial, root multiset, and endomorphism trace directly.
There is no project-specific replacement for any of these operations.

The root multiset counts algebraic multiplicity. Its sum theorem does not
assume diagonalizability, and all finite index types below may be empty.

Build and axiom-audit status is recorded separately in the chapter ledger.
-/

noncomputable section

open scoped BigOperators

namespace TraceFormulas

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Cyclicity includes compatible rectangular matrices. -/
theorem matrix_trace_cyclic (A : Matrix ι κ ℂ) (B : Matrix κ ι ℂ) :
    Matrix.trace (A * B) = Matrix.trace (B * A) :=
  Matrix.trace_mul_comm A B

variable [DecidableEq ι]

/-- An invertible change of coordinates, represented by a matrix unit. -/
theorem matrix_trace_similarity (S : (Matrix ι ι ℂ)ˣ) (A : Matrix ι ι ℂ) :
    Matrix.trace ((↑(S⁻¹) : Matrix ι ι ℂ) * A * (S : Matrix ι ι ℂ)) =
      Matrix.trace A :=
  Matrix.trace_units_conj' S A

/-- The usual matrix-inverse notation with explicit invertibility. -/
theorem matrix_trace_similarity_of_isUnit (S A : Matrix ι ι ℂ) (hS : IsUnit S) :
    Matrix.trace (S⁻¹ * A * S) = Matrix.trace A :=
  Matrix.trace_conj' hS A

/-- The trace is the sum of all characteristic roots with multiplicity. -/
theorem matrix_trace_eq_sum_roots (A : Matrix ι ι ℂ) :
    Matrix.trace A = A.charpoly.roots.sum :=
  Matrix.trace_eq_sum_roots_charpoly A

/-- Over the complex numbers, the root multiset has exactly the matrix size. -/
theorem matrix_charpoly_roots_card (A : Matrix ι ι ℂ) :
    A.charpoly.roots.card = Fintype.card ι := by
  calc
    A.charpoly.roots.card = A.charpoly.natDegree :=
      Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits A.charpoly)
    _ = Fintype.card ι := Matrix.charpoly_natDegree_eq_dim A

/-- A characteristic root is an eigenvalue in the nonzero-vector sense. -/
theorem matrix_isRoot_charpoly_iff (A : Matrix ι ι ℂ) (z : ℂ) :
    A.charpoly.IsRoot z ↔ ∃ v : ι → ℂ, v ≠ 0 ∧ A.mulVec v = z • v := by
  rw [Polynomial.IsRoot, Matrix.eval_charpoly, ← Matrix.exists_mulVec_eq_zero_iff]
  have scalar_action (v : ι → ℂ) : (Matrix.scalar ι z).mulVec v = z • v := by
    ext i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  constructor
  · rintro ⟨v, hv, h⟩
    rw [Matrix.sub_mulVec, scalar_action, sub_eq_zero] at h
    exact ⟨v, hv, h.symm⟩
  · rintro ⟨v, hv, h⟩
    refine ⟨v, hv, ?_⟩
    rw [Matrix.sub_mulVec, scalar_action, sub_eq_zero]
    exact h.symm

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- Mathlib's endomorphism trace is the trace of its matrix in any finite basis. -/
theorem endomorphism_trace_eq_basis_trace (b : Basis ι ℂ E) (T : E →ₗ[ℂ] E) :
    LinearMap.trace ℂ E T = Matrix.trace (LinearMap.toMatrix b b T) :=
  LinearMap.trace_eq_matrix_trace ℂ b T

/-- The two bases may be indexed by different finite types. -/
theorem endomorphism_basis_trace_independent [DecidableEq κ]
    (b : Basis ι ℂ E) (c : Basis κ ℂ E) (T : E →ₗ[ℂ] E) :
    Matrix.trace (LinearMap.toMatrix b b T) =
      Matrix.trace (LinearMap.toMatrix c c T) := by
  rw [← endomorphism_trace_eq_basis_trace b T,
    ← endomorphism_trace_eq_basis_trace c T]

end TraceFormulas
