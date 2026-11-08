import TraceFormulas.LinearAlgebra.MatrixTrace
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Section 0.1: finite matrices and two descriptions of a trace

The principal declarations specialize the shared Mathlib-based results to
the manuscript's complex matrices. Fin n includes n = 0. The characteristic
root multiset counts algebraic multiplicity without assuming diagonalizability.

The examples use actual matrix multiplication and characteristic polynomials.
Build, axiom audit, and human correspondence review are separate ledger fields.
-/

noncomputable section

open scoped BigOperators

namespace TraceFormulas.Volume01.A.Chapter00.Section01

theorem trace_eq_diagonal_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace A = ∑ i, A i i := rfl

theorem trace_add {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (A + B) = Matrix.trace A + Matrix.trace B :=
  Matrix.trace_add A B

theorem trace_scalar {n : ℕ} (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (c • A) = c * Matrix.trace A := by
  simpa only [smul_eq_mul] using Matrix.trace_smul c A

theorem trace_identity (n : ℕ) :
    Matrix.trace (1 : Matrix (Fin n) (Fin n) ℂ) = (n : ℂ) := by
  simp

theorem trace_empty (A : Matrix (Fin 0) (Fin 0) ℂ) : Matrix.trace A = 0 :=
  Matrix.trace_fin_zero A

theorem trace_cyclic {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ) :
    Matrix.trace (A * B) = Matrix.trace (B * A) :=
  matrix_trace_cyclic A B

theorem trace_similarity {n : ℕ}
    (S A : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) :
    Matrix.trace (S⁻¹ * A * S) = Matrix.trace A :=
  matrix_trace_similarity_of_isUnit S A hS

theorem trace_eigenvalue_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (∑ i, A i i) = A.charpoly.roots.sum :=
  matrix_trace_eq_sum_roots A

theorem characteristic_roots_count {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    A.charpoly.roots.card = n := by
  simpa only [Fintype.card_fin] using matrix_charpoly_roots_card A

theorem characteristic_root_iff_eigenvector {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    A.charpoly.IsRoot z ↔ ∃ v : Fin n → ℂ, v ≠ 0 ∧ A.mulVec v = z • v :=
  matrix_isRoot_charpoly_iff A z

theorem endomorphism_trace {E : Type*} [AddCommGroup E] [Module ℂ E]
    {n : ℕ} (b : Basis (Fin n) ℂ E) (T : E →ₗ[ℂ] E) :
    LinearMap.trace ℂ E T = Matrix.trace (LinearMap.toMatrix b b T) :=
  endomorphism_trace_eq_basis_trace b T

def openingMatrix : Matrix (Fin 2) (Fin 2) ℂ := !![2, 1; 1, 2]

theorem opening_trace : Matrix.trace openingMatrix = 4 := by
  norm_num [Matrix.trace, Matrix.diag_apply, openingMatrix, Fin.sum_univ_two]

theorem opening_eigenvector_three :
    openingMatrix.mulVec ![1, 1] = (3 : ℂ) • ![1, 1] := by
  ext i
  fin_cases i <;> norm_num [openingMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem opening_eigenvector_one :
    openingMatrix.mulVec ![1, -1] = (1 : ℂ) • ![1, -1] := by
  ext i
  fin_cases i <;> norm_num [openingMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem opening_eigenvectors_nonzero :
    (![1, 1] : Fin 2 → ℂ) ≠ 0 ∧ (![1, -1] : Fin 2 → ℂ) ≠ 0 := by
  constructor <;> intro h <;> have h0 := congrFun h 0 <;> norm_num at h0

def rectangularA : Matrix (Fin 1) (Fin 2) ℂ := !![1, 2]

def rectangularB : Matrix (Fin 2) (Fin 1) ℂ := !![3; 4]

theorem rectangular_product_AB : rectangularA * rectangularB = !![11] := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [Matrix.mul_apply, rectangularA, rectangularB, Fin.sum_univ_two]

theorem rectangular_product_BA : rectangularB * rectangularA = !![3, 6; 4, 8] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, rectangularA, rectangularB, Fin.sum_univ_one]

theorem rectangular_trace_AB : Matrix.trace (rectangularA * rectangularB) = 11 := by
  rw [rectangular_product_AB]
  norm_num [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_one]

theorem rectangular_trace_BA : Matrix.trace (rectangularB * rectangularA) = 11 := by
  rw [← trace_cyclic rectangularA rectangularB]
  exact rectangular_trace_AB

def jordanMatrix : Matrix (Fin 2) (Fin 2) ℂ := !![2, 1; 0, 2]

theorem jordan_trace : Matrix.trace jordanMatrix = 4 := by
  norm_num [Matrix.trace, Matrix.diag_apply, jordanMatrix, Fin.sum_univ_two]

theorem jordan_charpoly :
    jordanMatrix.charpoly = (Polynomial.X - Polynomial.C (2 : ℂ)) ^ 2 := by
  simp [Matrix.charpoly, Matrix.det_fin_two, Matrix.charmatrix_apply,
    Matrix.diagonal_apply, jordanMatrix, pow_two]

theorem jordan_characteristic_roots : jordanMatrix.charpoly.roots = {2, 2} := by
  rw [jordan_charpoly, Polynomial.roots_pow, Polynomial.roots_X_sub_C]
  simp [two_smul]

theorem jordan_eigenspace (v : Fin 2 → ℂ) :
    jordanMatrix.mulVec v = (2 : ℂ) • v ↔ v 1 = 0 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    simpa [jordanMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h0
  · intro h
    ext i
    fin_cases i <;> simp [jordanMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, h]

theorem jordan_eigenspace_eq_span :
    Module.End.eigenspace (Matrix.toLin' jordanMatrix) (2 : ℂ) =
      Submodule.span ℂ {(![1, 0] : Fin 2 → ℂ)} := by
  ext v
  rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, jordan_eigenspace,
    Submodule.mem_span_singleton]
  constructor
  · intro h
    refine ⟨v 0, ?_⟩
    ext i
    fin_cases i <;> simp [h]
  · rintro ⟨a, rfl⟩
    simp

theorem jordan_eigenspace_dimension :
    Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' jordanMatrix) (2 : ℂ)) = 1 := by
  rw [jordan_eigenspace_eq_span]
  apply finrank_span_singleton
  intro h
  have h0 := congrFun h 0
  norm_num at h0

theorem jordan_only_eigenvalue (v : Fin 2 → ℂ) (hv : v ≠ 0) (z : ℂ)
    (heigen : jordanMatrix.mulVec v = z • v) : z = 2 := by
  by_contra hz
  have h0 := congrFun heigen 0
  have h1 := congrFun heigen 1
  simp [jordanMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  have hv1 : v 1 = 0 := by
    exact h1.resolve_left (fun h => hz h.symm)
  have hv0 : v 0 = 0 := by
    rw [hv1, add_zero] at h0
    by_contra hv0
    exact hz (mul_right_cancel₀ hv0 h0).symm
  apply hv
  funext i
  fin_cases i
  · exact hv0
  · exact hv1

/-- There is no basis consisting of eigenvectors, regardless of the listed eigenvalues. -/
theorem jordan_no_eigenbasis :
    ¬ ∃ (b : Basis (Fin 2) ℂ (Fin 2 → ℂ)) (z : Fin 2 → ℂ),
      ∀ j, jordanMatrix.mulVec (b j) = z j • b j := by
  rintro ⟨b, z, h⟩
  have hz : ∀ j, z j = 2 := fun j => jordan_only_eigenvalue (b j) (b.ne_zero j) (z j) (h j)
  have hb : ∀ j, (b j) 1 = 0 := by
    intro j
    apply (jordan_eigenspace (b j)).mp
    simpa only [hz j] using h j
  have hall (v : Fin 2 → ℂ) : v 1 = 0 := by
    have hrepr := congrFun (b.sum_repr v) 1
    simpa [hb] using hrepr.symm
  have hbad := hall ![0, 1]
  norm_num at hbad

end TraceFormulas.Volume01.A.Chapter00.Section01
