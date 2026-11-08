import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Finite matrix measurements

This is the finite counting-measure algebra underlying Section 0.3. It uses
Mathlib matrices and their actual matrix-vector product and trace. The bridges
to actual integrals are in `Analysis.FiniteCountingMeasure`; the general L²
identities and compression are in `Analysis.RelativeKernel` and `WeightedKernel`.
The pairing uses the book's convention: linear in the output, conjugate-linear
in the testing vector p. A finite index type may be empty.
-/

noncomputable section

open scoped BigOperators

namespace TraceFormulas

variable {ι : Type*} [Fintype ι]

/-- The counting-measure relative pairing, with input q and testing vector p. -/
def relativeMatrixPairing (A : Matrix ι ι ℂ) (p q : ι → ℂ) : ℂ :=
  ∑ i, (A.mulVec q) i * star (p i)

theorem relativeMatrixPairing_eq_sum (A : Matrix ι ι ℂ) (p q : ι → ℂ) :
    relativeMatrixPairing A p q = ∑ i, ∑ j, A i j * q j * star (p i) := by
  simp only [relativeMatrixPairing, Matrix.mulVec, dotProduct, Finset.sum_mul]

variable [DecidableEq ι]

/-- Coordinate testing vectors recover an arbitrary matrix entry. -/
theorem relativeMatrixPairing_single (A : Matrix ι ι ℂ) (i j : ι) :
    relativeMatrixPairing A (Pi.single i 1) (Pi.single j 1) = A i j := by
  simp [relativeMatrixPairing, Matrix.mulVec, dotProduct, Pi.single_apply]

/-- Multiplication by a function is a diagonal matrix in the indicator basis. -/
def weightedMatrixTrace (A : Matrix ι ι ℂ) (w : ι → ℂ) : ℂ :=
  Matrix.trace (Matrix.diagonal w * A)

theorem weightedMatrixTrace_eq_sum (A : Matrix ι ι ℂ) (w : ι → ℂ) :
    weightedMatrixTrace A w = ∑ i, w i * A i i := by
  simp only [weightedMatrixTrace, Matrix.trace, Matrix.diag_apply,
    Matrix.diagonal_mul]

theorem weightedMatrixTrace_one (A : Matrix ι ι ℂ) :
    weightedMatrixTrace A (fun _ => 1) = Matrix.trace A := by
  simp [weightedMatrixTrace_eq_sum, Matrix.trace, Matrix.diag_apply]

/-- A singleton indicator weight recovers the corresponding diagonal entry. -/
theorem weightedMatrixTrace_single (A : Matrix ι ι ℂ) (i : ι) :
    weightedMatrixTrace A (Pi.single i 1) = A i i := by
  simp [weightedMatrixTrace_eq_sum, Pi.single_apply]

/-- All diagonal weights agree for matrices with the same diagonal. -/
theorem weightedMatrixTrace_eq_of_diag_eq (A B : Matrix ι ι ℂ)
    (h : ∀ i, A i i = B i i) (w : ι → ℂ) :
    weightedMatrixTrace A w = weightedMatrixTrace B w := by
  simp only [weightedMatrixTrace_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [h i]

end TraceFormulas
