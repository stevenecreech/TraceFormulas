import TraceFormulas.Analysis.FiniteCountingMeasure
import TraceFormulas.Analysis.KernelRepresentatives
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-!
# Section 0.3: ordinary, relative, and weighted kernel measurements

The declarations below use genuine L² and L∞ classes, Lebesgue integrals,
bounded multiplication, orthogonal projection, and `LinearMap.trace`.
Build and axiom evidence are kept in the chapter audit rather than inferred
from source-file presence.
Human correspondence review: not reviewed.

Targets include `finite-relative-kernel-identity`,
`finite-relative-diagonal-identity`, `finite-weighted-kernel-identity`,
`finite-weighted-diagonal-identity`, and `finite-three-measurements-example`.
Fin 2 indices 0 and 1 correspond to the manuscript's points 1 and 2.
Counting measure gives ordinary finite sums, with no normalization factor.
The final counting-measure bridges identify the numerical matrix results
with actual kernel integrals. The shared library proves that point indicators
span the genuine finite counting-measure L² space and its projection is identity.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace TraceFormulas.Volume01.A.Chapter00.Section03

section GeneralKernels

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SigmaFinite μ] {N : ℕ}

/-- The book's scalar period, linear in its second displayed argument. -/
def period (p f : Lp ℂ 2 μ) : ℂ := bookInner f p

omit [SigmaFinite μ] in
theorem period_eq_integral (p f : Lp ℂ 2 μ) :
    period p f = ∫ x, f x * star (p x) ∂μ :=
  (integral_l2_mul_star f p).symm

omit [SigmaFinite μ] in
theorem ordinary_trace_identity
    (u : Fin N → Lp ℂ 2 μ) (hu : Orthonormal ℂ u) (A : Matrix (Fin N) (Fin N) ℂ) :
    (∫ x, finiteKernel (fun j => (u j : X → ℂ)) A x x ∂μ) = Matrix.trace A :=
  integral_finiteKernel_diagonal_eq_matrix_trace u hu A

/-- Proposition 0.3.3: absolute convergence, operator coefficient, and period formula. -/
theorem relative_kernel_identity
    (u : Fin N → Lp ℂ 2 μ) (A : Matrix (Fin N) (Fin N) ℂ) (p q : Lp ℂ 2 μ) :
    Integrable (fun z : X × X => finiteKernel (fun j => (u j : X → ℂ)) A z.1 z.2 *
      q z.2 * star (p z.1)) (μ.prod μ) ∧
    relativeKernelPairing μ (finiteKernel (fun j => (u j : X → ℂ)) A) p q =
      bookInner (finiteOperator u A q) p ∧
    relativeKernelPairing μ (finiteKernel (fun j => (u j : X → ℂ)) A) p q =
      ∑ i, ∑ j, A i j * period p (u i) * star (period q (u j)) :=
  ⟨integrable_relativeKernel u A p q,
    relativeKernelPairing_eq_operator u A p q,
    relativeKernelPairing_eq_periods u A p q⟩

theorem relative_diagonal_corollary
    (u : Fin N → Lp ℂ 2 μ) (eigenvalue : Fin N → ℂ) (p q : Lp ℂ 2 μ) :
    relativeKernelPairing μ
        (finiteKernel (fun j => (u j : X → ℂ)) (Matrix.diagonal eigenvalue)) p q =
      ∑ j, eigenvalue j * period p (u j) * star (period q (u j)) :=
  relativeKernelPairing_diagonal u eigenvalue p q

omit [SigmaFinite μ] in
/-- Proposition 0.3.6, using the trace of the actual compressed endomorphism. -/
theorem weighted_kernel_identity
    (u : Fin N → Lp ℂ 2 μ) (hu : Orthonormal ℂ u)
    (A : Matrix (Fin N) (Fin N) ℂ) (w : Lp ℂ ⊤ μ) :
    Integrable (fun x => w x * finiteKernel (fun j => (u j : X → ℂ)) A x x) μ ∧
    weightedKernelIntegral μ (finiteKernel (fun j => (u j : X → ℂ)) A) w =
      LinearMap.trace ℂ (Submodule.span ℂ (Set.range u))
        (compressedFiniteOperator u A (multiplicationOperator w)) ∧
    weightedKernelIntegral μ (finiteKernel (fun j => (u j : X → ℂ)) A) w =
      ∑ i, ∑ j, A i j * ∫ x, w x * u i x * star (u j x) ∂μ := by
  refine ⟨integrable_weightedKernel u A w, weightedKernelIntegral_eq_trace u hu A w, ?_⟩
  simpa only [integral_weighted_l2_mul_star] using weightedKernelIntegral_eq_sum u A w

omit [SigmaFinite μ] in
theorem weighted_diagonal_corollary
    (u : Fin N → Lp ℂ 2 μ) (eigenvalue : Fin N → ℂ) (w : Lp ℂ ⊤ μ) :
    weightedKernelIntegral μ
        (finiteKernel (fun j => (u j : X → ℂ)) (Matrix.diagonal eigenvalue)) w =
      ∑ j, eigenvalue j * ∫ x, w x * (‖u j x‖ : ℂ) ^ 2 ∂μ :=
  weightedKernelIntegral_diagonal_norm u eigenvalue w

theorem relative_representatives
    (u v : Fin N → X → ℂ) (A : Matrix (Fin N) (Fin N) ℂ)
    (h : ∀ j, u j =ᵐ[μ] v j) {p p' q q' : X → ℂ}
    (hp : p =ᵐ[μ] p') (hq : q =ᵐ[μ] q') :
    relativeKernelPairing μ (finiteKernel u A) p q =
      relativeKernelPairing μ (finiteKernel v A) p' q' :=
  relativeKernelPairing_congr_ae (finiteKernel_product_ae_congr A u v h) hp hq

omit [SigmaFinite μ] in
theorem weighted_representatives
    (u v : Fin N → X → ℂ) (A : Matrix (Fin N) (Fin N) ℂ)
    (h : ∀ j, u j =ᵐ[μ] v j) {w w' : X → ℂ} (hw : w =ᵐ[μ] w') :
    weightedKernelIntegral μ (finiteKernel u A) w =
      weightedKernelIntegral μ (finiteKernel v A) w' :=
  weightedKernelIntegral_congr_diagonal_ae (finiteKernel_diagonal_ae_congr A u v h) hw

end GeneralKernels

def exampleA : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 2]

def exampleB : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 1, 2]

def firstIndicator : Fin 2 → ℂ := Pi.single 0 1

def secondIndicator : Fin 2 → ℂ := Pi.single 1 1

theorem input_exampleA : exampleA.mulVec secondIndicator = ![0, 2] := by
  ext i
  fin_cases i <;> norm_num [exampleA, secondIndicator, Pi.single_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem input_exampleB : exampleB.mulVec secondIndicator = ![1, 2] := by
  ext i
  fin_cases i <;> norm_num [exampleB, secondIndicator, Pi.single_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem weighted_matrix_exampleA (w : Fin 2 → ℂ) :
    Matrix.diagonal w * exampleA = !![w 0, 0; 0, 2 * w 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_mul, exampleA, mul_comm]

theorem weighted_matrix_exampleB (w : Fin 2 → ℂ) :
    Matrix.diagonal w * exampleB = !![w 0, w 0; w 1, 2 * w 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_mul, exampleB, mul_comm]

theorem ordinary_exampleA : Matrix.trace exampleA = 3 := by
  norm_num [Matrix.trace, Matrix.diag_apply, exampleA, Fin.sum_univ_two]

theorem ordinary_exampleB : Matrix.trace exampleB = 3 := by
  norm_num [Matrix.trace, Matrix.diag_apply, exampleB, Fin.sum_univ_two]

theorem relative_exampleA :
    relativeMatrixPairing exampleA firstIndicator secondIndicator = 0 := by
  rw [firstIndicator, secondIndicator, relativeMatrixPairing_single]
  rfl

theorem relative_exampleB :
    relativeMatrixPairing exampleB firstIndicator secondIndicator = 1 := by
  rw [firstIndicator, secondIndicator, relativeMatrixPairing_single]
  rfl

theorem weighted_exampleA (w : Fin 2 → ℂ) :
    weightedMatrixTrace exampleA w = w 0 + 2 * w 1 := by
  simp [weightedMatrixTrace_eq_sum, exampleA, Fin.sum_univ_two, mul_comm]

theorem weighted_exampleB (w : Fin 2 → ℂ) :
    weightedMatrixTrace exampleB w = w 0 + 2 * w 1 := by
  simp [weightedMatrixTrace_eq_sum, exampleB, Fin.sum_univ_two, mul_comm]

theorem weighted_first_exampleA :
    weightedMatrixTrace exampleA firstIndicator = 1 := by
  rw [firstIndicator, weightedMatrixTrace_single]
  rfl

theorem weighted_first_exampleB :
    weightedMatrixTrace exampleB firstIndicator = 1 := by
  rw [firstIndicator, weightedMatrixTrace_single]
  rfl

theorem weighted_second_exampleA :
    weightedMatrixTrace exampleA secondIndicator = 2 := by
  rw [secondIndicator, weightedMatrixTrace_single]
  rfl

theorem weighted_second_exampleB :
    weightedMatrixTrace exampleB secondIndicator = 2 := by
  rw [secondIndicator, weightedMatrixTrace_single]
  rfl

section CountingIntegrals

local instance : MeasurableSpace (Fin 2) := ⊤

theorem ordinary_integral_exampleA :
    (∫ x, exampleA x x ∂Measure.count) = 3 := by
  rw [ordinaryKernelIntegral_count, ordinary_exampleA]

theorem ordinary_integral_exampleB :
    (∫ x, exampleB x x ∂Measure.count) = 3 := by
  rw [ordinaryKernelIntegral_count, ordinary_exampleB]

theorem relative_integral_exampleA :
    relativeKernelPairing Measure.count exampleA firstIndicator secondIndicator = 0 := by
  rw [relativeKernelPairing_count, relative_exampleA]

theorem relative_integral_exampleB :
    relativeKernelPairing Measure.count exampleB firstIndicator secondIndicator = 1 := by
  rw [relativeKernelPairing_count, relative_exampleB]

theorem weighted_integral_exampleA (w : Fin 2 → ℂ) :
    weightedKernelIntegral Measure.count exampleA w = w 0 + 2 * w 1 := by
  rw [weightedKernelIntegral_count, weighted_exampleA]

theorem weighted_integral_exampleB (w : Fin 2 → ℂ) :
    weightedKernelIntegral Measure.count exampleB w = w 0 + 2 * w 1 := by
  rw [weightedKernelIntegral_count, weighted_exampleB]

end CountingIntegrals

end TraceFormulas.Volume01.A.Chapter00.Section03
