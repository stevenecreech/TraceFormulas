import TraceFormulas.Analysis.FiniteKernel
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.LinearAlgebra.Trace

/-!
# Weighted finite-kernel traces

The multiplication operator below is Mathlib's Hölder construction on genuine
L∞ and L² classes. The compressed endomorphism uses the actual orthogonal
projection onto the finite span, and its trace is `LinearMap.trace`.
Compilation and axiom evidence are recorded separately in the chapter audit.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace TraceFormulas

section Compression

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Fintype ι]

/-- The actual endomorphism obtained by restriction, multiplication by an
operator `M`, and orthogonal projection back onto the finite span. -/
def compressedFiniteOperator (u : ι → E) (A : Matrix ι ι ℂ) (M : E →L[ℂ] E) :
    Submodule.span ℂ (Set.range u) →ₗ[ℂ] Submodule.span ℂ (Set.range u) := by
  let V := Submodule.span ℂ (Set.range u)
  letI : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ (Set.finite_range u)
  exact (V.orthogonalProjection.toLinearMap.comp
    (M.toLinearMap.comp (finiteOperator u A).toLinearMap)).comp V.subtype

/-- The trace of a genuine compressed endomorphism, computed in its orthonormal basis. -/
theorem trace_compressedFiniteOperator
    (u : ι → E) (hu : Orthonormal ℂ u) (A : Matrix ι ι ℂ) (M : E →L[ℂ] E) :
    LinearMap.trace ℂ (Submodule.span ℂ (Set.range u))
      (compressedFiniteOperator u A M) =
      ∑ i, ∑ j, A i j * bookInner (M (u i)) (u j) := by
  classical
  let V := Submodule.span ℂ (Set.range u)
  letI : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ (Set.finite_range u)
  let b := Basis.span hu.linearIndependent
  have hb (j : ι) : ((b j : V) : E) = u j := Basis.span_apply hu.linearIndependent j
  have hcoeff (j : ι) :
      bookInner ((compressedFiniteOperator u A M (b j) : V) : E) (u j) =
        ∑ i, A i j * bookInner (M (u i)) (u j) := by
    change inner ℂ (u j)
      ((V.orthogonalProjection (M (finiteOperator u A ((b j : V) : E)))) : E) = _
    rw [← Basis.span_apply hu.linearIndependent j, ← Submodule.coe_inner,
      Submodule.inner_orthogonalProjection_eq_of_mem_left]
    simp only [hb, finiteOperator_basis hu, map_sum, map_smul,
      inner_sum, inner_smul_right, bookInner]
  rw [LinearMap.trace_eq_matrix_trace ℂ b]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply, b, spanBasis_repr hu]
  calc
    (∑ j, bookInner ((compressedFiniteOperator u A M (b j) : V) : E) (u j)) =
        ∑ j, ∑ i, A i j * bookInner (M (u i)) (u j) := by
      exact Finset.sum_congr rfl (fun j _ => hcoeff j)
    _ = ∑ i, ∑ j, A i j * bookInner (M (u i)) (u j) := Finset.sum_comm

end Compression

variable {X ι : Type*} [MeasurableSpace X] {μ : Measure X} [Fintype ι]

/-- Multiplication by an L∞ class, as a bounded operator on L². -/
def multiplicationOperator (w : Lp ℂ ⊤ μ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL μ ⊤ 2 2 w

theorem multiplicationOperator_coe (w : Lp ℂ ⊤ μ) (f : Lp ℂ 2 μ) :
    (multiplicationOperator w f : X → ℂ) =ᵐ[μ] fun x => w x * f x := by
  exact (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder w f

theorem integrable_weighted_l2_mul_star
    (w : Lp ℂ ⊤ μ) (f g : Lp ℂ 2 μ) :
    Integrable (fun x => w x * f x * star (g x)) μ := by
  apply (integrable_l2_mul_star (multiplicationOperator w f) g).congr
  filter_upwards [multiplicationOperator_coe w f] with x hx
  rw [hx]

theorem integral_weighted_l2_mul_star
    (w : Lp ℂ ⊤ μ) (f g : Lp ℂ 2 μ) :
    (∫ x, w x * f x * star (g x) ∂μ) =
      bookInner (multiplicationOperator w f) g := by
  rw [← integral_l2_mul_star]
  apply integral_congr_ae
  filter_upwards [multiplicationOperator_coe w f] with x hx
  rw [hx]

/-- The weighted diagonal integral of the specified finite kernel. -/
def weightedKernelIntegral (μ : Measure X) (K : X → X → ℂ) (w : X → ℂ) : ℂ :=
  ∫ x, w x * K x x ∂μ

/-- Weighted diagonal integrals require equality of the diagonals for the base measure. -/
theorem weightedKernelIntegral_congr_diagonal_ae {K L : X → X → ℂ} {w w' : X → ℂ}
    (hK : (fun x => K x x) =ᵐ[μ] (fun x => L x x)) (hw : w =ᵐ[μ] w') :
    weightedKernelIntegral μ K w = weightedKernelIntegral μ L w' := by
  apply integral_congr_ae
  filter_upwards [hK, hw] with x hx hwx
  rw [hx, hwx]

theorem integrable_weightedKernel
    (u : ι → Lp ℂ 2 μ) (A : Matrix ι ι ℂ) (w : Lp ℂ ⊤ μ) :
    Integrable (fun x => w x * finiteKernel (fun i => (u i : X → ℂ)) A x x) μ := by
  simp only [finiteKernel, Finset.mul_sum]
  apply integrable_finset_sum
  intro i _
  apply integrable_finset_sum
  intro j _
  convert (integrable_weighted_l2_mul_star w (u i) (u j)).const_mul (A i j) using 1
  funext x
  ring

theorem weightedKernelIntegral_eq_sum
    (u : ι → Lp ℂ 2 μ) (A : Matrix ι ι ℂ) (w : Lp ℂ ⊤ μ) :
    weightedKernelIntegral μ (finiteKernel (fun i => (u i : X → ℂ)) A) w =
      ∑ i, ∑ j, A i j * bookInner (multiplicationOperator w (u i)) (u j) := by
  have ht (i j : ι) : Integrable (fun x => A i j * (w x * u i x * star (u j x))) μ :=
    (integrable_weighted_l2_mul_star w (u i) (u j)).const_mul (A i j)
  have heq : (fun x => w x * finiteKernel (fun i => (u i : X → ℂ)) A x x) =
      (fun x => ∑ i, ∑ j, A i j * (w x * u i x * star (u j x))) := by
    funext x
    simp only [finiteKernel, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  unfold weightedKernelIntegral
  rw [heq, integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro j _
      rw [integral_const_mul, integral_weighted_l2_mul_star]
    · intro j _
      exact ht i j
  · intro i _
    exact integrable_finset_sum _ (fun j _ => ht i j)

/-- The weighted integral is the actual trace of the compressed endomorphism. -/
theorem weightedKernelIntegral_eq_trace
    (u : ι → Lp ℂ 2 μ) (hu : Orthonormal ℂ u) (A : Matrix ι ι ℂ) (w : Lp ℂ ⊤ μ) :
    weightedKernelIntegral μ (finiteKernel (fun i => (u i : X → ℂ)) A) w =
      LinearMap.trace ℂ (Submodule.span ℂ (Set.range u))
        (compressedFiniteOperator u A (multiplicationOperator w)) := by
  rw [weightedKernelIntegral_eq_sum, trace_compressedFiniteOperator u hu]

theorem weightedKernelIntegral_diagonal [DecidableEq ι]
    (u : ι → Lp ℂ 2 μ) (eigenvalue : ι → ℂ) (w : Lp ℂ ⊤ μ) :
    weightedKernelIntegral μ
        (finiteKernel (fun i => (u i : X → ℂ)) (Matrix.diagonal eigenvalue)) w =
      ∑ j, eigenvalue j * ∫ x, w x * u j x * star (u j x) ∂μ := by
  simp_rw [integral_weighted_l2_mul_star]
  rw [weightedKernelIntegral_eq_sum]
  simp [Matrix.diagonal_apply]

theorem weightedKernelIntegral_diagonal_norm [DecidableEq ι]
    (u : ι → Lp ℂ 2 μ) (eigenvalue : ι → ℂ) (w : Lp ℂ ⊤ μ) :
    weightedKernelIntegral μ
        (finiteKernel (fun i => (u i : X → ℂ)) (Matrix.diagonal eigenvalue)) w =
      ∑ j, eigenvalue j * ∫ x, w x * (‖u j x‖ : ℂ) ^ 2 ∂μ := by
  rw [weightedKernelIntegral_diagonal]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  rw [mul_assoc]
  congr 1
  exact RCLike.mul_conj (u j x)

end TraceFormulas
