import TraceFormulas.Analysis.FiniteKernelTrace

/-!
# Spectral specialization of the finite kernel

The diagonal construction is linked to the same arbitrary linear operator
whose action on an orthonormal eigenfamily and orthogonal complement is given
in the manuscript. No boundedness hypothesis on that operator is assumed;
boundedness follows from the finite expansion.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace TraceFormulas

variable {X ι : Type*} [Fintype ι]

def spectralKernel (u : ι → X → ℂ) (eigenvalue : ι → ℂ) (x y : X) : ℂ :=
  ∑ j, eigenvalue j * u j x * star (u j y)

theorem finiteKernel_diagonal (u : ι → X → ℂ) (eigenvalue : ι → ℂ) (x y : X)
    [DecidableEq ι] :
    finiteKernel u (Matrix.diagonal eigenvalue) x y = spectralKernel u eigenvalue x y := by
  simp [finiteKernel, spectralKernel, Matrix.diagonal]

variable [MeasurableSpace X] {μ : Measure X}

theorem integrable_spectralKernel_mul (u : ι → Lp ℂ 2 μ)
    (eigenvalue : ι → ℂ) (f : Lp ℂ 2 μ) (x : X) :
    Integrable (fun y => spectralKernel (fun i => (u i : X → ℂ)) eigenvalue x y * f y) μ := by
  classical
  simpa only [finiteKernel_diagonal] using
    integrable_finiteKernel_mul u (Matrix.diagonal eigenvalue) f x

theorem spectral_operator_eq_integral_ae (u : ι → Lp ℂ 2 μ) (hu : Orthonormal ℂ u)
    (T : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) (eigenvalue : ι → ℂ)
    (heigen : ∀ j, T (u j) = eigenvalue j • u j)
    (hzero : ∀ r ∈ (Submodule.span ℂ (Set.range u))ᗮ, T r = 0)
    (f : Lp ℂ 2 μ) :
    (fun x => T f x) =ᵐ[μ]
      fun x => ∫ y, spectralKernel (fun i => (u i : X → ℂ)) eigenvalue x y * f y ∂μ := by
  classical
  rw [finite_spectral_operator_eq_diagonal hu T eigenvalue heigen hzero]
  simpa only [finiteKernel_diagonal, ContinuousLinearMap.coe_coe] using
    finiteOperator_eq_integral_ae u (Matrix.diagonal eigenvalue) f

theorem norm_spectral_operator_le (u : ι → Lp ℂ 2 μ) (hu : Orthonormal ℂ u)
    (T : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) (eigenvalue : ι → ℂ)
    (heigen : ∀ j, T (u j) = eigenvalue j • u j)
    (hzero : ∀ r ∈ (Submodule.span ℂ (Set.range u))ᗮ, T r = 0)
    (f : Lp ℂ 2 μ) :
    ‖T f‖ ≤ (∑ j, ‖eigenvalue j‖) * ‖f‖ := by
  classical
  rw [finite_spectral_operator_eq_diagonal hu T eigenvalue heigen hzero]
  simpa [Matrix.diagonal, apply_ite] using norm_finiteOperator_le hu (Matrix.diagonal eigenvalue) f

theorem integrable_spectralKernel_diagonal (u : ι → Lp ℂ 2 μ) (eigenvalue : ι → ℂ) :
    Integrable (fun x => spectralKernel (fun i => (u i : X → ℂ)) eigenvalue x x) μ := by
  classical
  simpa only [finiteKernel_diagonal] using
    integrable_finiteKernel_diagonal u (Matrix.diagonal eigenvalue)

theorem spectral_kernel_trace_identity (u : ι → Lp ℂ 2 μ) (hu : Orthonormal ℂ u)
    (T : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) (eigenvalue : ι → ℂ)
    (heigen : ∀ j, T (u j) = eigenvalue j • u j)
    (hzero : ∀ r ∈ (Submodule.span ℂ (Set.range u))ᗮ, T r = 0) :
    (∫ x, spectralKernel (fun i => (u i : X → ℂ)) eigenvalue x x ∂μ) =
      finiteRankTrace T ∧ finiteRankTrace T = ∑ j, eigenvalue j := by
  classical
  constructor
  · rw [finite_spectral_operator_eq_diagonal hu T eigenvalue heigen hzero]
    simpa only [finiteKernel_diagonal] using
      integral_finiteKernel_eq_operator_trace u hu (Matrix.diagonal eigenvalue)
  · exact finiteRankTrace_spectral_operator hu T eigenvalue heigen hzero

end TraceFormulas
