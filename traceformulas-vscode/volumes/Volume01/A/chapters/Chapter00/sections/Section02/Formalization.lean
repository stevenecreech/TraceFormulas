import TraceFormulas.Analysis.SpectralKernel
import TraceFormulas.Analysis.KernelRepresentatives
import TraceFormulas.Analysis.FiniteCountingKernel
import TraceFormulas.Analysis.FiniteProjection
import TraceFormulas.Analysis.RankOneExample

/-!
# Section 0.2: orthonormal families, kernels, and genuine operator traces

The section uses Mathlib's complex L² space, Bochner integral, continuous linear
maps, orthogonal complements, and endomorphism trace. The supporting-space
trace is proved equal to the canonical trace on the actual operator range.
The book's linear-first convention is `bookInner f g = inner ℂ g f`.
Fin N includes N=0. Representative changes have explicit almost-everywhere
bridges; no diagonal equality is inferred from product-a.e. kernel equality.
Human correspondence review remains pending independently of machine checks.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace TraceFormulas.Volume01.A.Chapter00.Section02

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem finite_orthonormal_coefficients {N : ℕ}
    (u : Fin N → Lp ℂ 2 μ) (hu : Orthonormal ℂ u) (f : Lp ℂ 2 μ) :
    ∃! r : Lp ℂ 2 μ, r ∈ (Submodule.span ℂ (Set.range u))ᗮ ∧
      f = (∑ j, bookInner f (u j) • u j) + r := by
  simpa only [finiteProjection] using finite_orthonormal_decomposition hu f

theorem uniqueness_of_coefficients {N : ℕ}
    (u : Fin N → Lp ℂ 2 μ) (hu : Orthonormal ℂ u) (f : Lp ℂ 2 μ)
    (c : Fin N → ℂ) (r : Lp ℂ 2 μ)
    (hr : r ∈ (Submodule.span ℂ (Set.range u))ᗮ)
    (hf : f = (∑ j, c j • u j) + r) :
    c = fun j => bookInner f (u j) := coefficients_unique hu f c r hr hf

theorem spectral_operator_formula {N : ℕ}
    (u : Fin N → Lp ℂ 2 μ) (hu : Orthonormal ℂ u)
    (T : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) (eigenvalue : Fin N → ℂ)
    (heigen : ∀ j, T (u j) = eigenvalue j • u j)
    (hzero : ∀ r ∈ (Submodule.span ℂ (Set.range u))ᗮ, T r = 0)
    (f : Lp ℂ 2 μ) :
    T f = ∑ j, (eigenvalue j * bookInner f (u j)) • u j :=
  finite_spectral_operator_expansion hu T eigenvalue heigen hzero f

theorem spectral_operator_bound {N : ℕ}
    (u : Fin N → Lp ℂ 2 μ) (hu : Orthonormal ℂ u)
    (T : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) (eigenvalue : Fin N → ℂ)
    (heigen : ∀ j, T (u j) = eigenvalue j • u j)
    (hzero : ∀ r ∈ (Submodule.span ℂ (Set.range u))ᗮ, T r = 0)
    (f : Lp ℂ 2 μ) :
    ‖T f‖ ≤ (∑ j, ‖eigenvalue j‖) * ‖f‖ :=
  norm_spectral_operator_le u hu T eigenvalue heigen hzero f

theorem spectral_kernel_representation {N : ℕ}
    (u : Fin N → Lp ℂ 2 μ) (hu : Orthonormal ℂ u)
    (T : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) (eigenvalue : Fin N → ℂ)
    (heigen : ∀ j, T (u j) = eigenvalue j • u j)
    (hzero : ∀ r ∈ (Submodule.span ℂ (Set.range u))ᗮ, T r = 0)
    (f : Lp ℂ 2 μ) :
    (fun x => T f x) =ᵐ[μ]
      fun x => ∫ y, spectralKernel (fun i => (u i : X → ℂ)) eigenvalue x y * f y ∂μ :=
  spectral_operator_eq_integral_ae u hu T eigenvalue heigen hzero f

theorem supporting_space_trace_independent
    (S : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ)
    (W W' : Submodule ℂ (Lp ℂ 2 μ)) [FiniteDimensional ℂ W] [FiniteDimensional ℂ W']
    (h : LinearMap.range S ≤ W) (h' : LinearMap.range S ≤ W') :
    LinearMap.trace ℂ W (supportedEndomorphism S W h) =
      LinearMap.trace ℂ W' (supportedEndomorphism S W' h') :=
  supported_trace_independent S W W' h h'

theorem spectral_trace_identity {N : ℕ}
    (u : Fin N → Lp ℂ 2 μ) (hu : Orthonormal ℂ u)
    (T : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) (eigenvalue : Fin N → ℂ)
    (heigen : ∀ j, T (u j) = eigenvalue j • u j)
    (hzero : ∀ r ∈ (Submodule.span ℂ (Set.range u))ᗮ, T r = 0) :
    (∫ x, spectralKernel (fun i => (u i : X → ℂ)) eigenvalue x x ∂μ) =
      finiteRankTrace T ∧ finiteRankTrace T = ∑ j, eigenvalue j :=
  spectral_kernel_trace_identity u hu T eigenvalue heigen hzero

theorem finite_kernel_representation {N : ℕ}
    (u : Fin N → Lp ℂ 2 μ) (A : Matrix (Fin N) (Fin N) ℂ) (f : Lp ℂ 2 μ) :
    (fun x => finiteOperator u A f x) =ᵐ[μ]
      fun x => ∫ y, finiteKernel (fun i => (u i : X → ℂ)) A x y * f y ∂μ :=
  finiteOperator_eq_integral_ae u A f

theorem finite_kernel_representation_chosen_representatives {N : ℕ}
    (u : Fin N → Lp ℂ 2 μ) (v : Fin N → X → ℂ)
    (hv : ∀ i, (u i : X → ℂ) =ᵐ[μ] v i)
    (A : Matrix (Fin N) (Fin N) ℂ) (f : Lp ℂ 2 μ) :
    (fun x => finiteOperator u A f x) =ᵐ[μ]
      fun x => ∫ y, finiteKernel v A x y * f y ∂μ :=
  (finiteOperator_eq_integral_ae u A f).trans
    (finiteKernel_operator_ae_congr A (fun i => (u i : X → ℂ)) v hv f)

theorem finite_operator_bound {N : ℕ}
    (u : Fin N → Lp ℂ 2 μ) (hu : Orthonormal ℂ u)
    (A : Matrix (Fin N) (Fin N) ℂ) (f : Lp ℂ 2 μ) :
    ‖finiteOperator u A f‖ ≤ (∑ i, ∑ j, ‖A i j‖) * ‖f‖ :=
  norm_finiteOperator_le hu A f

theorem finite_operator_support {N : ℕ}
    (u : Fin N → Lp ℂ 2 μ) (A : Matrix (Fin N) (Fin N) ℂ) :
    LinearMap.range (finiteOperator u A).toLinearMap ≤ Submodule.span ℂ (Set.range u) ∧
    ∀ f ∈ (Submodule.span ℂ (Set.range u))ᗮ, finiteOperator u A f = 0 :=
  ⟨finiteOperator_range_le u A, fun f hf => finiteOperator_eq_zero_of_mem_orthogonal u A f hf⟩

theorem finite_operator_basis_action {N : ℕ}
    (u : Fin N → Lp ℂ 2 μ) (hu : Orthonormal ℂ u)
    (A : Matrix (Fin N) (Fin N) ℂ) (j : Fin N) :
    finiteOperator u A (u j) = ∑ i, A i j • u i := finiteOperator_basis hu A j

theorem finite_kernel_diagonal_integrable {N : ℕ}
    (u : Fin N → Lp ℂ 2 μ) (A : Matrix (Fin N) (Fin N) ℂ) :
    Integrable (fun x => finiteKernel (fun i => (u i : X → ℂ)) A x x) μ :=
  integrable_finiteKernel_diagonal u A

theorem finite_kernel_diagonal_integrable_chosen_representatives {N : ℕ}
    (u : Fin N → Lp ℂ 2 μ) (v : Fin N → X → ℂ)
    (hv : ∀ i, (u i : X → ℂ) =ᵐ[μ] v i)
    (A : Matrix (Fin N) (Fin N) ℂ) :
    Integrable (fun x => finiteKernel v A x x) μ :=
  (integrable_finiteKernel_diagonal u A).congr
    (finiteKernel_diagonal_ae_congr A (fun i => (u i : X → ℂ)) v hv)

theorem finite_kernel_trace_identity {N : ℕ}
    (u : Fin N → Lp ℂ 2 μ) (hu : Orthonormal ℂ u)
    (A : Matrix (Fin N) (Fin N) ℂ) :
    (∫ x, finiteKernel (fun i => (u i : X → ℂ)) A x x ∂μ) =
      finiteRankTrace (finiteOperator u A).toLinearMap ∧
    finiteRankTrace (finiteOperator u A).toLinearMap = A.charpoly.roots.sum :=
  TraceFormulas.finiteKernel_trace_identity u hu A

theorem trace_identity_chosen_representatives {N : ℕ}
    (u : Fin N → Lp ℂ 2 μ) (hu : Orthonormal ℂ u)
    (v : Fin N → X → ℂ) (hv : ∀ i, (u i : X → ℂ) =ᵐ[μ] v i)
    (A : Matrix (Fin N) (Fin N) ℂ) :
    (∫ x, finiteKernel v A x x ∂μ) = finiteRankTrace (finiteOperator u A).toLinearMap := by
  rw [← finiteKernel_diagonal_integral_congr A (fun i => (u i : X → ℂ)) v hv]
  exact integral_finiteKernel_eq_operator_trace u hu A

theorem representative_diagonal_independence {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℂ) (u v : Fin N → X → ℂ)
    (h : ∀ i, u i =ᵐ[μ] v i) :
    (fun x => finiteKernel u A x x) =ᵐ[μ] (fun x => finiteKernel v A x x) :=
  finiteKernel_diagonal_ae_congr A u v h

theorem identity_matrix_projection {N : ℕ}
    (u : Fin N → Lp ℂ 2 μ) (hu : Orthonormal ℂ u) (f : Lp ℂ 2 μ) :
    finiteOperator u (1 : Matrix (Fin N) (Fin N) ℂ) f =
      (finiteSpanProjection u f : Lp ℂ 2 μ) :=
  finiteOperator_identity_eq_projection u hu f

theorem projection_trace {N : ℕ}
    (u : Fin N → Lp ℂ 2 μ) (hu : Orthonormal ℂ u) :
    finiteRankTrace (finiteOperator u (1 : Matrix (Fin N) (Fin N) ℂ)).toLinearMap = (N : ℂ) := by
  simpa using finiteRankTrace_identity_operator u hu

theorem point_indicator_kernel {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (x y : Fin N) :
    finiteKernel (fun i => Pi.single i (1 : ℂ)) A x y = A x y :=
  finiteKernel_pointIndicators A x y

theorem rank_one_normalization : ‖rankOneLp‖ = 1 := rankOneLp_norm

theorem rank_one_eigenvector (α : ℂ) : rankOneOperator α rankOneLp = α • rankOneLp :=
  rankOneOperator_eigen α

theorem rank_one_zero_orthogonal (α : ℂ) (f : Lp ℂ 2 unitIntervalMeasure)
    (hf : f ∈ (Submodule.span ℂ (Set.range rankOneFamily))ᗮ) :
    rankOneOperator α f = 0 := rankOneOperator_zero_orthogonal α f hf

theorem rank_one_kernel (α : ℂ) (x y : ℝ) :
    finiteKernel (fun _ : Fin 1 => rankOneFunction) (fun _ _ => α) x y =
      3 * α * (x : ℂ) * (y : ℂ) := rankOne_kernel_formula α x y

theorem rank_one_operator_integral (α : ℂ) (f : Lp ℂ 2 unitIntervalMeasure) :
    (fun x => rankOneOperator α f x) =ᵐ[unitIntervalMeasure]
      fun x => 3 * α * (x : ℂ) * (∫ y : ℝ, (y : ℂ) * f y ∂unitIntervalMeasure) :=
  rankOneOperator_integral α f

theorem rank_one_trace_identity (α : ℂ) :
    (∫ x : ℝ, 3 * α * (x : ℂ) * (x : ℂ) ∂unitIntervalMeasure) =
      finiteRankTrace (rankOneOperator α).toLinearMap ∧
    finiteRankTrace (rankOneOperator α).toLinearMap = α :=
  ⟨rankOne_trace_identity α, rankOneOperator_trace α⟩

theorem diagonal_counterexample :
    (fun z : ℝ × ℝ => diagonalIndicator z.1 z.2) =ᵐ[
      unitIntervalMeasure.prod unitIntervalMeasure] 0 ∧
    (∀ (f : ℝ → ℂ) (x : ℝ), ∫ y, diagonalIndicator x y * f y ∂unitIntervalMeasure = 0) ∧
    (∫ x, diagonalIndicator x x ∂unitIntervalMeasure) = 1 ∧
    (∫ _x : ℝ, (0 : ℂ) ∂unitIntervalMeasure) = 0 :=
  ⟨diagonalIndicator_product_ae_zero, diagonalIndicator_zero_operator,
    diagonalIndicator_diagonal_integral, zero_kernel_diagonal_integral⟩

end TraceFormulas.Volume01.A.Chapter00.Section02
