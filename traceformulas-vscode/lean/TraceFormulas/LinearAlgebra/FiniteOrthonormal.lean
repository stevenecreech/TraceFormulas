import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Data.Matrix.Basic

/-!
# Finite orthonormal coefficients

The book uses a complex inner product linear in the first argument. Mathlib's
inner product is linear in the second, so `bookInner f g = inner ℂ g f`.
The definition merely reverses an existing inner product; it does not assume
any of the conclusions below. The finite index type may be empty. Machine
checks and the separate human correspondence review are recorded in the audit.
-/

noncomputable section

open scoped BigOperators

namespace TraceFormulas

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The book's linear-in-the-first-argument inner product. -/
def bookInner (f g : E) : ℂ := inner ℂ g f

/-- The finite orthonormal expansion; orthonormality is a theorem hypothesis. -/
def finiteProjection [Fintype ι] (u : ι → E) (f : E) : E :=
  ∑ j, bookInner f (u j) • u j

/-- The actual bounded finite-rank operator associated with a finite family and a matrix.
Its construction uses Mathlib's rank-one continuous linear maps. -/
def finiteOperator [Fintype ι] (u : ι → E) (A : Matrix ι ι ℂ) : E →L[ℂ] E :=
  ∑ i, ∑ j, (innerSL ℂ (u j)).smulRight (A i j • u i)

theorem finiteOperator_apply [Fintype ι] (u : ι → E) (A : Matrix ι ι ℂ) (f : E) :
    finiteOperator u A f = ∑ i, ∑ j, (A i j * bookInner f (u j)) • u i := by
  simp [finiteOperator, bookInner, smul_smul, mul_comm]

theorem finiteOperator_apply' [Fintype ι] (u : ι → E) (A : Matrix ι ι ℂ) (f : E) :
    finiteOperator u A f = ∑ i, (∑ j, A i j * bookInner f (u j)) • u i := by
  rw [finiteOperator_apply]
  simp only [Finset.sum_smul]

variable [Fintype ι] {u : ι → E}

theorem coefficient_of_sum (hu : Orthonormal ℂ u) (c : ι → ℂ) (j : ι) :
    bookInner (∑ i, c i • u i) (u j) = c j := by
  simpa only [bookInner] using hu.inner_right_fintype c j

/-- Coordinates in the actual basis of the span agree with the book's inner products. -/
theorem spanBasis_repr (hu : Orthonormal ℂ u)
    (v : Submodule.span ℂ (Set.range u)) (j : ι) :
    (Basis.span hu.linearIndependent).repr v j = bookInner (v : E) (u j) := by
  have hv : (∑ i, (Basis.span hu.linearIndependent).repr v i • u i) = (v : E) := by
    simpa [Basis.span_apply] using
      congrArg (fun z : Submodule.span ℂ (Set.range u) => (z : E))
        ((Basis.span hu.linearIndependent).sum_repr v)
  rw [← hv, coefficient_of_sum hu]

theorem finiteOperator_basis (hu : Orthonormal ℂ u) (A : Matrix ι ι ℂ) (j : ι) :
    finiteOperator u A (u j) = ∑ i, A i j • u i := by
  classical
  simp [finiteOperator_apply, bookInner, orthonormal_iff_ite.mp hu]

theorem finiteOperator_mem_span (u : ι → E) (A : Matrix ι ι ℂ) (f : E) :
    finiteOperator u A f ∈ Submodule.span ℂ (Set.range u) := by
  rw [finiteOperator_apply]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.sum_mem
  intro j _
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

theorem finiteOperator_range_le (u : ι → E) (A : Matrix ι ι ℂ) :
    LinearMap.range (finiteOperator u A).toLinearMap ≤ Submodule.span ℂ (Set.range u) := by
  rintro _ ⟨f, rfl⟩
  exact finiteOperator_mem_span u A f

theorem finiteOperator_eq_zero_of_mem_orthogonal (u : ι → E) (A : Matrix ι ι ℂ)
    (f : E) (hf : f ∈ (Submodule.span ℂ (Set.range u))ᗮ) :
    finiteOperator u A f = 0 := by
  have hz (j : ι) : bookInner f (u j) = 0 :=
    (Submodule.mem_orthogonal _ _).mp hf (u j) (Submodule.subset_span (Set.mem_range_self j))
  simp [finiteOperator_apply, hz]

theorem norm_finiteOperator_le (hu : Orthonormal ℂ u) (A : Matrix ι ι ℂ) (f : E) :
    ‖finiteOperator u A f‖ ≤ (∑ i, ∑ j, ‖A i j‖) * ‖f‖ := by
  rw [finiteOperator_apply]
  calc
    ‖∑ i, ∑ j, (A i j * bookInner f (u j)) • u i‖
        ≤ ∑ i, ‖∑ j, (A i j * bookInner f (u j)) • u i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖(A i j * bookInner f (u j)) • u i‖ :=
      Finset.sum_le_sum (fun i _ => norm_sum_le _ _)
    _ ≤ ∑ i, ∑ j, ‖A i j‖ * ‖f‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simp only [norm_smul, norm_mul, hu.norm_eq_one, mul_one]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa only [bookInner, hu.norm_eq_one, one_mul] using norm_inner_le_norm (u j) f
    _ = (∑ i, ∑ j, ‖A i j‖) * ‖f‖ := by simp only [Finset.sum_mul]

theorem residual_inner_eq_zero (hu : Orthonormal ℂ u) (f : E) (j : ι) :
    bookInner (f - finiteProjection u f) (u j) = 0 := by
  change inner ℂ (u j) (f - ∑ i, bookInner f (u i) • u i) = 0
  rw [inner_sub_right, hu.inner_right_fintype]
  simp only [bookInner, sub_self]

theorem residual_mem_orthogonal (hu : Orthonormal ℂ u) (f : E) :
    f - finiteProjection u f ∈ (Submodule.span ℂ (Set.range u))ᗮ := by
  apply (Submodule.mem_orthogonal _ _).2
  intro v hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
      rcases hv with ⟨j, rfl⟩
      exact residual_inner_eq_zero hu f j
  | zero => exact inner_zero_left _
  | add x y hx hy hxf hyf =>
      rw [inner_add_left, hxf, hyf, add_zero]
  | smul c x hx hxf =>
      rw [inner_smul_left, hxf, mul_zero]

theorem finite_orthonormal_decomposition (hu : Orthonormal ℂ u) (f : E) :
    ∃! r : E, r ∈ (Submodule.span ℂ (Set.range u))ᗮ ∧
      f = finiteProjection u f + r := by
  refine ⟨f - finiteProjection u f, ⟨residual_mem_orthogonal hu f, ?_⟩, ?_⟩
  · abel
  · intro r hr
    apply eq_sub_iff_add_eq.mpr
    rw [add_comm]
    exact hr.2.symm

theorem coefficients_unique (hu : Orthonormal ℂ u) (f : E)
    (c : ι → ℂ) (r : E)
    (hr : r ∈ (Submodule.span ℂ (Set.range u))ᗮ)
    (hf : f = (∑ j, c j • u j) + r) :
    c = fun j => bookInner f (u j) := by
  funext j
  have hrj : inner ℂ (u j) r = 0 :=
    (Submodule.mem_orthogonal _ _).mp hr (u j)
      (Submodule.subset_span ⟨j, rfl⟩)
  symm
  change inner ℂ (u j) f = c j
  rw [hf, inner_add_right, hu.inner_right_fintype, hrj, add_zero]

theorem finite_spectral_operator_expansion (hu : Orthonormal ℂ u)
    (T : E →ₗ[ℂ] E) (eigenvalue : ι → ℂ)
    (heigen : ∀ j, T (u j) = eigenvalue j • u j)
    (hzero : ∀ r ∈ (Submodule.span ℂ (Set.range u))ᗮ, T r = 0)
    (f : E) :
    T f = ∑ j, (eigenvalue j * bookInner f (u j)) • u j := by
  have hr := hzero (f - finiteProjection u f) (residual_mem_orthogonal hu f)
  have hf : f = finiteProjection u f + (f - finiteProjection u f) := by abel
  calc
    T f = T (finiteProjection u f + (f - finiteProjection u f)) := congrArg T hf
    _ = T (finiteProjection u f) := by rw [map_add, hr, add_zero]
    _ = ∑ j, (eigenvalue j * bookInner f (u j)) • u j := by
      simp only [finiteProjection, map_sum, map_smul, heigen, smul_smul, mul_comm]

end TraceFormulas
