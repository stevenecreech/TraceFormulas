import TraceFormulas.Analysis.FiniteKernelTrace
import Mathlib.Analysis.InnerProductSpace.Projection

/-! # The identity matrix gives the actual orthogonal projection -/

noncomputable section
open scoped BigOperators

namespace TraceFormulas

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Fintype ι]

def finiteSpanProjection (u : ι → E) : E →L[ℂ] Submodule.span ℂ (Set.range u) := by
  letI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range u)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range u)
  exact (Submodule.span ℂ (Set.range u)).orthogonalProjection

theorem finiteOperator_identity [DecidableEq ι] (u : ι → E) (f : E) :
    finiteOperator u (1 : Matrix ι ι ℂ) f = finiteProjection u f := by
  simp [finiteOperator_apply, finiteProjection, Matrix.one_apply]

theorem finiteOperator_identity_eq_projection [DecidableEq ι]
    (u : ι → E) (hu : Orthonormal ℂ u) (f : E) :
    finiteOperator u (1 : Matrix ι ι ℂ) f = (finiteSpanProjection u f : E) := by
  let V := Submodule.span ℂ (Set.range u)
  letI : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ (Set.finite_range u)
  change finiteOperator u (1 : Matrix ι ι ℂ) f = (V.orthogonalProjection f : E)
  symm
  apply Submodule.eq_orthogonalProjection_of_mem_orthogonal
  · exact finiteOperator_mem_span u 1 f
  · rw [finiteOperator_identity]
    exact residual_mem_orthogonal hu f

theorem finiteRankTrace_identity_operator [DecidableEq ι]
    (u : ι → E) (hu : Orthonormal ℂ u) :
    finiteRankTrace (finiteOperator u (1 : Matrix ι ι ℂ)).toLinearMap =
      (Fintype.card ι : ℂ) := by
  rw [finiteRankTrace_finiteOperator hu]
  simp

end TraceFormulas
