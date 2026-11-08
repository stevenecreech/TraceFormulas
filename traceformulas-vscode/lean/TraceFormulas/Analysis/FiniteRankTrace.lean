import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Trace of an operator with finite-dimensional range

The trace is defined using Mathlib's trace of the induced endomorphism of the
actual range. A comparison theorem identifies it with the trace on every
finite-dimensional subspace containing that range. This is a canonical form
of the manuscript's definition using a supporting subspace.

Build and dependency-axiom evidence are recorded in the chapter audit.
Steven's review of mathematical correspondence is recorded separately.
-/

noncomputable section

namespace TraceFormulas

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- Restrict a range-supported linear map to its supporting subspace. -/
def supportedEndomorphism (S : E →ₗ[ℂ] E) (W : Submodule ℂ E)
    (h : LinearMap.range S ≤ W) : W →ₗ[ℂ] W :=
  (S.codRestrict W (fun x => h (LinearMap.mem_range_self S x))).comp W.subtype

/-- Trace on the actual range. Its finite-rank interpretation is asserted only
under the finite-dimensional hypotheses of the theorems below. -/
def finiteRankTrace (S : E →ₗ[ℂ] E) : ℂ :=
  LinearMap.trace ℂ (LinearMap.range S) (S.rangeRestrict.comp (LinearMap.range S).subtype)

theorem finiteRankTrace_eq_supported_trace (S : E →ₗ[ℂ] E)
    (W : Submodule ℂ E) [FiniteDimensional ℂ W] (h : LinearMap.range S ≤ W) :
    finiteRankTrace S = LinearMap.trace ℂ W (supportedEndomorphism S W h) := by
  letI : FiniteDimensional ℂ (LinearMap.range S) := Submodule.finiteDimensional_of_le h
  let f : W →ₗ[ℂ] LinearMap.range S := S.rangeRestrict.comp W.subtype
  let g : LinearMap.range S →ₗ[ℂ] W := Submodule.inclusion h
  change LinearMap.trace ℂ (LinearMap.range S) (f.comp g) =
    LinearMap.trace ℂ W (g.comp f)
  exact (LinearMap.trace_comp_comm' f g).symm

/-- The supporting space does not affect the trace. No choice of basis is built
into either side: both are Mathlib endomorphism traces. -/
theorem supported_trace_independent (S : E →ₗ[ℂ] E)
    (W W' : Submodule ℂ E) [FiniteDimensional ℂ W] [FiniteDimensional ℂ W']
    (h : LinearMap.range S ≤ W) (h' : LinearMap.range S ≤ W') :
    LinearMap.trace ℂ W (supportedEndomorphism S W h) =
      LinearMap.trace ℂ W' (supportedEndomorphism S W' h') := by
  rw [← finiteRankTrace_eq_supported_trace S W h,
    ← finiteRankTrace_eq_supported_trace S W' h']

end TraceFormulas
