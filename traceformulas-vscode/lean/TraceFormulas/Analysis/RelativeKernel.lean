import TraceFormulas.Analysis.FiniteKernel
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Relative pairings of finite kernels

These definitions use the actual iterated Lebesgue integral and Mathlib L²
classes. The finite separated-variable calculation is accompanied by an
integrability theorem on the product measure, not an assumed convergence fact.
Compilation and axiom evidence are recorded separately in the chapter audit.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace TraceFormulas

variable {X ι : Type*} [MeasurableSpace X] {μ : Measure X} [Fintype ι]

/-- Integrate a kernel against an input `q` and an output test `p`. -/
def relativeKernelPairing (μ : Measure X) (K : X → X → ℂ) (p q : X → ℂ) : ℂ :=
  ∫ x, ∫ y, K x y * q y * star (p x) ∂μ ∂μ

private theorem relative_integrand_eq
    (u : ι → Lp ℂ 2 μ) (A : Matrix ι ι ℂ) (p q : Lp ℂ 2 μ) :
    (fun z : X × X => finiteKernel (fun i => (u i : X → ℂ)) A z.1 z.2 *
      q z.2 * star (p z.1)) =
    (fun z => ∑ i, ∑ j, A i j *
      ((u i z.1 * star (p z.1)) * (q z.2 * star (u j z.2)))) := by
  funext z
  simp only [finiteKernel, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [Fintype ι] in
theorem integrable_relativeKernel_term
    (u : ι → Lp ℂ 2 μ) (A : Matrix ι ι ℂ) (p q : Lp ℂ 2 μ) (i j : ι) :
    Integrable (fun z : X × X => A i j *
      ((u i z.1 * star (p z.1)) * (q z.2 * star (u j z.2)))) (μ.prod μ) :=
  ((integrable_l2_mul_star (u i) p).mul_prod
    (integrable_l2_mul_star q (u j))).const_mul (A i j)

/-- Absolute convergence of the relative kernel integrand on the product space. -/
theorem integrable_relativeKernel
    (u : ι → Lp ℂ 2 μ) (A : Matrix ι ι ℂ) (p q : Lp ℂ 2 μ) :
    Integrable (fun z : X × X => finiteKernel (fun i => (u i : X → ℂ)) A z.1 z.2 *
      q z.2 * star (p z.1)) (μ.prod μ) := by
  rw [relative_integrand_eq]
  apply integrable_finset_sum
  intro i _
  apply integrable_finset_sum
  intro j _
  exact integrable_relativeKernel_term u A p q i j

variable [SigmaFinite μ]

/-- Product-almost-everywhere kernel equality suffices for a relative pairing. -/
theorem relativeKernelPairing_congr_ae {K L : X → X → ℂ} {p p' q q' : X → ℂ}
    (hK : (fun z : X × X => K z.1 z.2) =ᵐ[μ.prod μ] (fun z => L z.1 z.2))
    (hp : p =ᵐ[μ] p') (hq : q =ᵐ[μ] q') :
    relativeKernelPairing μ K p q = relativeKernelPairing μ L p' q' := by
  unfold relativeKernelPairing
  apply integral_congr_ae
  filter_upwards [Measure.ae_ae_of_ae_prod hK, hp] with x hx hpx
  apply integral_congr_ae
  filter_upwards [hx, hq] with y hxy hqy
  rw [hxy, hpx, hqy]

theorem relativeKernelPairing_eq_sum
    (u : ι → Lp ℂ 2 μ) (A : Matrix ι ι ℂ) (p q : Lp ℂ 2 μ) :
    relativeKernelPairing μ (finiteKernel (fun i => (u i : X → ℂ)) A) p q =
      ∑ i, ∑ j, A i j * bookInner (u i) p * bookInner q (u j) := by
  unfold relativeKernelPairing
  rw [← integral_prod _ (integrable_relativeKernel u A p q), relative_integrand_eq]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro j _
      rw [integral_const_mul,
        integral_prod_mul (fun x => u i x * star (p x))
          (fun y => q y * star (u j y)),
        integral_l2_mul_star, integral_l2_mul_star]
      exact (mul_assoc _ _ _).symm
    · intro j _
      exact integrable_relativeKernel_term u A p q i j
  · intro i _
    exact integrable_finset_sum _ (fun j _ => integrable_relativeKernel_term u A p q i j)

/-- The relative integral is the genuine Hilbert-space operator coefficient. -/
theorem relativeKernelPairing_eq_operator
    (u : ι → Lp ℂ 2 μ) (A : Matrix ι ι ℂ) (p q : Lp ℂ 2 μ) :
    relativeKernelPairing μ (finiteKernel (fun i => (u i : X → ℂ)) A) p q =
      bookInner (finiteOperator u A q) p := by
  rw [relativeKernelPairing_eq_sum, finiteOperator_apply]
  simp only [bookInner, inner_sum, inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The period form, with conjugation matching the manuscript convention. -/
theorem relativeKernelPairing_eq_periods
    (u : ι → Lp ℂ 2 μ) (A : Matrix ι ι ℂ) (p q : Lp ℂ 2 μ) :
    relativeKernelPairing μ (finiteKernel (fun i => (u i : X → ℂ)) A) p q =
      ∑ i, ∑ j, A i j * bookInner (u i) p * star (bookInner (u j) q) := by
  rw [relativeKernelPairing_eq_sum]
  simp only [bookInner, ← starRingEnd_apply, inner_conj_symm]

/-- The relative corollary for a diagonal coefficient matrix. -/
theorem relativeKernelPairing_diagonal [DecidableEq ι]
    (u : ι → Lp ℂ 2 μ) (eigenvalue : ι → ℂ) (p q : Lp ℂ 2 μ) :
    relativeKernelPairing μ
        (finiteKernel (fun i => (u i : X → ℂ)) (Matrix.diagonal eigenvalue)) p q =
      ∑ j, eigenvalue j * bookInner (u j) p * star (bookInner (u j) q) := by
  rw [relativeKernelPairing_eq_periods]
  simp [Matrix.diagonal_apply]

end TraceFormulas
