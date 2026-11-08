import TraceFormulas.LinearAlgebra.FiniteOrthonormal
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Finite kernels on a measure space

These statements use actual Mathlib L² equivalence classes, Lebesgue integrals,
and continuous linear operators. Machine evidence is recorded in the chapter audit.
The kernel itself is defined on chosen pointwise representatives; equality of
its diagonal will be treated separately from equality for product measure.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace TraceFormulas

variable {X ι : Type*} [Fintype ι]

/-- The finite kernel formula on a specified family of pointwise representatives. -/
def finiteKernel (u : ι → X → ℂ) (A : Matrix ι ι ℂ) (x y : X) : ℂ :=
  ∑ i, ∑ j, A i j * u i x * star (u j y)

variable [MeasurableSpace X] {μ : Measure X}

/-- Products of two genuine L² representatives are integrable. -/
theorem integrable_l2_mul_star (f g : Lp ℂ 2 μ) :
    Integrable (fun x => f x * star (g x)) μ := by
  simpa only [RCLike.inner_apply, Complex.star_def] using
    (L2.integrable_inner (𝕜 := ℂ) g f)

/-- The coefficient integral uses the book's linear-in-the-first-argument convention. -/
theorem integral_l2_mul_star (f g : Lp ℂ 2 μ) :
    (∫ x, f x * star (g x) ∂μ) = bookInner f g := by
  simp only [bookInner, L2.inner_def, RCLike.inner_apply, Complex.star_def]

omit [MeasurableSpace X] in
theorem finiteKernel_mul_eq (u : ι → X → ℂ) (A : Matrix ι ι ℂ)
    (f : X → ℂ) (x y : X) :
    finiteKernel u A x y * f y =
      ∑ i, ∑ j, (A i j * u i x) * (f y * star (u j y)) := by
  simp only [finiteKernel, Finset.sum_mul]
  simp only [mul_assoc, mul_comm, mul_left_comm]

theorem integrable_finiteKernel_mul (u : ι → Lp ℂ 2 μ)
    (A : Matrix ι ι ℂ) (f : Lp ℂ 2 μ) (x : X) :
    Integrable (fun y => finiteKernel (fun i => (u i : X → ℂ)) A x y * f y) μ := by
  simp_rw [finiteKernel_mul_eq]
  apply integrable_finset_sum
  intro i _
  apply integrable_finset_sum
  intro j _
  exact (integrable_l2_mul_star f (u j)).const_mul (A i j * u i x)

theorem integral_finiteKernel_mul (u : ι → Lp ℂ 2 μ)
    (A : Matrix ι ι ℂ) (f : Lp ℂ 2 μ) (x : X) :
    (∫ y, finiteKernel (fun i => (u i : X → ℂ)) A x y * f y ∂μ) =
      ∑ i, ∑ j, (A i j * bookInner f (u j)) * u i x := by
  simp_rw [finiteKernel_mul_eq]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro j _
      rw [integral_const_mul, integral_l2_mul_star]
      simp only [mul_assoc, mul_comm, mul_left_comm]
    · intro j _
      exact (integrable_l2_mul_star f (u j)).const_mul (A i j * u i x)
  · intro i _
    exact integrable_finset_sum _ (fun j _ =>
      (integrable_l2_mul_star f (u j)).const_mul (A i j * u i x))

theorem coeFn_l2_finset_sum {η : Type*} (s : Finset η) (f : η → Lp ℂ 2 μ) :
    (fun x => (∑ i ∈ s, f i : Lp ℂ 2 μ) x) =ᵐ[μ] fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Lp.coeFn_zero ℂ 2 μ)
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      filter_upwards [Lp.coeFn_add (f i) (∑ j ∈ s, f j), ih] with x hadd hsum
      simpa only [Pi.add_apply, hsum] using hadd

theorem coeFn_l2_sum_smul (u : ι → Lp ℂ 2 μ) (c : ι → ℂ) :
    (fun x => (∑ i, c i • u i : Lp ℂ 2 μ) x) =ᵐ[μ] fun x => ∑ i, c i * u i x := by
  filter_upwards [coeFn_l2_finset_sum Finset.univ (fun i => c i • u i),
    ae_all_iff.mpr (fun i => Lp.coeFn_smul (c i) (u i))] with x hsum hsmul
  simpa only [hsmul, Pi.smul_apply, smul_eq_mul] using hsum

theorem coeFn_finiteOperator (u : ι → Lp ℂ 2 μ) (A : Matrix ι ι ℂ) (f : Lp ℂ 2 μ) :
    (fun x => finiteOperator u A f x) =ᵐ[μ]
      fun x => ∑ i, ∑ j, (A i j * bookInner f (u j)) * u i x := by
  rw [finiteOperator_apply']
  filter_upwards [coeFn_l2_sum_smul u (fun i => ∑ j, A i j * bookInner f (u j))] with x hx
  simpa only [Finset.sum_mul] using hx

/-- The operator's L² representative equals the actual kernel integral almost everywhere. -/
theorem finiteOperator_eq_integral_ae (u : ι → Lp ℂ 2 μ)
    (A : Matrix ι ι ℂ) (f : Lp ℂ 2 μ) :
    (fun x => finiteOperator u A f x) =ᵐ[μ]
      fun x => ∫ y, finiteKernel (fun i => (u i : X → ℂ)) A x y * f y ∂μ := by
  filter_upwards [coeFn_finiteOperator u A f] with x hx
  rw [hx, integral_finiteKernel_mul]

omit [Fintype ι] in
/-- Each summand of the specified diagonal is integrable. -/
theorem integrable_finiteKernel_diagonal_term
    (u : ι → Lp ℂ 2 μ) (A : Matrix ι ι ℂ) (i j : ι) :
    Integrable (fun x => A i j * u i x * star (u j x)) μ := by
  simpa only [mul_assoc] using (integrable_l2_mul_star (u i) (u j)).const_mul (A i j)

theorem integrable_finiteKernel_diagonal
    (u : ι → Lp ℂ 2 μ) (A : Matrix ι ι ℂ) :
    Integrable (fun x => finiteKernel (fun i => (u i : X → ℂ)) A x x) μ := by
  apply integrable_finset_sum
  intro i _
  apply integrable_finset_sum
  intro j _
  exact integrable_finiteKernel_diagonal_term u A i j

theorem integral_finiteKernel_diagonal
    (u : ι → Lp ℂ 2 μ) (A : Matrix ι ι ℂ) :
    (∫ x, finiteKernel (fun i => (u i : X → ℂ)) A x x ∂μ) =
      ∑ i, ∑ j, A i j * bookInner (u i) (u j) := by
  unfold finiteKernel
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro j _
      simp only [mul_assoc, integral_const_mul, integral_l2_mul_star]
    · intro j _
      exact integrable_finiteKernel_diagonal_term u A i j
  · intro i _
    exact integrable_finset_sum _ (fun j _ => integrable_finiteKernel_diagonal_term u A i j)

theorem integral_finiteKernel_diagonal_eq_matrix_trace
    (u : ι → Lp ℂ 2 μ) (hu : Orthonormal ℂ u) (A : Matrix ι ι ℂ) :
    (∫ x, finiteKernel (fun i => (u i : X → ℂ)) A x x ∂μ) = Matrix.trace A := by
  classical
  rw [integral_finiteKernel_diagonal]
  simp [bookInner, orthonormal_iff_ite.mp hu, Matrix.trace, Matrix.diag_apply]

end TraceFormulas
