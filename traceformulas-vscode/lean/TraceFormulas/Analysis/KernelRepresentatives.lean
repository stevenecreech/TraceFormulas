import TraceFormulas.Analysis.FiniteKernel
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Representatives and diagonal integrals

Changes induced from the finitely many one-variable representatives preserve
the diagonal almost everywhere. The final results give the actual Lebesgue
counterexample on [0,1], showing why arbitrary product-null changes do not.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace TraceFormulas

variable {X ι : Type*} [MeasurableSpace X] [Fintype ι] {μ : Measure X}

theorem finiteKernel_diagonal_ae_congr (A : Matrix ι ι ℂ)
    (u v : ι → X → ℂ) (h : ∀ i, u i =ᵐ[μ] v i) :
    (fun x => finiteKernel u A x x) =ᵐ[μ] (fun x => finiteKernel v A x x) := by
  have hall : ∀ᵐ x ∂μ, ∀ i, u i x = v i x := (ae_all_iff).2 h
  filter_upwards [hall] with x hx
  simp only [finiteKernel, hx]

theorem finiteKernel_diagonal_integral_congr (A : Matrix ι ι ℂ)
    (u v : ι → X → ℂ) (h : ∀ i, u i =ᵐ[μ] v i) :
    (∫ x, finiteKernel u A x x ∂μ) = ∫ x, finiteKernel v A x x ∂μ :=
  integral_congr_ae (finiteKernel_diagonal_ae_congr A u v h)

theorem finiteKernel_product_ae_congr (A : Matrix ι ι ℂ)
    (u v : ι → X → ℂ) (h : ∀ i, u i =ᵐ[μ] v i) :
    (fun z : X × X => finiteKernel u A z.1 z.2) =ᵐ[μ.prod μ]
      (fun z : X × X => finiteKernel v A z.1 z.2) := by
  have hall : ∀ᵐ x ∂μ, ∀ i, u i x = v i x := (ae_all_iff).2 h
  have hf := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae hall
  have hs := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae hall
  filter_upwards [hf, hs] with z hz₁ hz₂
  simp only [finiteKernel, hz₁, hz₂]

/-- Rebuilding from a.e.-equal one-variable representatives preserves the
integral operator a.e., as well as the stronger diagonal conclusion above. -/
theorem finiteKernel_operator_ae_congr (A : Matrix ι ι ℂ)
    (u v : ι → X → ℂ) (h : ∀ i, u i =ᵐ[μ] v i) (f : X → ℂ) :
    (fun x => ∫ y, finiteKernel u A x y * f y ∂μ) =ᵐ[μ]
      (fun x => ∫ y, finiteKernel v A x y * f y ∂μ) := by
  have hall : ∀ᵐ x ∂μ, ∀ i, u i x = v i x := (ae_all_iff).2 h
  filter_upwards [hall] with x hx
  apply integral_congr_ae
  filter_upwards [hall] with y hy
  simp only [finiteKernel, hx, hy]

/-- Arbitrary product-a.e. kernel changes preserve row integrals a.e.; they
need not preserve the diagonal integral. -/
theorem kernel_operator_ae_congr [SigmaFinite μ] (K L : X → X → ℂ)
    (h : (fun z : X × X => K z.1 z.2) =ᵐ[μ.prod μ]
      (fun z : X × X => L z.1 z.2)) (f : X → ℂ) :
    (fun x => ∫ y, K x y * f y ∂μ) =ᵐ[μ]
      (fun x => ∫ y, L x y * f y ∂μ) := by
  filter_upwards [Measure.ae_ae_of_ae_prod h] with x hx
  apply integral_congr_ae
  filter_upwards [hx] with y hy
  rw [hy]

/-- Lebesgue measure restricted to the interval used in the manuscript. -/
abbrev unitIntervalMeasure : Measure ℝ := volume.restrict (Set.Icc 0 1)

/-- The pointwise indicator of the diagonal, with complex values. -/
def diagonalIndicator (x y : ℝ) : ℂ := by
  classical
  exact if x = y then 1 else 0

theorem diagonalIndicator_row_ae_zero (x : ℝ) :
    diagonalIndicator x =ᵐ[unitIntervalMeasure] 0 := by
  have h : ∀ᵐ y ∂unitIntervalMeasure, x ≠ y := by
    rw [ae_iff]
    simp [eq_comm]
  filter_upwards [h] with y hy
  simp [diagonalIndicator, hy]

theorem diagonalIndicator_product_ae_zero :
    (fun z : ℝ × ℝ => diagonalIndicator z.1 z.2) =ᵐ[
      unitIntervalMeasure.prod unitIntervalMeasure] 0 := by
  have h : ∀ᵐ z ∂unitIntervalMeasure.prod unitIntervalMeasure, z.1 ≠ z.2 := by
    apply (Measure.ae_prod_iff_ae_ae
      (isClosed_eq continuous_fst continuous_snd).measurableSet.compl).2
    apply Filter.Eventually.of_forall
    intro x
    rw [ae_iff]
    simp [eq_comm]
  filter_upwards [h] with z hz
  simp [diagonalIndicator, hz]

/-- Every row integral against any input function is zero, not just the kernel a.e. -/
theorem diagonalIndicator_zero_operator (f : ℝ → ℂ) (x : ℝ) :
    (∫ y, diagonalIndicator x y * f y ∂unitIntervalMeasure) = 0 := by
  calc
    _ = ∫ _y, (0 : ℂ) ∂unitIntervalMeasure := by
      apply integral_congr_ae
      filter_upwards [diagonalIndicator_row_ae_zero x] with y hy
      simp only [Pi.zero_apply] at hy
      simp only [hy, zero_mul]
    _ = 0 := integral_zero _ _

theorem diagonalIndicator_diagonal_integral :
    (∫ x, diagonalIndicator x x ∂unitIntervalMeasure) = 1 := by
  simp [diagonalIndicator, integral_const, measureReal_def, Measure.restrict_apply,
    Real.volume_Icc]

theorem zero_kernel_diagonal_integral :
    (∫ _x : ℝ, (0 : ℂ) ∂unitIntervalMeasure) = 0 := integral_zero _ _

end TraceFormulas
