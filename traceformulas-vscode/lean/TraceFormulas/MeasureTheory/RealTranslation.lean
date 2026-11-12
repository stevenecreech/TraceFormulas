import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Translation-invariant measures on the real line

The measurable structure on `ℝ` is its Borel sigma-algebra, and `volume` is
Mathlib's Lebesgue measure. Finite-on-compacts implies sigma-finiteness here.
The scalar includes zero and is fixed by the mass of the unit half-open interval.

The proof reuses Mathlib's uniqueness theorem for additive invariant measures,
which is more general than the manuscript's interval-subdivision argument.
-/
noncomputable section
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal
namespace TraceFormulas.RealTranslation

theorem eq_smul_volume (ν : Measure ℝ)
    [IsFiniteMeasureOnCompacts ν] [IsAddLeftInvariant ν] :
    ν = ν (Ico 0 1) • volume := by
  ext s hs
  have h := measure_add_measure_eq ν volume (Ico (0 : ℝ) 1) s (by simp) (by simp)
  simpa only [Real.volume_Ico, sub_zero, ENNReal.ofReal_one, one_mul,
    smul_apply, smul_eq_mul] using h.symm

theorem measure_Ico (ν : Measure ℝ)
    [IsFiniteMeasureOnCompacts ν] [IsAddLeftInvariant ν] (a b : ℝ) :
    ν (Ico a b) = ν (Ico 0 1) * ENNReal.ofReal (b - a) := by
  conv_lhs => rw [eq_smul_volume ν]
  simp only [smul_apply, smul_eq_mul, Real.volume_Ico]

theorem existsUnique_scale (ν : Measure ℝ)
    [IsFiniteMeasureOnCompacts ν] [IsAddLeftInvariant ν] :
    ∃! c : ℝ≥0, ν = (c : ℝ≥0∞) • volume := by
  have hfin : ν (Ico (0 : ℝ) 1) ≠ ⊤ :=
    (measure_mono Ico_subset_Icc_self).trans_lt isCompact_Icc.measure_lt_top |>.ne
  refine ⟨(ν (Ico (0 : ℝ) 1)).toNNReal, ?_, ?_⟩
  · change ν = ((ν (Ico (0 : ℝ) 1)).toNNReal : ℝ≥0∞) • volume
    rw [ENNReal.coe_toNNReal hfin]
    exact eq_smul_volume ν
  · intro c hc
    apply ENNReal.coe_injective
    rw [ENNReal.coe_toNNReal hfin, hc]
    simp

end TraceFormulas.RealTranslation
