import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Haar measure: nonvanishing, uniqueness, and left/right transport

These results use actual Borel measures and the standard topological group
structure. In second-countable locally compact Hausdorff groups, Mathlib's
`Regular` and finite-on-compacts hypotheses also supply inner regularity on all
Borel sets. The book's nonzero regular left-invariant measure therefore gives
Mathlib's `IsHaarMeasure`, whose fields include positivity on nonempty open sets.

The uniqueness proof reuses Mathlib's general uniqueness of sigma-finite
invariant measures. Its normalization uses a compact set with nonempty interior.
For right translation, `map (fun x => x * h⁻¹) ν` evaluates on a Borel set `E`
as `ν (E * h)`: the inverse is essential to the manuscript's scalar convention.
-/
noncomputable section

open Set MeasureTheory MeasureTheory.Measure TopologicalSpace
open scoped ENNReal NNReal Pointwise Topology

namespace TraceFormulas.HaarBasics

variable {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [MeasurableSpace L] [BorelSpace L] [LocallyCompactSpace L]
  [SecondCountableTopology L]

theorem left_haar_of_nonzero (ν : Measure L) [ν.Regular]
    [IsMulLeftInvariant ν] (hν : ν ≠ 0) : IsHaarMeasure ν := by
  letI : NeZero ν := ⟨hν⟩
  exact { toIsFiniteMeasureOnCompacts := inferInstance
          toIsMulLeftInvariant := inferInstance
          toIsOpenPosMeasure := inferInstance }

theorem positive_on_open (ν : Measure L) [ν.Regular]
    [IsMulLeftInvariant ν] (hν : ν ≠ 0) {U : Set L}
    (hU : IsOpen U) (hne : U.Nonempty) : 0 < ν U := by
  letI := left_haar_of_nonzero ν hν
  exact hU.measure_pos ν hne

omit [LocallyCompactSpace L] [SecondCountableTopology L] in
theorem inverse_is_right_haar (ν : Measure L) [ν.Regular]
    [IsMulLeftInvariant ν] (hν : ν ≠ 0) :
    ν.inv.Regular ∧ IsMulRightInvariant ν.inv ∧ ν.inv ≠ 0 := by
  refine ⟨regular_inv_iff.mpr inferInstance, inferInstance, ?_⟩
  intro hz
  apply hν
  have h := congrArg Measure.inv hz
  rw [Measure.inv_inv] at h
  simpa only [Measure.inv_def, Measure.map_zero] using h

theorem unique_positive_scale (ν μ : Measure L)
    [IsHaarMeasure ν] [IsHaarMeasure μ] :
    ∃! c : ℝ≥0, 0 < c ∧ ν = (c : ℝ≥0∞) • μ := by
  let K : PositiveCompacts L := Classical.choice inferInstance
  have hμ0 : μ K ≠ 0 := (measure_pos_of_nonempty_interior μ K.interior_nonempty).ne'
  have hν0 : ν K ≠ 0 := (measure_pos_of_nonempty_interior ν K.interior_nonempty).ne'
  have hμfin : μ K ≠ ⊤ := K.isCompact.measure_ne_top
  have hνfin : ν K ≠ ⊤ := K.isCompact.measure_ne_top
  have heq : ν = (ν K / μ K) • μ := measure_eq_div_smul ν μ hμ0 hμfin
  have hfin : ν K / μ K ≠ ⊤ := ENNReal.div_ne_top hνfin hμ0
  have hpos : 0 < ν K / μ K := ENNReal.div_pos hν0 hμfin
  refine ⟨(ν K / μ K).toNNReal, ⟨?_, ?_⟩, ?_⟩
  · exact ENNReal.toNNReal_pos hpos.ne' hfin
  · rwa [ENNReal.coe_toNNReal hfin]
  · intro c hc
    apply ENNReal.coe_injective
    rw [ENNReal.coe_toNNReal hfin]
    have hh := congrArg (fun m : Measure L => m (K : Set L)) hc.2
    simp only [smul_apply, smul_eq_mul] at hh
    rw [hh, ENNReal.mul_div_cancel_right hμ0 hμfin]

theorem right_translate_scale (ν : Measure L) [IsHaarMeasure ν] (h : L) :
    ∃! c : ℝ≥0, 0 < c ∧ map (fun x => x * h⁻¹) ν = (c : ℝ≥0∞) • ν :=
  unique_positive_scale (map (fun x => x * h⁻¹) ν) ν

omit [LocallyCompactSpace L] [SecondCountableTopology L] in
theorem right_translate_apply (ν : Measure L) (h : L) {E : Set L}
    (hE : MeasurableSet E) :
    map (fun x => x * h⁻¹) ν E = ν ((fun x => x * h) '' E) := by
  rw [map_apply (measurable_mul_const _) hE]
  congr 1
  ext x
  constructor
  · intro hx
    exact ⟨x * h⁻¹, hx, by simp⟩
  · rintro ⟨y, hy, rfl⟩
    change (y * h) * h⁻¹ ∈ E
    simpa only [mul_assoc, mul_inv_cancel, mul_one] using hy

end TraceFormulas.HaarBasics
