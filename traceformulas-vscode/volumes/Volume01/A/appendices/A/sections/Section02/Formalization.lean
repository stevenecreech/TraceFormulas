import TraceFormulas.MeasureTheory.HaarBasics

/-!
# Appendix A.2: basic Haar measure results (partial)

These declarations apply to nonzero regular Borel left-invariant measures on
the book's locally compact Hausdorff second-countable groups. The formal facts
also hold without a Hausdorff hypothesis; inversion needs neither local
compactness nor second countability. Mathlib supplies the
standard measurable structure and measure operations; no measure is defined by
the desired conclusion. In these spaces regularity also gives compact inner
approximation on every Borel set, matching the book's Radon convention.

The companion covers positive mass of nonempty open sets, inversion exchanging
left and right invariance, uniqueness up to a finite positive scalar, and the
existence of the right-translation scalar with the book's convention.
The scalar's homomorphism and continuity properties are not yet formalized here.
-/
noncomputable section

open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal

namespace TraceFormulas.Volume01.A.Appendices.A.Section02

variable {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [MeasurableSpace L] [BorelSpace L] [LocallyCompactSpace L]
  [SecondCountableTopology L]

theorem haar_positive_on_open (ν : Measure L) [ν.Regular]
    [IsMulLeftInvariant ν] (hν : ν ≠ 0) {U : Set L}
    (hU : IsOpen U) (hne : U.Nonempty) : 0 < ν U :=
  HaarBasics.positive_on_open ν hν hU hne

omit [LocallyCompactSpace L] [SecondCountableTopology L] in
theorem haar_inverse (ν : Measure L) [ν.Regular]
    [IsMulLeftInvariant ν] (hν : ν ≠ 0) :
    ν.inv.Regular ∧ IsMulRightInvariant ν.inv ∧ ν.inv ≠ 0 :=
  HaarBasics.inverse_is_right_haar ν hν

theorem haar_unique_scale (ν μ : Measure L) [ν.Regular] [μ.Regular]
    [IsMulLeftInvariant ν] [IsMulLeftInvariant μ] (hν : ν ≠ 0) (hμ : μ ≠ 0) :
    ∃! c : ℝ≥0, 0 < c ∧ ν = (c : ℝ≥0∞) • μ := by
  letI := HaarBasics.left_haar_of_nonzero ν hν
  letI := HaarBasics.left_haar_of_nonzero μ hμ
  exact HaarBasics.unique_positive_scale ν μ

theorem haar_right_translate_scale (ν : Measure L) [ν.Regular]
    [IsMulLeftInvariant ν] (hν : ν ≠ 0) (h : L) :
    ∃! c : ℝ≥0, 0 < c ∧ map (fun x => x * h⁻¹) ν = (c : ℝ≥0∞) • ν := by
  letI := HaarBasics.left_haar_of_nonzero ν hν
  exact HaarBasics.right_translate_scale ν h

omit [LocallyCompactSpace L] [SecondCountableTopology L] in
theorem haar_right_translate_apply (ν : Measure L) (h : L) {E : Set L}
    (hE : MeasurableSet E) :
    map (fun x => x * h⁻¹) ν E = ν ((fun x => x * h) '' E) :=
  HaarBasics.right_translate_apply ν h hE

end TraceFormulas.Volume01.A.Appendices.A.Section02
