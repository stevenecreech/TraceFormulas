import TraceFormulas.MeasureTheory.HaarBasics
import TraceFormulas.Geometry.IwasawaCharacters

/-!
# Section 1.8: abstract Haar measure facts (partial)

These declarations formalize the abstract uniqueness and inversion statements
used to organize the chapter. They do not yet construct the actual Haar measure
on SL₂(ℝ), identify its quotient measure on the half-plane, or prove the modular
covolumes. They also cover the conjugation and positive-character arguments
for the diagonal Iwasawa factor, without identifying that character with the
actual modular function. The former real-line companion now belongs to Appendix A.1.
-/
noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal

namespace TraceFormulas.Volume01.A.Chapter01.Section08

theorem quarter_turn_conjugation (y : ℝ) (hy : 0 < y) :
    Hyperbolic.rotation (Real.pi / 2) * Hyperbolic.dilation y hy *
      (Hyperbolic.rotation (Real.pi / 2))⁻¹ = (Hyperbolic.dilation y hy)⁻¹ :=
  Hyperbolic.quarter_turn_conjugates_dilation y hy

theorem positive_reciprocal_fixed_point {x : ℝ} (hx : 0 < x) (h : x = x⁻¹) : x = 1 :=
  Hyperbolic.positive_eq_one_of_eq_inv hx h

theorem positive_character_on_dilation (χ : Hyperbolic.RealGroup →* ℝˣ)
    (hpos : ∀ g, 0 < (χ g : ℝ)) (y : ℝ) (hy : 0 < y) :
    χ (Hyperbolic.dilation y hy) = 1 :=
  Hyperbolic.positive_character_dilation χ hpos y hy

variable {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [MeasurableSpace L] [BorelSpace L] [LocallyCompactSpace L]
  [SecondCountableTopology L]

theorem haar_unique_scale (ν μ : Measure L) [ν.Regular] [μ.Regular]
    [IsMulLeftInvariant ν] [IsMulLeftInvariant μ] (hν : ν ≠ 0) (hμ : μ ≠ 0) :
    ∃! c : ℝ≥0, 0 < c ∧ ν = (c : ℝ≥0∞) • μ := by
  letI := HaarBasics.left_haar_of_nonzero ν hν
  letI := HaarBasics.left_haar_of_nonzero μ hμ
  exact HaarBasics.unique_positive_scale ν μ

omit [LocallyCompactSpace L] [SecondCountableTopology L] in
theorem haar_inverse (ν : Measure L) [ν.Regular]
    [IsMulLeftInvariant ν] (hν : ν ≠ 0) :
    ν.inv.Regular ∧ IsMulRightInvariant ν.inv ∧ ν.inv ≠ 0 :=
  HaarBasics.inverse_is_right_haar ν hν

end TraceFormulas.Volume01.A.Chapter01.Section08
