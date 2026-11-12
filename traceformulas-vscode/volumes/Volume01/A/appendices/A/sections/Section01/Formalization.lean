import TraceFormulas.MeasureTheory.RealTranslation
import TraceFormulas.MeasureTheory.BorelUniqueness

/-!
# Appendix A.1: measure uniqueness and the real-line measure lemma (partial)

The companion covers Dynkin's π–λ principle, uniqueness from a generating
π-system with finite mass or a countable finite-mass cover, and uniqueness of
Borel measures on `ℝ` from bounded half-open intervals and on
`ℝ × (0, ∞)` from compactly bounded half-open rectangles, as well as the
preparatory uniqueness of translation-invariant Borel measures on `ℝ`.
The refresher's examples and weighted-measure and pushforward identities are
not covered by these uniqueness declarations.

Mathlib's `IsAddLeftInvariant` expresses invariance as equality of pushforward
measures under translations. Since translations are measurable bijections, this
is the book's invariance of the measure of translated Borel sets.
-/
noncomputable section
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal
namespace TraceFormulas.Volume01.A.Appendices.A.Section01

theorem pi_lambda {α : Type*} (C : Set (Set α)) (hC : IsPiSystem C)
    (D : MeasurableSpace.DynkinSystem α) (hCD : ∀ s ∈ C, D.Has s)
    {s : Set α} (hs : MeasurableSet[MeasurableSpace.generateFrom C] s) : D.Has s :=
  BorelUniqueness.pi_lambda C hC D hCD hs

theorem finite_measure_uniqueness {α : Type*} [m : MeasurableSpace α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (C : Set (Set α)) (hgen : m = MeasurableSpace.generateFrom C)
    (hC : IsPiSystem C) (hwhole : μ univ = ν univ)
    (h : ∀ s ∈ C, μ s = ν s) : μ = ν :=
  BorelUniqueness.finite_eq_of_pi_system μ ν C hgen hC hwhole h

theorem measure_uniqueness_of_finite_cover {α : Type*} [m : MeasurableSpace α]
    (μ ν : Measure α) (C : Set (Set α))
    (hgen : m = MeasurableSpace.generateFrom C) (hC : IsPiSystem C)
    (E : ℕ → Set α) (hcover : ⋃ n, E n = univ) (hE : ∀ n, E n ∈ C)
    (hfinite : ∀ n, μ (E n) ≠ ∞) (h : ∀ s ∈ C, μ s = ν s) : μ = ν :=
  BorelUniqueness.eq_of_pi_system_cover μ ν C hgen hC E hcover hE hfinite h

theorem real_borel_measure_uniqueness (μ ν : Measure ℝ)
    [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    (h : ∀ a b : ℝ, a < b → μ (Ico a b) = ν (Ico a b)) : μ = ν :=
  BorelUniqueness.real_eq_of_Ico μ ν h

theorem rectangle_borel_measure_uniqueness
    (μ ν : Measure (ℝ × Set.Ioi (0 : ℝ)))
    [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    (h : ∀ a b : ℝ, ∀ c d : Set.Ioi (0 : ℝ), a < b → c < d →
      μ (Ico a b ×ˢ Ico c d) = ν (Ico a b ×ˢ Ico c d)) : μ = ν :=
  BorelUniqueness.half_plane_eq_of_rectangles μ ν h

theorem translation_invariant_eq (ν : Measure ℝ)
    [IsFiniteMeasureOnCompacts ν] [IsAddLeftInvariant ν] :
    ν = ν (Ico 0 1) • volume :=
  RealTranslation.eq_smul_volume ν

theorem translation_invariant_interval (ν : Measure ℝ)
    [IsFiniteMeasureOnCompacts ν] [IsAddLeftInvariant ν] (a b : ℝ) :
    ν (Ico a b) = ν (Ico 0 1) * ENNReal.ofReal (b - a) :=
  RealTranslation.measure_Ico ν a b

theorem translation_invariant_unique_scale (ν : Measure ℝ)
    [IsFiniteMeasureOnCompacts ν] [IsAddLeftInvariant ν] :
    ∃! c : ℝ≥0, ν = (c : ℝ≥0∞) • volume :=
  RealTranslation.existsUnique_scale ν

end TraceFormulas.Volume01.A.Appendices.A.Section01
