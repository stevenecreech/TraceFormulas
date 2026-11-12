import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.Topology.Order.Compact

/-!
# Uniqueness from generating families

These are uniqueness statements for Mathlib's measures and their actual
sigma-algebras. The finite theorem uses Dynkin's π–λ argument in Mathlib;
the countable-cover theorem applies the finite argument to restrictions.
The real-line specialization uses bounded half-open intervals, with finite
interval mass supplied by the compact closure.
-/
noncomputable section
open Set MeasureTheory MeasureTheory.Measure MeasurableSpace
open scoped ENNReal
namespace TraceFormulas.BorelUniqueness

/-- A Dynkin system containing a π-system contains its generated sigma-algebra. -/
theorem pi_lambda {α : Type*} (C : Set (Set α)) (hC : IsPiSystem C)
    (D : DynkinSystem α) (hCD : ∀ s ∈ C, D.Has s)
    {s : Set α} (hs : MeasurableSet[generateFrom C] s) : D.Has s := by
  have hgen : (DynkinSystem.generate C).Has s := by
    rwa [DynkinSystem.generateFrom_eq hC] at hs
  exact DynkinSystem.generate_le D hCD s hgen

/-- Finite measures agreeing on a generating π-system and on the whole space agree. -/
theorem finite_eq_of_pi_system {α : Type*} [m : MeasurableSpace α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (C : Set (Set α)) (hgen : m = generateFrom C) (hC : IsPiSystem C)
    (hwhole : μ univ = ν univ) (h : ∀ s ∈ C, μ s = ν s) : μ = ν :=
  MeasureTheory.ext_of_generate_finite C hgen hC h hwhole

/-- A common countable finite-mass cover removes the total-finiteness hypothesis. -/
theorem eq_of_pi_system_cover {α : Type*} [m : MeasurableSpace α]
    (μ ν : Measure α) (C : Set (Set α)) (hgen : m = generateFrom C)
    (hC : IsPiSystem C) (E : ℕ → Set α) (hcover : ⋃ n, E n = univ)
    (hE : ∀ n, E n ∈ C) (hfinite : ∀ n, μ (E n) ≠ ∞)
    (h : ∀ s ∈ C, μ s = ν s) : μ = ν :=
  Measure.ext_of_generateFrom_of_iUnion C E hgen hC hcover hE hfinite h

/-- Bounded half-open intervals determine Borel measures finite on compact sets. -/
theorem real_eq_of_Ico (μ ν : Measure ℝ)
    [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    (h : ∀ a b : ℝ, a < b → μ (Ico a b) = ν (Ico a b)) : μ = ν := by
  apply Measure.ext_of_Ico' μ ν
  · intro a b _
    exact ((measure_mono Ico_subset_Icc_self).trans_lt isCompact_Icc.measure_lt_top).ne
  · exact fun {a b} hab => h a b hab

private theorem ico_countably_spanning (α : Type*) [TopologicalSpace α]
    [SecondCountableTopology α] [LinearOrder α] [OrderTopology α]
    [Nonempty α] [NoMaxOrder α] :
    IsCountablySpanning {t : Set α | ∃ a b, a < b ∧ Ico a b = t} := by
  rcases exists_countable_dense_bot_top α with ⟨s, hsc, hsd, hsb, _⟩
  let T : Set (Set α) := {t | ∃ a ∈ s, ∃ b ∈ s, a < b ∧ Ico a b = t}
  have hTc : T.Countable := by
    have h := hsc.biUnion fun a _ => hsc.biUnion fun b _ =>
      countable_iUnion fun _ : a < b => countable_singleton (Ico a b)
    simpa only [← setOf_eq_eq_singleton, ← setOf_exists, T, eq_comm, exists_prop] using h
  have hTU : ⋃₀ T = univ := by
    refine sUnion_eq_univ_iff.2 fun x => ?_
    rcases hsd.exists_le' hsb x with ⟨a, has, hax⟩
    rcases hsd.exists_gt x with ⟨b, hbs, hxb⟩
    exact ⟨Ico a b, ⟨a, has, b, hbs, hax.trans_lt hxb, rfl⟩, hax, hxb⟩
  have hTne : T.Nonempty := by
    obtain ⟨x⟩ := ‹Nonempty α›
    obtain ⟨t, ht, _⟩ := sUnion_eq_univ_iff.mp hTU x
    exact ⟨t, ht⟩
  obtain ⟨E, hE⟩ := hTc.exists_eq_range hTne
  refine ⟨E, ?_, ?_⟩
  · intro n
    have hn : E n ∈ T := hE ▸ mem_range_self n
    rcases hn with ⟨a, _, b, _, hab, heq⟩
    exact ⟨a, b, hab, heq⟩
  · simpa only [hE, sUnion_range] using hTU

/-- Compactly bounded half-open rectangles determine measures on ordered products. -/
theorem eq_of_Ico_prod {α β : Type*}
    [TopologicalSpace α] [SecondCountableTopology α] [LinearOrder α]
    [OrderTopology α] [MeasurableSpace α] [BorelSpace α]
    [CompactIccSpace α] [Nonempty α] [NoMaxOrder α]
    [TopologicalSpace β] [SecondCountableTopology β] [LinearOrder β]
    [OrderTopology β] [MeasurableSpace β] [BorelSpace β]
    [CompactIccSpace β] [Nonempty β] [NoMaxOrder β]
    (μ ν : Measure (α × β))
    [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    (h : ∀ a b : α, ∀ c d : β, a < b → c < d →
      μ (Ico a b ×ˢ Ico c d) = ν (Ico a b ×ˢ Ico c d)) : μ = ν := by
  let C : Set (Set α) := {s | ∃ a b, a < b ∧ Ico a b = s}
  let D : Set (Set β) := {s | ∃ c d, c < d ∧ Ico c d = s}
  have hC : IsCountablySpanning C := ico_countably_spanning α
  have hD : IsCountablySpanning D := ico_countably_spanning β
  have hgenC : generateFrom C = ‹MeasurableSpace α› :=
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Ico α)).symm
  have hgenD : generateFrom D = ‹MeasurableSpace β› :=
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Ico β)).symm
  obtain ⟨E, hE, hcover⟩ := hC.prod hD
  refine eq_of_pi_system_cover μ ν (image2 (· ×ˢ ·) C D)
    (generateFrom_eq_prod hgenC hgenD hC hD).symm
    ((isPiSystem_Ico id id).prod (isPiSystem_Ico id id)) E hcover hE ?_ ?_
  · intro n
    rcases hE n with ⟨s, ⟨a, b, _, rfl⟩, t, ⟨c, d, _, rfl⟩, heq⟩
    rw [← heq]
    exact ((measure_mono (Set.prod_mono Ico_subset_Icc_self Ico_subset_Icc_self)).trans_lt
      (isCompact_Icc.prod isCompact_Icc).measure_lt_top).ne
  · rintro s ⟨_, ⟨a, b, hab, rfl⟩, _, ⟨c, d, hcd, rfl⟩, rfl⟩
    exact h a b c d hab hcd

/-- The coordinate half-plane uses its subspace Borel structure. -/
theorem half_plane_eq_of_rectangles
    (μ ν : Measure (ℝ × Set.Ioi (0 : ℝ)))
    [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    (h : ∀ a b : ℝ, ∀ c d : Set.Ioi (0 : ℝ), a < b → c < d →
      μ (Ico a b ×ˢ Ico c d) = ν (Ico a b ×ˢ Ico c d)) : μ = ν := by
  letI : CompactIccSpace (Set.Ioi (0 : ℝ)) := ⟨fun {a b} =>
    Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr (by
      simpa only [Set.image_subtype_val_Icc] using
        (isCompact_Icc : IsCompact (Icc (a : ℝ) (b : ℝ))))⟩
  exact eq_of_Ico_prod μ ν h

end TraceFormulas.BorelUniqueness
