import TraceFormulas.Geometry.InvariantGeometry

/-!
# Section 1.3: invariant tangent geometry (partial coverage)

These results concern actual real bilinear forms, the complex derivative of the
fractional action, density covariance, gradient duality with a real linear
differential, and the invariant J used in the geodesic proof. They do not yet construct a
smooth Riemannian bundle, identify its volume with a Lebesgue measure, or prove
the claims about path distance, geodesics, the Laplacian or Radon measures.
-/
noncomputable section
open UpperHalfPlane TraceFormulas.Hyperbolic
namespace TraceFormulas.Volume01.A.Chapter01.Section03

/-! Derivative used in the invariant-geometry calculations. -/
theorem fractional_action_derivative (g : RealGroup) (z : ℍ) :
    HasDerivAt (fun w : ℂ => ((g 0 0 : ℂ) * w + g 0 1) / factor g w)
      (mobiusDerivative g z) (z : ℂ) :=
  hasDerivAt_fractional_action g z

theorem tangent_squared_length_positive (z : ℍ) (v : ℂ) (hv : v ≠ 0) :
    0 < tangentEnergy z v :=
  tangentEnergy_positive z v hv

theorem euclidean_normalization_at_i (v : ℂ) :
    tangentEnergy UpperHalfPlane.I v = Complex.normSq v :=
  tangentEnergy_at_I v

theorem tangent_squared_length_invariant (g : RealGroup) (z : ℍ) (v : ℂ) :
    tangentEnergy (g • z) (mobiusDerivative g z * v) = tangentEnergy z v :=
  tangentEnergy_invariant g z v

/-! Metric uniqueness: hyperbolic.invariant-geometry; smooth bundle interface remains open. -/
theorem invariant_metric_coefficients (B : ℍ → LinearMap.BilinForm ℝ ℂ)
    (hsym : ∀ z v w, B z v w = B z w v)
    (hpos : ∀ z v, v ≠ 0 → 0 < B z v v)
    (hinv : IsInvariantBilinearField B) :
    ∃ c : ℝ, 0 < c ∧ ∀ (z : ℍ) (v w : ℂ),
      B z v w = (c / z.im ^ 2) * (v * star w).re := by
  refine ⟨B UpperHalfPlane.I 1 1, hpos _ _ one_ne_zero, ?_⟩
  exact invariantBilinearField_unique B hsym hinv

/-! Density identities for hyperbolic.invariant-density; the measure bridge remains open. -/
theorem area_density_covariance (g : RealGroup) (z : ℍ) :
    areaDensity (g • z) * Complex.normSq (mobiusDerivative g z) = areaDensity z :=
  areaDensity_covariant g z

theorem invariant_positive_density_unique (ρ : ℍ → ℝ) (hpos : ∀ z, 0 < ρ z)
    (hinv : ∀ (g : RealGroup) (z : ℍ),
      ρ (g • z) * Complex.normSq (mobiusDerivative g z) = ρ z) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, ρ z = C / z.im ^ 2 := by
  exact ⟨ρ UpperHalfPlane.I, hpos _, density_unique ρ hinv⟩

/-- The actual real bilinear tangent form has the manuscript's coefficient formula. -/
theorem tangent_inner_product_formula (z : ℍ) (v w : ℂ) :
    tangentForm z v w = (v * star w).re / z.im ^ 2 :=
  tangentForm_apply z v w

theorem tangent_inner_product_symmetric (z : ℍ) (v w : ℂ) :
    tangentForm z v w = tangentForm z w v :=
  tangentForm_symmetric z v w

theorem tangent_inner_product_positive (z : ℍ) (v : ℂ) (hv : v ≠ 0) :
    0 < tangentForm z v v :=
  tangentForm_positive z v hv

theorem tangent_inner_product_invariant (g : RealGroup) (z : ℍ) (v w : ℂ) :
    tangentForm (g • z) (mobiusDerivative g z * v) (mobiusDerivative g z * w) =
      tangentForm z v w :=
  tangentForm_invariant g z v w

theorem tangent_length_invariant (g : RealGroup) (z : ℍ) (v : ℂ) :
    ‖mobiusDerivative g z * v‖ / (g • z).im = ‖v‖ / z.im :=
  tangent_norm_invariant g z v

/-! Pointwise gradient characterization: hyperbolic.gradient. -/
/-- Duality with a real linear differential, before integrating it into a vector field. -/
theorem gradient_duality (z : ℍ) (ell : ℂ →ₗ[ℝ] ℝ) (v : ℂ) :
    tangentForm z (gradientFromDifferential z ell) v = ell v :=
  gradientFromDifferential_duality z ell v

/-! Invariant ratio used in hyperbolic.distance-formula. Vertical and circular minimizing paths remain open. -/
/-- This is the invariant J, not yet the characterization of distance by paths. -/
theorem two_point_ratio_invariant (g : RealGroup) (z w : ℍ) :
    distanceRatio (g • z) (g • w) = distanceRatio z w :=
  distanceRatio_invariant g z w

end TraceFormulas.Volume01.A.Chapter01.Section03
