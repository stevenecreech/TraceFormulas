import TraceFormulas.Geometry.DiskGeometry

/-!
# Section 1.4: Cayley coordinates and point pairs (partial coverage)

Mathlib's actual half-plane and unit disk are connected by inverse Cayley maps.
The derivatives and tangent metric coefficients are checked. The normalized
point-pair invariant, its disk expression, and its specialization at i are also checked. Rotation
conjugacy, geodesics, path-distance identities, orbit classification, induced
area and radial integration remain to be formalized.
-/
noncomputable section
open UpperHalfPlane TraceFormulas.Hyperbolic
namespace TraceFormulas.Volume01.A.Chapter01.Section04

/-! Cayley bijection: hyperbolic.cayley. -/
theorem cayley_disk_complement (z : ℍ) :
    1 - Complex.normSq (cayley z) = 4 * z.im / Complex.normSq ((z : ℂ) + Complex.I) :=
  cayley_normSq_complement z

theorem inverse_cayley_imaginary_part (ζ : Complex.UnitDisc) :
    (inverseCayley (ζ : ℂ)).im =
      (1 - Complex.normSq (ζ : ℂ)) / Complex.normSq (1 - (ζ : ℂ)) :=
  inverseCayley_im ζ

theorem cayley_left_inverse (z : ℍ) : inverseCayley (cayley z) = (z : ℂ) :=
  inverseCayley_cayley z

theorem cayley_right_inverse (ζ : Complex.UnitDisc) : cayley (inverseCayley ζ) = (ζ : ℂ) :=
  cayley_inverseCayley ζ

theorem cayley_bijection : Function.Bijective cayleyToDisk := cayleyEquiv.bijective

/-! Coordinate derivatives and metric: hyperbolic.disk-metric. Path and area bridges remain open. -/
theorem cayley_derivative (z : ℍ) :
    HasDerivAt cayley (2 * Complex.I / ((z : ℂ) + Complex.I) ^ 2) (z : ℂ) :=
  hasDerivAt_cayley z

theorem inverse_cayley_derivative (ζ : Complex.UnitDisc) :
    HasDerivAt inverseCayley (2 * Complex.I / (1 - (ζ : ℂ)) ^ 2) (ζ : ℂ) :=
  hasDerivAt_inverseCayley ζ

theorem disk_metric_coefficients (ζ : Complex.UnitDisc) (v : ℂ) :
    tangentEnergy (inverseCayleyToHalf ζ) (2 * Complex.I / (1 - (ζ : ℂ)) ^ 2 * v) =
      4 * Complex.normSq v / (1 - Complex.normSq (ζ : ℂ)) ^ 2 :=
  inverseCayley_tangentEnergy ζ v

/-! Elementary properties: hyperbolic.point-pair-properties. -/
theorem point_pair_nonnegative (z w : ℍ) : 0 ≤ pointPair z w := pointPair_nonneg z w

theorem point_pair_zero (z w : ℍ) : pointPair z w = 0 ↔ z = w := pointPair_eq_zero_iff z w

theorem point_pair_symmetry (z w : ℍ) : pointPair z w = pointPair w z :=
  pointPair_symmetric z w

theorem point_pair_invariance (g : RealGroup) (z w : ℍ) :
    pointPair (g • z) (g • w) = pointPair z w := pointPair_invariant g z w

/-! Disk-coordinate formula: hyperbolic.point-pair-disk. The path-distance corollary hyperbolic.point-pair-distance remains open. -/
theorem inverse_cayley_difference (ζ η : Complex.UnitDisc) :
    inverseCayley ζ - inverseCayley η =
      2 * Complex.I * ((ζ : ℂ) - η) / ((1 - (ζ : ℂ)) * (1 - (η : ℂ))) :=
  inverseCayley_difference ζ η

theorem point_pair_disk_formula (ζ η : Complex.UnitDisc) :
    pointPair (inverseCayleyToHalf ζ) (inverseCayleyToHalf η) =
      Complex.normSq ((ζ : ℂ) - η) /
        ((1 - Complex.normSq (ζ : ℂ)) * (1 - Complex.normSq (η : ℂ))) :=
  pointPair_disk ζ η

/-! Substitution used in hyperbolic.pair-orbits. Rotation matching, orbit classification and hyperbolic.radial-functions remain open. -/
/-- Substitute the disk coordinates 0 and C(w) into the general disk formula. -/
theorem point_pair_from_i (w : ℍ) :
    pointPair I w = Complex.normSq (cayley w) / (1 - Complex.normSq (cayley w)) :=
  pointPair_basepoint_cayley w

end TraceFormulas.Volume01.A.Chapter01.Section04
