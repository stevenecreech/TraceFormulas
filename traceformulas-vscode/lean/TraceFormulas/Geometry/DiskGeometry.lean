import TraceFormulas.Geometry.InvariantGeometry
import Mathlib.Analysis.Complex.UnitDisc.Basic

/-!
# Cayley coordinates and the normalized point-pair invariant

The disk and half-plane are Mathlib's genuine domains. Coordinate identities and
pointwise metric coefficients are separated from the remaining path, measure,
ordered-pair orbit and radial-integration obligations.
-/
noncomputable section
open UpperHalfPlane
namespace TraceFormulas.Hyperbolic

def cayley (z : ℂ) : ℂ := (z - Complex.I) / (z + Complex.I)
def inverseCayley (ζ : ℂ) : ℂ := Complex.I * (1 + ζ) / (1 - ζ)

theorem cayley_den_ne_zero (z : ℍ) : (z : ℂ) + Complex.I ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.add_im, Complex.I_im, Complex.zero_im, coe_im] at hi
  linarith [z.im_pos]

theorem cayley_normSq_complement (z : ℍ) :
    1 - Complex.normSq (cayley z) = 4 * z.im / Complex.normSq ((z : ℂ) + Complex.I) := by
  have h := (Complex.normSq_pos.mpr (cayley_den_ne_zero z)).ne'
  rw [cayley, Complex.normSq_div]
  apply (eq_div_iff h).mpr
  field_simp
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.I_re, Complex.I_im, coe_im]
  ring

theorem cayley_norm_lt_one (z : ℍ) : ‖cayley z‖ < 1 := by
  have h : 0 < 1 - Complex.normSq (cayley z) := by
    rw [cayley_normSq_complement]
    exact div_pos (by positivity) (Complex.normSq_pos.mpr (cayley_den_ne_zero z))
  rw [Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg (cayley z)]

def cayleyToDisk (z : ℍ) : Complex.UnitDisc :=
  Complex.UnitDisc.mk (cayley z) (cayley_norm_lt_one z)

theorem inverseCayley_im (ζ : ℂ) :
    (inverseCayley ζ).im = (1 - Complex.normSq ζ) / Complex.normSq (1 - ζ) := by
  simp only [inverseCayley, Complex.div_im, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, zero_add, add_zero, zero_sub, Complex.normSq_apply]
  ring

theorem disk_den_ne_zero (ζ : Complex.UnitDisc) : (1 - (ζ : ℂ)) ≠ 0 :=
  sub_ne_zero.mpr ζ.coe_ne_one.symm

def inverseCayleyToHalf (ζ : Complex.UnitDisc) : ℍ :=
  ⟨inverseCayley ζ, by
    rw [inverseCayley_im]
    exact div_pos (sub_pos.mpr ζ.normSq_lt_one)
      (Complex.normSq_pos.mpr (disk_den_ne_zero ζ))⟩

theorem inverseCayleyToHalf_coe (ζ : Complex.UnitDisc) :
    ((inverseCayleyToHalf ζ : ℍ) : ℂ) = inverseCayley ζ := rfl

theorem inverseCayleyToHalf_im (ζ : Complex.UnitDisc) :
    (inverseCayleyToHalf ζ).im =
      (1 - Complex.normSq (ζ : ℂ)) / Complex.normSq (1 - (ζ : ℂ)) :=
  inverseCayley_im ζ

theorem inverseCayley_cayley (z : ℍ) : inverseCayley (cayley z) = (z : ℂ) := by
  have h := cayley_den_ne_zero z
  have hi : (1 - cayley z) ≠ 0 := disk_den_ne_zero (cayleyToDisk z)
  unfold inverseCayley
  apply (div_eq_iff hi).mpr
  unfold cayley
  field_simp
  ring

theorem cayley_inverseCayley (ζ : Complex.UnitDisc) : cayley (inverseCayley ζ) = (ζ : ℂ) := by
  have h := disk_den_ne_zero ζ
  have hi : inverseCayley (ζ : ℂ) + Complex.I ≠ 0 :=
    cayley_den_ne_zero (inverseCayleyToHalf ζ)
  unfold cayley
  apply (div_eq_iff hi).mpr
  unfold inverseCayley
  field_simp
  ring

/-- A bijection of the actual half-plane and disk, not yet a metric-space isometry. -/
def cayleyEquiv : ℍ ≃ Complex.UnitDisc where
  toFun := cayleyToDisk
  invFun := inverseCayleyToHalf
  left_inv z := by
    apply Subtype.ext
    exact inverseCayley_cayley z
  right_inv ζ := by
    apply Complex.UnitDisc.coe_injective
    exact cayley_inverseCayley ζ

theorem hasDerivAt_cayley (z : ℍ) :
    HasDerivAt cayley (2 * Complex.I / ((z : ℂ) + Complex.I) ^ 2) (z : ℂ) := by
  have h := ((hasDerivAt_id (z : ℂ)).sub_const Complex.I).div
    ((hasDerivAt_id (z : ℂ)).add_const Complex.I) (cayley_den_ne_zero z)
  convert h using 1
  simp only [id_eq]
  ring

theorem hasDerivAt_inverseCayley (ζ : Complex.UnitDisc) :
    HasDerivAt inverseCayley (2 * Complex.I / (1 - (ζ : ℂ)) ^ 2) (ζ : ℂ) := by
  have h := (((hasDerivAt_id (ζ : ℂ)).const_add 1).const_mul Complex.I).div
    ((hasDerivAt_id (ζ : ℂ)).const_sub 1) (disk_den_ne_zero ζ)
  convert h using 1
  simp only [id_eq]
  ring

/-- The inverse derivative pulls the actual half-plane tangent energy back to disk coefficients. -/
theorem inverseCayley_tangentEnergy (ζ : Complex.UnitDisc) (v : ℂ) :
    tangentEnergy (inverseCayleyToHalf ζ) (2 * Complex.I / (1 - (ζ : ℂ)) ^ 2 * v) =
      4 * Complex.normSq v / (1 - Complex.normSq (ζ : ℂ)) ^ 2 := by
  have hd := (Complex.normSq_pos.mpr (disk_den_ne_zero ζ)).ne'
  have hr := (sub_pos.mpr ζ.normSq_lt_one).ne'
  simp only [tangentEnergy, inverseCayleyToHalf_im,
    Complex.normSq_mul, Complex.normSq_div, map_pow]
  norm_num
  field_simp

def pointPair (z w : ℍ) : ℝ :=
  Complex.normSq ((z : ℂ) - w) / (4 * z.im * w.im)

theorem pointPair_eq_ratio (z w : ℍ) : pointPair z w = distanceRatio z w / 4 := by
  unfold pointPair distanceRatio
  ring

theorem pointPair_nonneg (z w : ℍ) : 0 ≤ pointPair z w := by
  exact div_nonneg (Complex.normSq_nonneg _) (by positivity)

theorem pointPair_eq_zero_iff (z w : ℍ) : pointPair z w = 0 ↔ z = w := by
  have h : 4 * z.im * w.im ≠ 0 := by positivity
  simp only [pointPair, div_eq_zero_iff, h, or_false, Complex.normSq_eq_zero, sub_eq_zero]
  exact Subtype.val_inj

theorem pointPair_symmetric (z w : ℍ) : pointPair z w = pointPair w z := by
  unfold pointPair
  have h : Complex.normSq ((z : ℂ) - w) = Complex.normSq ((w : ℂ) - z) := by
    rw [← Complex.normSq_neg ((w : ℂ) - z), neg_sub]
  rw [h]
  congr 1
  ring

theorem pointPair_invariant (g : RealGroup) (z w : ℍ) :
    pointPair (g • z) (g • w) = pointPair z w := by
  simp only [pointPair_eq_ratio, distanceRatio_invariant]

theorem inverseCayley_difference (ζ η : Complex.UnitDisc) :
    inverseCayley ζ - inverseCayley η =
      2 * Complex.I * ((ζ : ℂ) - η) / ((1 - (ζ : ℂ)) * (1 - (η : ℂ))) := by
  have hz := disk_den_ne_zero ζ
  have hw := disk_den_ne_zero η
  unfold inverseCayley
  field_simp
  ring

theorem pointPair_disk (ζ η : Complex.UnitDisc) :
    pointPair (inverseCayleyToHalf ζ) (inverseCayleyToHalf η) =
      Complex.normSq ((ζ : ℂ) - η) /
        ((1 - Complex.normSq (ζ : ℂ)) * (1 - Complex.normSq (η : ℂ))) := by
  have hz := (Complex.normSq_pos.mpr (disk_den_ne_zero ζ)).ne'
  have hw := (Complex.normSq_pos.mpr (disk_den_ne_zero η)).ne'
  have hr := (sub_pos.mpr ζ.normSq_lt_one).ne'
  have hs := (sub_pos.mpr η.normSq_lt_one).ne'
  simp only [pointPair, inverseCayleyToHalf_coe, inverseCayleyToHalf_im,
    inverseCayley_difference, Complex.normSq_div, Complex.normSq_mul]
  norm_num
  field_simp
  ring

/-- At the base point, the disk formula depends only on the other point's radius. -/
theorem pointPair_basepoint_cayley (w : ℍ) :
    pointPair I w = Complex.normSq (cayley w) / (1 - Complex.normSq (cayley w)) := by
  have h := pointPair_disk (cayleyToDisk I) (cayleyToDisk w)
  have left_inv (z : ℍ) : inverseCayleyToHalf (cayleyToDisk z) = z :=
    cayleyEquiv.left_inv z
  rw [left_inv, left_inv] at h
  simpa [cayleyToDisk, cayley] using h

end TraceFormulas.Hyperbolic
