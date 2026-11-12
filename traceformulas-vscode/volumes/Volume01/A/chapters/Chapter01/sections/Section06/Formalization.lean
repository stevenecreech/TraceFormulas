import TraceFormulas.Geometry.ModularDomain

/-!
# Section 1.6: modular generators and orbit reduction (partial)

`fd` uses squared complex norm, equivalent to the book's |z| >= 1.
`fdo` is defined by strict inequalities; a topological-interior identification
is not claimed here. Interior uniqueness below assumes BOTH representatives
are strict and asserts equality of points. The stronger centrality conclusion,
the denominator lemma, boundary classification and tiling remain obligations.
-/
noncomputable section
open scoped MatrixGroups
open Matrix ModularGroup UpperHalfPlane
namespace TraceFormulas.Volume01.A.Chapter01.Section06

theorem generator_S_rows (g : SL(2, ℤ)) :
    ((S * g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![-g 1 0, -g 1 1; g 0 0, g 0 1] := ModularDomain.S_rows g

theorem generator_T_rows (q : ℤ) (g : SL(2, ℤ)) :
    ((T ^ q * g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![g 0 0 + q * g 1 0, g 0 1 + q * g 1 1; g 1 0, g 1 1] :=
  ModularDomain.T_power_rows q g

theorem generators : Subgroup.closure {S, T} = ⊤ :=
  _root_.SpecialLinearGroup.SL2Z_generators

theorem generator_S_square : (S : SL(2, ℤ)) ^ 2 = -1 := ModularDomain.S_square

theorem generator_ST_cube : ((S * T : SL(2, ℤ)) ^ 3) = -1 := ModularDomain.ST_cube

theorem translation_action (n : ℤ) (z : ℍ) :
    ((T ^ n • z : ℍ) : ℂ) = (z : ℂ) + n := coe_T_zpow_smul_eq z

theorem domain_membership (z : ℍ) :
    z ∈ fd ↔ |z.re| ≤ (1 : ℝ) / 2 ∧ 1 ≤ ‖(z : ℂ)‖ := by
  change (1 ≤ Complex.normSq (z : ℂ) ∧ _) ↔ _
  rw [Complex.normSq_eq_norm_sq]
  have h := norm_nonneg (z : ℂ)
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, by nlinarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by nlinarith, h1⟩

theorem strict_domain_membership (z : ℍ) :
    z ∈ fdo ↔ |z.re| < (1 : ℝ) / 2 ∧ 1 < ‖(z : ℂ)‖ := by
  change (1 < Complex.normSq (z : ℂ) ∧ _) ↔ _
  rw [Complex.normSq_eq_norm_sq]
  have h := norm_nonneg (z : ℂ)
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, by nlinarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by nlinarith, h1⟩

theorem domain_height_bound {z : ℍ} (hz : z ∈ fd) : 3 ≤ 4 * z.im ^ 2 :=
  three_le_four_mul_im_sq_of_mem_fd hz

theorem orbit_meets_domain (z : ℍ) : ∃ g : SL(2, ℤ), g • z ∈ fd :=
  exists_smul_mem_fd z

theorem strict_representatives_equal (g : SL(2, ℤ)) (z : ℍ)
    (hz : z ∈ fdo) (hg : g • z ∈ fdo) : z = g • z :=
  eq_smul_self_of_mem_fdo_mem_fdo hz hg

end TraceFormulas.Volume01.A.Chapter01.Section06
