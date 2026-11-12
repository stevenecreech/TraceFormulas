import TraceFormulas.Geometry.RealMobius
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! Elementary Iwasawa motions and the orbit map, using the manuscript's parameters.
Topological quotient identification and the angular parameter modulo 2π remain open.
-/
noncomputable section
open scoped MatrixGroups
open UpperHalfPlane
namespace TraceFormulas.Hyperbolic

def translation (x : ℝ) : RealGroup :=
  ⟨!![1, x; 0, 1], by simp⟩

def dilation (y : ℝ) (hy : 0 < y) : RealGroup :=
  ⟨!![Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹], by
    simp [ne_of_gt (Real.sqrt_pos.2 hy)]⟩

def rotation (θ : ℝ) : RealGroup :=
  ⟨!![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ], by
    simp only [Matrix.det_fin_two_of]
    nlinarith [Real.cos_sq_add_sin_sq θ]⟩

theorem translation_action (x : ℝ) (z : ℍ) :
    ((translation x • z : ℍ) : ℂ) = (z : ℂ) + x := by
  simp [action_formula, factor, translation]

theorem dilation_action (y : ℝ) (hy : 0 < y) (z : ℍ) :
    ((dilation y hy • z : ℍ) : ℂ) = (y : ℂ) * z := by
  have hs : ((Real.sqrt y : ℝ) : ℂ) ^ 2 = (y : ℂ) := by
    exact_mod_cast Real.sq_sqrt hy.le
  simp only [action_formula, dilation, factor, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.of_apply, Complex.ofReal_zero,
    Complex.ofReal_inv, mul_zero, zero_mul, zero_add, add_zero, div_inv_eq_mul]
  calc
    _ = ((Real.sqrt y : ℝ) : ℂ) ^ 2 * z := by ring
    _ = _ := by rw [hs]

theorem rotation_fixes_I (θ : ℝ) : rotation θ • UpperHalfPlane.I = UpperHalfPlane.I := by
  apply UpperHalfPlane.ext
  rw [action_formula]
  apply (div_eq_iff (factor_ne_zero (rotation θ) UpperHalfPlane.I)).2
  apply Complex.ext <;> simp [factor, rotation, UpperHalfPlane.coe_I]

/-- The actual triangular matrix that maps i to the given point. -/
def sectionMatrix (z : ℍ) : RealGroup := translation z.re * dilation z.im z.im_pos

theorem sectionMatrix_action (z w : ℍ) :
    ((sectionMatrix z • w : ℍ) : ℂ) = (z.re : ℂ) + (z.im : ℂ) * w := by
  rw [sectionMatrix, mul_smul, translation_action, dilation_action]
  exact add_comm _ _

/-- The inverse position matrix first subtracts x, then divides by y. -/
theorem sectionMatrix_inverse_action (z w : ℍ) :
    (((sectionMatrix z)⁻¹ • w : ℍ) : ℂ) =
      ((w : ℂ) - (z.re : ℂ)) / (z.im : ℂ) := by
  have h := sectionMatrix_action z ((sectionMatrix z)⁻¹ • w)
  rw [smul_inv_smul] at h
  have hy : (z.im : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt z.im_pos
  apply (eq_div_iff hy).2
  rw [mul_comm]
  exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans h.symm)

theorem sectionMatrix_smul_I (z : ℍ) : sectionMatrix z • UpperHalfPlane.I = z := by
  apply UpperHalfPlane.ext
  rw [sectionMatrix, mul_smul, translation_action, dilation_action]
  change (z.im : ℂ) * Complex.I + z.re = (z : ℂ)
  exact (add_comm _ _).trans (Complex.re_add_im (z : ℂ))

theorem transitive_action (z w : ℍ) : ∃ g : RealGroup, g • z = w := by
  refine ⟨sectionMatrix w * (sectionMatrix z)⁻¹, ?_⟩
  have hz : (sectionMatrix z)⁻¹ • z = UpperHalfPlane.I := by
    calc
      _ = (sectionMatrix z)⁻¹ • (sectionMatrix z • UpperHalfPlane.I) :=
        congrArg (fun w : ℍ => (sectionMatrix z)⁻¹ • w) (sectionMatrix_smul_I z).symm
      _ = _ := inv_smul_smul _ _
  rw [mul_smul, hz, sectionMatrix_smul_I]

/-- Equality of orbit points is precisely membership of the relative matrix in the stabilizer. -/
theorem same_point_iff_stabilizer (g h : RealGroup) :
    g • UpperHalfPlane.I = h • UpperHalfPlane.I ↔
      h⁻¹ * g ∈ MulAction.stabilizer RealGroup UpperHalfPlane.I := by
  rw [MulAction.mem_stabilizer_iff, mul_smul]
  constructor
  · intro heq
    rw [heq, inv_smul_smul]
  · intro heq
    have h' := congrArg (fun z : ℍ => h • z) heq
    simpa only [smul_inv_smul] using h'

/-- Every matrix factors as the chosen position matrix times a stabilizer element. -/
theorem position_stabilizer_factorization (g : RealGroup) :
    ∃ k : MulAction.stabilizer RealGroup UpperHalfPlane.I,
      g = sectionMatrix (g • UpperHalfPlane.I) * k := by
  let s := sectionMatrix (g • UpperHalfPlane.I)
  have hk : s⁻¹ * g ∈ MulAction.stabilizer RealGroup UpperHalfPlane.I := by
    apply (same_point_iff_stabilizer g s).mp
    exact (sectionMatrix_smul_I _).symm
  refine ⟨⟨s⁻¹ * g, hk⟩, ?_⟩
  change g = s * (s⁻¹ * g)
  simp


/-- The fixed-point equation for i is exactly the rotation-matrix entry condition. -/
theorem fixes_I_iff_entries (g : RealGroup) :
    g • UpperHalfPlane.I = UpperHalfPlane.I ↔
      g 0 0 = g 1 1 ∧ g 0 1 = -(g 1 0) := by
  rw [← UpperHalfPlane.ext_iff', action_formula,
    div_eq_iff (factor_ne_zero g UpperHalfPlane.I)]
  constructor
  · intro h
    have hr := congrArg Complex.re h
    have hi := congrArg Complex.im h
    simp [factor, UpperHalfPlane.coe_I] at hr hi
    exact ⟨hi, hr⟩
  · rintro ⟨ha, hb⟩
    apply Complex.ext <;> simp [factor, UpperHalfPlane.coe_I, ha, hb]

/-- This proves that every stabilizer element is one of the manuscript's rotations. -/
theorem fixes_I_iff_rotation (g : RealGroup) :
    g • UpperHalfPlane.I = UpperHalfPlane.I ↔ ∃ θ : ℝ, g = rotation θ := by
  constructor
  · intro h
    obtain ⟨ha, hb⟩ := (fixes_I_iff_entries g).mp h
    have hc : g 1 0 = -(g 0 1) := by linarith
    have hdet := g.property
    rw [Matrix.det_fin_two] at hdet
    have hu : g 0 0 * g 0 0 + g 0 1 * g 0 1 = 1 := by
      simpa [← ha, hc] using hdet
    let u : ℂ := ⟨g 0 0, g 0 1⟩
    have hn : ‖u‖ = 1 := by
      rw [Complex.norm_def]
      change Real.sqrt (g 0 0 * g 0 0 + g 0 1 * g 0 1) = 1
      rw [hu]
      norm_num
    have hcos := Complex.norm_mul_cos_arg u
    have hsin := Complex.norm_mul_sin_arg u
    simp only [hn, one_mul] at hcos hsin
    refine ⟨u.arg, ?_⟩
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change g i j = !![Real.cos u.arg, Real.sin u.arg; -Real.sin u.arg, Real.cos u.arg] i j
    rw [hcos, hsin]
    fin_cases i <;> fin_cases j <;> simp [u, ha, hc]
  · rintro ⟨θ, rfl⟩
    exact rotation_fixes_I θ

theorem iwasawa_existence (g : RealGroup) :
    ∃ θ : ℝ, g = translation (g • UpperHalfPlane.I).re *
      dilation (g • UpperHalfPlane.I).im (g • UpperHalfPlane.I).im_pos * rotation θ := by
  obtain ⟨k, hk⟩ := position_stabilizer_factorization g
  obtain ⟨θ, hθ⟩ := (fixes_I_iff_rotation (k : RealGroup)).mp k.property
  exact ⟨θ, by simpa [sectionMatrix, hθ] using hk⟩

/-- Coordinates of the orbit point, computed by complex division at i. -/
theorem base_point_coordinates (g : RealGroup) :
    (g • UpperHalfPlane.I).re =
        (g 0 0 * g 1 0 + g 0 1 * g 1 1) / ((g 1 0) ^ 2 + (g 1 1) ^ 2) ∧
    (g • UpperHalfPlane.I).im = 1 / ((g 1 0) ^ 2 + (g 1 1) ^ 2) := by
  constructor
  · change Complex.re ((g • UpperHalfPlane.I : ℍ) : ℂ) = _
    rw [action_formula]
    simp [factor, UpperHalfPlane.coe_I, Complex.div_re, Complex.normSq_apply, pow_two]
    ring
  · rw [action_im]
    simp [factor, UpperHalfPlane.coe_I, Complex.normSq_apply, pow_two]
    ring

theorem nak_smul_I (x y : ℝ) (hy : 0 < y) (θ : ℝ) :
    (((translation x * dilation y hy * rotation θ) • UpperHalfPlane.I : ℍ) : ℂ) =
      (x : ℂ) + (y : ℂ) * Complex.I := by
  rw [mul_smul, rotation_fixes_I, mul_smul, translation_action, dilation_action]
  simpa only [UpperHalfPlane.coe_I] using add_comm ((y : ℂ) * Complex.I) (x : ℂ)

/-- Equality of NAK factorizations determines x, y and the actual rotation matrix. -/
theorem iwasawa_unique (x x' y y' : ℝ) (hy : 0 < y) (hy' : 0 < y') (θ θ' : ℝ)
    (h : translation x * dilation y hy * rotation θ =
      translation x' * dilation y' hy' * rotation θ') :
    x = x' ∧ y = y' ∧ rotation θ = rotation θ' := by
  have hp := congrArg (fun g : RealGroup => ((g • UpperHalfPlane.I : ℍ) : ℂ)) h
  dsimp only at hp
  rw [nak_smul_I, nak_smul_I] at hp
  have hx : x = x' := by simpa using congrArg Complex.re hp
  have hy_eq : y = y' := by simpa using congrArg Complex.im hp
  refine ⟨hx, hy_eq, ?_⟩
  subst x'
  subst y'
  exact mul_left_cancel h

end TraceFormulas.Hyperbolic

