import TraceFormulas.Geometry.Iwasawa

/-! The diagonal-factor step in the unimodularity argument.
The modular function itself and full unimodularity remain separate obligations.
-/
noncomputable section
namespace TraceFormulas.Hyperbolic

/-- Conjugation by the quarter-turn swaps the two diagonal entries. -/
theorem quarter_turn_conjugates_dilation (y : ℝ) (hy : 0 < y) :
    rotation (Real.pi / 2) * dilation y hy * (rotation (Real.pi / 2))⁻¹ =
      (dilation y hy)⁻¹ := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation, dilation, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- A positive real number equal to its reciprocal is one. -/
theorem positive_eq_one_of_eq_inv {x : ℝ} (hx : 0 < x) (h : x = x⁻¹) : x = 1 := by
  have hs : x ^ 2 = 1 := by
    calc
      x ^ 2 = x * x := pow_two x
      _ = x * x⁻¹ := congrArg (x * ·) h
      _ = 1 := mul_inv_cancel₀ (ne_of_gt hx)
  rcases sq_eq_one_iff.mp hs with heq | heq
  · exact heq
  · linarith

/-- A positive character is one on an element conjugate to its inverse. -/
theorem character_eq_one_of_conjugate_inverse {L : Type*} [Group L]
    (χ : L →* ℝˣ) (g h : L) (hpos : 0 < (χ g : ℝ))
    (hconj : h * g * h⁻¹ = g⁻¹) : χ g = 1 := by
  have hinv : χ g = (χ g)⁻¹ := by
    simpa [map_mul, map_inv, mul_comm, mul_left_comm, mul_assoc] using congrArg χ hconj
  apply Units.ext
  apply positive_eq_one_of_eq_inv hpos
  simpa only [Units.val_inv_eq_inv_val] using congrArg Units.val hinv

/-- The diagonal factor has trivial value for every positive real character. -/
theorem positive_character_dilation (χ : RealGroup →* ℝˣ)
    (hpos : ∀ g, 0 < (χ g : ℝ)) (y : ℝ) (hy : 0 < y) :
    χ (dilation y hy) = 1 :=
  character_eq_one_of_conjugate_inverse χ (dilation y hy) (rotation (Real.pi / 2))
    (hpos _) (quarter_turn_conjugates_dilation y hy)

end TraceFormulas.Hyperbolic
