import Mathlib.NumberTheory.Modular
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices

/-!
# The modular generators as row operations

Use Mathlib's integral special linear group and its actual action on the upper
half-plane. These computations support the manuscript's Euclidean reduction.
-/
open scoped MatrixGroups
open Matrix ModularGroup
namespace TraceFormulas.ModularDomain

theorem S_rows (g : SL(2, ℤ)) :
    ((S * g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![-g 1 0, -g 1 1; g 0 0, g 0 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SpecialLinearGroup.coe_mul, coe_S, Matrix.mul_apply, Fin.sum_univ_two]

theorem T_power_rows (q : ℤ) (g : SL(2, ℤ)) :
    ((T ^ q * g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![g 0 0 + q * g 1 0, g 0 1 + q * g 1 1; g 1 0, g 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SpecialLinearGroup.coe_mul, coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two]

theorem S_square : (S : SL(2, ℤ)) ^ 2 = -1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pow_succ, SpecialLinearGroup.coe_mul, coe_S,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem ST_cube : ((S * T : SL(2, ℤ)) ^ 3) = -1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pow_succ, SpecialLinearGroup.coe_mul, coe_S, coe_T,
      Matrix.mul_apply, Fin.sum_univ_two]

end TraceFormulas.ModularDomain
