import CarrySelfAdjointOperator.NativeScalarGenuineIdentification
import Mathlib.Tactic

/-!
# Direct carry-native Schwarz reflection

This second proof works directly on the native bracket series.  Every
Dirichlet base is a nonnegative real integer, so conjugation commutes with
each value, center block, seed, convergent series, camera factor, and native
quotient.  The literal native/Genuine identification then transports the
same identity to the Genuine continuation.
-/

open scoped BigOperators

namespace CarrySelfAdjointOperator

open Complex
open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Camera

noncomputable section

theorem dirichletValue_conj_from_nativeBase (s : ℂ) (n : ℕ) :
    dirichletValue ((starRingEnd ℂ) s) n =
      (starRingEnd ℂ) (dirichletValue s n) := by
  have harg : (((n : ℕ) : ℂ)).arg ≠ Real.pi := by
    rw [← Complex.ofReal_natCast]
    rw [Complex.arg_ofReal_of_nonneg (by positivity)]
    exact Real.pi_pos.ne
  rw [dirichletValue, dirichletValue,
    show -((starRingEnd ℂ) s) = (starRingEnd ℂ) (-s) by simp,
    Complex.cpow_conj _ _ harg, map_natCast]

theorem centeredBracketTerm_conj_from_nativeGeometry
    (s : ℂ) (center radius : ℕ) :
    centeredBracketTerm ((starRingEnd ℂ) s) center radius =
      (starRingEnd ℂ) (centeredBracketTerm s center radius) := by
  simp [centeredBracketTerm, dirichletValue_conj_from_nativeBase,
    map_sub, map_add, map_mul, map_ofNat]

theorem centerBracketTerm_conj_from_nativeGeometry
    (camera index : ℕ) (s : ℂ) :
    centerBracketTerm camera ((starRingEnd ℂ) s) index =
      (starRingEnd ℂ) (centerBracketTerm camera s index) := by
  unfold centerBracketTerm
  split_ifs
  · exact centeredBracketTerm_conj_from_nativeGeometry s _ _
  · rw [map_sum]
    apply Finset.sum_congr rfl
    intro radius _
    exact centeredBracketTerm_conj_from_nativeGeometry s _ _

theorem seedDirichletTerm_conj_from_nativeGeometry
    (camera : ℕ) (s : ℂ) :
    seedDirichletTerm camera ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (seedDirichletTerm camera s) := by
  unfold seedDirichletTerm
  split_ifs
  · exact dirichletValue_conj_from_nativeBase s 1
  · rw [map_sum]
    apply Finset.sum_congr rfl
    intro radius _
    exact dirichletValue_conj_from_nativeBase s radius

/-- Direct termwise Schwarz reflection of every native bracket series. -/
theorem bracketCharacteristic_conj_from_nativeSeries
    (camera : ℕ) (s : ℂ) :
    bracketCharacteristic camera ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (bracketCharacteristic camera s) := by
  rw [bracketCharacteristic, bracketCharacteristic, map_add, conj_tsum,
    seedDirichletTerm_conj_from_nativeGeometry]
  congr 1
  exact tsum_congr
    (fun index => centerBracketTerm_conj_from_nativeGeometry camera index s)

theorem factor_three_conj_from_nativeGeometry (s : ℂ) :
    factor 3 ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (factor 3 s) := by
  rw [factor_of_odd (by norm_num : 3 ≠ 2) (by norm_num : Odd 3),
    factor_of_odd (by norm_num : 3 ≠ 2) (by norm_num : Odd 3)]
  unfold oddFactor
  have harg : (((3 : ℕ) : ℂ)).arg ≠ Real.pi := by
    rw [← Complex.ofReal_natCast]
    rw [Complex.arg_ofReal_of_nonneg (by positivity)]
    exact Real.pi_pos.ne
  have hexponent :
      (1 : ℂ) - (starRingEnd ℂ) s =
        (starRingEnd ℂ) ((1 : ℂ) - s) := by simp
  rw [hexponent, Complex.cpow_conj _ _ harg, map_natCast,
    map_sub, map_one]

/-- Direct Schwarz reflection of the native scalar, with no domain or
arithmetic hypothesis. -/
theorem nativeScalar_conj_from_nativeSeries (s : ℂ) :
    nativeScalar ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (nativeScalar s) := by
  rw [nativeScalar, nativeScalar,
    bracketCharacteristic_conj_from_nativeSeries,
    factor_three_conj_from_nativeGeometry, map_div₀]

/-- Direct Schwarz reflection transported to the Genuine presentation. -/
theorem genuineContinuation_conj_from_nativeSeries (s : ℂ) :
    genuineContinuation ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (genuineContinuation s) := by
  rw [← nativeScalar_eq_genuineContinuation_unconditional,
    ← nativeScalar_eq_genuineContinuation_unconditional,
    nativeScalar_conj_from_nativeSeries]

end

end CarrySelfAdjointOperator
