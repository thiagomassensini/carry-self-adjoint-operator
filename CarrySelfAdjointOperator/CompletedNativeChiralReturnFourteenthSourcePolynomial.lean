import CarrySelfAdjointOperator.CompletedNativeChiralReturnSevenBoundaryFace

/-! Exact polynomial of the original seven-coordinate source discriminant.
No matrix, canonical moment or new metric is used. The coefficients follow
from the source product-rule recurrence; the identity is checked by ring. -/
namespace CarrySelfAdjointOperator
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 8192

def nativeSourceFourteenthMixedNumerator (a b c d e f g h : ℝ) : ℝ :=
  (48510:ℝ)*(a^3*b*d*f*h) +
  (-68796:ℝ)*(a^3*b*d*g^2) +
  (-83160:ℝ)*(a^3*b*e^2*h) +
  (360360:ℝ)*(a^3*b*e*f*g) +
  (-275275:ℝ)*(a^3*b*f^3) +
  (-161700:ℝ)*(a^3*c^2*f*h) +
  (229320:ℝ)*(a^3*c^2*g^2) +
  (1164240:ℝ)*(a^3*c*d*e*h) +
  (-2522520:ℝ)*(a^3*c*d*f*g) +
  (-4324320:ℝ)*(a^3*c*e^2*g) +
  (6606600:ℝ)*(a^3*c*e*f^2) +
  (-1222452:ℝ)*(a^3*d^3*h) +
  (9081072:ℝ)*(a^3*d^2*e*g) +
  (6936930:ℝ)*(a^3*d^2*f^2) +
  (-35675640:ℝ)*(a^3*d*e^2*f) +
  (20386080:ℝ)*(a^3*e^4) +
  (242550:ℝ)*(a^2*b^2*c*f*h) +
  (-343980:ℝ)*(a^2*b^2*c*g^2) +
  (-1018710:ℝ)*(a^2*b^2*d*e*h) +
  (2144142:ℝ)*(a^2*b^2*d*f*g) +
  (4324320:ℝ)*(a^2*b^2*e^2*g) +
  (-6441435:ℝ)*(a^2*b^2*e*f^2) +
  (-4365900:ℝ)*(a^2*b*c^2*e*h) +
  (9669660:ℝ)*(a^2*b*c^2*f*g) +
  (12224520:ℝ)*(a^2*b*c*d^2*h) +
  (-30270240:ℝ)*(a^2*b*c*d*e*g) +
  (-101741640:ℝ)*(a^2*b*c*d*f^2) +
  (130810680:ℝ)*(a^2*b*c*e^2*f) +
  (-79459380:ℝ)*(a^2*b*d^3*g) +
  (461999538:ℝ)*(a^2*b*d^2*e*f) +
  (-428107680:ℝ)*(a^2*b*d*e^3) +
  (-6791400:ℝ)*(a^2*c^3*d*h) +
  (75675600:ℝ)*(a^2*c^3*e*g) +
  (-69369300:ℝ)*(a^2*c^3*f^2) +
  (291351060:ℝ)*(a^2*c^2*d*e*f) +
  (-713512800:ℝ)*(a^2*c^2*e^3) +
  (-524431908:ℝ)*(a^2*c*d^3*f) +
  (1498376880:ℝ)*(a^2*c*d^2*e^2) +
  (-524431908:ℝ)*(a^2*d^4*e) +
  (6548850:ℝ)*(a*b^3*c*e*h) +
  (-14504490:ℝ)*(a*b^3*c*f*g) +
  (-16299360:ℝ)*(a*b^3*d^2*h) +
  (69999930:ℝ)*(a*b^3*d*e*g) +
  (88792704:ℝ)*(a*b^3*d*f^2) +
  (-173918745:ℝ)*(a*b^3*e^2*f) +
  (10187100:ℝ)*(a*b^2*c^2*d*h) +
  (-397296900:ℝ)*(a*b^2*c^2*e*g) +
  (548017470:ℝ)*(a*b^2*c^2*f^2) +
  (794593800:ℝ)*(a*b^2*c*d^2*g) +
  (-4786481700:ℝ)*(a*b^2*c*d*e*f) +
  (4816211400:ℝ)*(a*b^2*c*e^3) +
  (-374594220:ℝ)*(a*b^2*d^2*e^2) +
  (-441441000:ℝ)*(a*b*c^3*d*g) +
  (1456755300:ℝ)*(a*b*c^3*e*f) +
  (5244319080:ℝ)*(a*b*c^2*d^2*f) +
  (-12486474000:ℝ)*(a*b*c^2*d*e^2) +
  (5244319080:ℝ)*(a*b*c*d^3*e) +
  (-2913510600:ℝ)*(a*c^4*d*f) +
  (6243237000:ℝ)*(a*c^4*e^2) +
  (-2913510600:ℝ)*(a*c^3*d^2*e) +
  (425675250:ℝ)*(b^4*c*e*g) +
  (-665945280:ℝ)*(b^4*c*f^2) +
  (-1059458400:ℝ)*(b^4*d^2*g) +
  (5993507520:ℝ)*(b^4*d*e*f) +
  (-5418237825:ℝ)*(b^4*e^3) +
  (662161500:ℝ)*(b^3*c^2*d*g) +
  (-2185132950:ℝ)*(b^3*c^2*e*f) +
  (-6992425440:ℝ)*(b^3*c*d^2*f) +
  (16856739900:ℝ)*(b^3*c*d*e^2) +
  (-6992425440:ℝ)*(b^3*d^3*e) +
  (4370265900:ℝ)*(b^2*c^3*d*f) +
  (-9364855500:ℝ)*(b^2*c^3*e^2) +
  (4370265900:ℝ)*(b^2*c^2*d^2*e)

theorem nativeSourceSevenEvenDiscriminant_integral_formula :
    nativeSourceSevenEvenDiscriminant =
      nativeSourceFourteenthMixedNumerator
        (completedNativeXiCosineMoment 0) (completedNativeXiCosineMoment 1)
        (completedNativeXiCosineMoment 2) (completedNativeXiCosineMoment 3)
        (completedNativeXiCosineMoment 4) (completedNativeXiCosineMoment 5)
        (completedNativeXiCosineMoment 6) (completedNativeXiCosineMoment 7) /
        (13153940405570764800000 * completedNativeXiCosineMoment 0^7) := by
  obtain ⟨h0,h1,h2,h3⟩ := nativeSourceOddBoundaryCoefficient_integral_formulas
  unfold nativeSourceSevenEvenDiscriminant nativeSourceSevenEvenCoupling0
    nativeSourceSevenEvenCoupling1 nativeSourceSevenEvenCoupling2 nativeSourceFiveEvenDiscriminant
  rw [h0,h1,h2,h3, nativeSourceOddBoundaryCoefficient_four_integral_formula,
    nativeSourceOddBoundaryCoefficient_five_integral_formula,
    nativeSourceOddBoundaryCoefficient_six_integral_formula]
  unfold nativeSourceFourteenthMixedNumerator nativeSourceSeventhNumerator nativeSourceNinthNumerator
    nativeSourceEleventhNumerator nativeSourceThirteenthNumerator
  field_simp [(completedNativeXiCosineMoment_pos 0).ne']
  ring
end
end CarrySelfAdjointOperator
