import CarrySelfAdjointOperator.NativeIncidenceCauchyPorts
import CarrySelfAdjointOperator.CompletedNativeChiralReturnGreenBoundaryTower

namespace CarrySelfAdjointOperator.NativeCauchyPorts
open NativeCarrySpectralWeyl.Camera.FiniteBridge
open CPFormal.Analytic.Cp ChiralReturn MaterialCameraJets FiniteClockJets MeasureTheory
open scoped BigOperators unitInterval
noncomputable section
set_option autoImplicit false

/-- Polynomial part of the radial half-density, evaluated in a real variable. -/
def radialRealRepresentative (k j : ℕ) (u : ℝ) : ℝ :=
  Real.sqrt ((k : ℝ)+1) * Real.sqrt u * u^j

/-- This derivative certifies the half-density offset, rather than assuming
that the OLD formal degree jet is its derivative. -/
theorem radialRealRepresentative_derivative_one (k j : ℕ) :
    HasDerivAt (radialRealRepresentative k j)
      (Real.sqrt ((k : ℝ)+1) * ((j : ℝ)+1/2)) 1 := by
  have h := ((Real.hasDerivAt_sqrt (by norm_num : (1 : ℝ) ≠ 0)).mul
    ((hasDerivAt_id (1 : ℝ)).pow j)).const_mul (Real.sqrt ((k : ℝ)+1))
  have h' : HasDerivAt (fun u => Real.sqrt ((k : ℝ)+1) * (Real.sqrt u * u^j))
      (Real.sqrt ((k : ℝ)+1) * ((j : ℝ)+1/2)) 1 := by
    simpa [add_comm] using h
  have hf : (fun u => Real.sqrt ((k : ℝ)+1) * (Real.sqrt u * u^j)) =
      radialRealRepresentative k j := by
    funext u
    dsimp [radialRealRepresentative]
    ring
  rw [hf] at h'
  exact h' 

/-- Real representative of the original positive-position centered stencil. -/
def nativeBracketRealRepresentative (k p r : ℕ) (u : ℝ) : ℝ :=
  radialRealRepresentative k p u - 2*radialRealRepresentative k (p+r) u +
    radialRealRepresentative k (p+2*r) u

theorem nativeBracket_profile_realRepresentative (k p r : ℕ) (u : unitInterval) :
    nativeStencilCauchyProfile k (centeredBracketStencil (p+r+1) r) u =
      (nativeBracketRealRepresentative k p r (u : ℝ) : ℂ) := by
  rw [nativeBracket_profile_factor]
  simp [radialContinuousState, completedNativeChiralCauchyContinuousFeature,
    intervalCoordinate, nativeBracketRealRepresentative, radialRealRepresentative, pow_add, pow_mul]
  ring

theorem nativeBracket_derivative_one (k p r : ℕ) :
    HasDerivAt (nativeBracketRealRepresentative k p r) 0 1 := by
  have h := ((radialRealRepresentative_derivative_one k p).sub
    ((radialRealRepresentative_derivative_one k (p+r)).const_mul 2)).add
      (radialRealRepresentative_derivative_one k (p+2*r))
  change HasDerivAt (nativeBracketRealRepresentative k p r) _ 1 at h
  exact h.congr_deriv (by push_cast; ring)

/-- Bulk is an explicit finite geometric polynomial, on the SAME continuous
carrier, with no Green identification implicit in its definition. -/
def nativeBracketCauchyBulk (k p r : ℕ) : C(unitInterval, ℂ) :=
  radialContinuousState k p * (∑ q ∈ Finset.range r, intervalCoordinate^q)^2

theorem nativeBracket_profile_bulk (k p r : ℕ) :
    nativeStencilCauchyProfile k (centeredBracketStencil (p+r+1) r) =
      (1-intervalCoordinate)^2 * nativeBracketCauchyBulk k p r := by
  rw [nativeBracket_profile_factor]
  have h : 1-intervalCoordinate^r =
      (1-intervalCoordinate)*(∑ q ∈ Finset.range r, intervalCoordinate^q) := by
    have hg := mul_geom_sum intervalCoordinate r
    linear_combination hg
  rw [h]
  unfold nativeBracketCauchyBulk
  ring

/-- Unscaled endpoint traces of the MATERIAL-clocked incidence.
The first component uses log(position), not log(interval coordinate). -/
def bracketMaterialClockTraces (c r : ℝ) : ℝ × ℝ :=
  (Real.log (c-r)-2*Real.log c+Real.log (c+r),
   (c-r-1/2)*Real.log (c-r)-2*(c-1/2)*Real.log c+(c+r-1/2)*Real.log (c+r))

theorem bracketClock_value_closed (c r : ℝ) (hc : 0<c) (hr : 0≤r) (hrc : r<c) :
    (bracketMaterialClockTraces c r).1 = Real.log (1-r^2/c^2) := by
  have hm : c-r ≠ 0 := (sub_pos.mpr hrc).ne'
  have hp : c+r ≠ 0 := (by positivity : 0<c+r).ne'
  have he : 1-r^2/c^2 = (c-r)*(c+r)/(c*c) := by field_simp; ring
  rw [he, Real.log_div (mul_ne_zero hm hp) (mul_ne_zero hc.ne' hc.ne'),
    Real.log_mul hm hp, Real.log_mul hc.ne' hc.ne']
  simp only [bracketMaterialClockTraces]
  ring

theorem bracketClock_derivative_closed (c r : ℝ) (hc : 0<c) (hr : 0≤r) (hrc : r<c) :
    (bracketMaterialClockTraces c r).2 =
      (c-1/2)*(bracketMaterialClockTraces c r).1 + r*Real.log ((c+r)/(c-r)) := by
  rw [Real.log_div (by positivity : c+r ≠ 0) ((sub_pos.mpr hrc).ne')]
  simp only [bracketMaterialClockTraces]
  ring

/-- A nondegenerate material bracket develops a strictly negative zeroth
boundary trace after clocking. No sign of the chiral energy is inferred. -/
theorem bracketClock_value_neg (c r : ℝ) (hr : 0<r) (hrc : r<c) :
    (bracketMaterialClockTraces c r).1 < 0 := by
  rw [bracketClock_value_closed c r (hr.trans hrc) hr.le hrc]
  apply Real.log_neg
  · have hcs : 0<c^2 := sq_pos_of_pos (hr.trans hrc)
    have hrs : r^2<c^2 := by nlinarith
    exact sub_pos.mpr ((div_lt_one hcs).mpr hrs)
  · have hp : 0<r^2/c^2 := div_pos (sq_pos_of_pos hr) (sq_pos_of_pos (hr.trans hrc))
    linarith

/-- Direct positive-index finite Cauchy synthesis, independently of U. -/
def finiteMaterialCauchyProfile (k N : ℕ) (x : FiniteRealSpectralHilbert N) : C(unitInterval, ℂ) :=
  ∑ i : Fin N, x i • radialContinuousState k i

/-- Finite physical nodal synthesis agrees with the existing undressed
incident synthesis; it does NOT identify it with the completed source. -/
theorem finiteMaterialCauchyProfile_toLp (k N : ℕ) (x : FiniteRealSpectralHilbert N) :
    ContinuousMap.toLp 2 volume ℂ (finiteMaterialCauchyProfile k N x) =
      radialIncidentSynthesis k N (fun i => x i) := by
  simp [finiteMaterialCauchyProfile, radialIncidentSynthesis, radialContinuousState_toLp]

/-- Endpoint after applying the ORIGINAL materialJet action. -/
theorem finiteMaterialCauchyProfile_clock_trace (k N : ℕ) (x : FiniteRealSpectralHilbert N) :
    finiteMaterialCauchyProfile k N (materialJet 1 x) 1 =
      (Real.sqrt ((k : ℝ)+1) : ℂ) *
        ∑ i : Fin N, (Real.log ((i.val+1 : ℕ) : ℝ) : ℂ) * x i := by
  simp [finiteMaterialCauchyProfile, materialJet_apply, finiteRealSpectralFrequency,
    radialContinuousState, completedNativeChiralCauchyContinuousFeature]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The existing degree jet has offset +1. The true half-density derivative
has offset +1/2; the discrepancy is half the zeroth boundary trace. -/
theorem radialHalfDensityTrace_eq_degreeJet_sub_half {N : ℕ} (d : Fin N → ℂ) :
    (∑ i, d i * ((i.val : ℂ)+1/2)) =
      radialEulerBoundaryJet d 1 - (1/2 : ℂ)*radialEulerBoundaryJet d 0 := by
  simp only [radialEulerBoundaryJet, pow_one, pow_zero, mul_one,
    Nat.cast_add, Nat.cast_one, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Minimal physical centered bracket (positions 1,2,3). -/
def firstNativeBracket : FiniteRealSpectralHilbert 3 := WithLp.toLp 2 ![1,-2,1]

theorem firstNativeBracket_clock_trace (k : ℕ) :
    finiteMaterialCauchyProfile k 3 (materialJet 1 firstNativeBracket) 1 =
      (Real.sqrt ((k : ℝ)+1) : ℂ) * (Real.log (3/4 : ℝ) : ℂ) := by
  rw [finiteMaterialCauchyProfile_clock_trace]
  have hl : Real.log (3/4 : ℝ) = Real.log 3 - 2*Real.log 2 := by
    rw [Real.log_div (by norm_num : (3 : ℝ) ≠ 0) (by norm_num : (4 : ℝ) ≠ 0)]
    rw [show (4 : ℝ) = 2*2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [hl]
  norm_num [Fin.sum_univ_succ, firstNativeBracket]
  left
  ring

/-- Precise boundary obstruction: clocking the smallest native incidence
leaves the kernel of endpoint evaluation. -/
theorem firstNativeBracket_clock_trace_ne_zero (k : ℕ) :
    finiteMaterialCauchyProfile k 3 (materialJet 1 firstNativeBracket) 1 ≠ 0 := by
  rw [firstNativeBracket_clock_trace]
  apply mul_ne_zero
  · exact_mod_cast (Real.sqrt_pos.mpr (by positivity : (0 : ℝ)<(k : ℝ)+1)).ne'
  · exact_mod_cast (Real.log_neg (by norm_num : (0 : ℝ)<3/4) (by norm_num : (3/4 : ℝ)<1)).ne


/-- Literal clocked representative on positive native positions. These
weights are log(position), independent of the interval variable u. -/
def clockedBracketRealRepresentative (k p r : ℕ) (u : ℝ) : ℝ :=
  Real.log ((p+1 : ℕ) : ℝ) * radialRealRepresentative k p u -
    2*Real.log ((p+r+1 : ℕ) : ℝ)*radialRealRepresentative k (p+r) u +
    Real.log ((p+2*r+1 : ℕ) : ℝ)*radialRealRepresentative k (p+2*r) u

theorem clockedBracket_value_one (k p r : ℕ) :
    clockedBracketRealRepresentative k p r 1 =
      Real.sqrt ((k : ℝ)+1) * (bracketMaterialClockTraces ((p+r+1 : ℕ) : ℝ) r).1 := by
  have hl : ((p+r+1 : ℕ) : ℝ) - (r : ℝ) = ((p+1 : ℕ) : ℝ) := by push_cast; ring
  have hr : ((p+r+1 : ℕ) : ℝ) + (r : ℝ) = ((p+2*r+1 : ℕ) : ℝ) := by push_cast; ring
  simp only [bracketMaterialClockTraces, hl, hr]
  simp [clockedBracketRealRepresentative, radialRealRepresentative]
  ring

theorem clockedBracket_derivative_one (k p r : ℕ) :
    HasDerivAt (clockedBracketRealRepresentative k p r)
      (Real.sqrt ((k : ℝ)+1) * (bracketMaterialClockTraces ((p+r+1 : ℕ) : ℝ) r).2) 1 := by
  have h := (((radialRealRepresentative_derivative_one k p).const_mul
    (Real.log ((p+1 : ℕ) : ℝ))).sub
    ((radialRealRepresentative_derivative_one k (p+r)).const_mul
      (2*Real.log ((p+r+1 : ℕ) : ℝ)))).add
      ((radialRealRepresentative_derivative_one k (p+2*r)).const_mul
        (Real.log ((p+2*r+1 : ℕ) : ℝ)))
  change HasDerivAt (clockedBracketRealRepresentative k p r) _ 1 at h
  apply h.congr_deriv
  have hl : ((p+r+1 : ℕ) : ℝ) - (r : ℝ) = ((p+1 : ℕ) : ℝ) := by push_cast; ring
  have hr : ((p+r+1 : ℕ) : ℝ) + (r : ℝ) = ((p+2*r+1 : ℕ) : ℝ) := by push_cast; ring
  simp only [bracketMaterialClockTraces, hl, hr]
  push_cast
  ring

/-- Exact positive-variable defect against multiplication by log(u). No
infinite-domain log(u) operator or new Hilbert metric is introduced. -/
theorem clockedBracket_logCoordinate_defect (k p r : ℕ) (u : ℝ) :
    clockedBracketRealRepresentative k p r u -
      Real.log u * nativeBracketRealRepresentative k p r u =
      (Real.log ((p+1 : ℕ) : ℝ)-Real.log u)*radialRealRepresentative k p u -
      2*(Real.log ((p+r+1 : ℕ) : ℝ)-Real.log u)*radialRealRepresentative k (p+r) u +
      (Real.log ((p+2*r+1 : ℕ) : ℝ)-Real.log u)*radialRealRepresentative k (p+2*r) u := by
  unfold clockedBracketRealRepresentative nativeBracketRealRepresentative
  ring

/-- The minimal clocked representative is actually produced by materialJet,
not chosen as a synthetic logarithmic stencil. -/
theorem firstNativeBracket_clock_realRepresentative (k : ℕ) (u : unitInterval) :
    finiteMaterialCauchyProfile k 3 (materialJet 1 firstNativeBracket) u =
      (clockedBracketRealRepresentative k 0 1 (u : ℝ) : ℂ) := by
  simp [finiteMaterialCauchyProfile, materialJet_apply, finiteRealSpectralFrequency,
    firstNativeBracket, Fin.sum_univ_succ, radialContinuousState,
    completedNativeChiralCauchyContinuousFeature, clockedBracketRealRepresentative,
    radialRealRepresentative]
  norm_num only
  rw [Complex.ofReal_log (by norm_num : (0 : ℝ)≤2),
    Complex.ofReal_log (by norm_num : (0 : ℝ)≤3)]
  simp only [Complex.ofReal_ofNat]
  ring

/-- In the ORIGINAL Lp metric, the clocked minimal bracket cannot equal a
finite three-node profile in the zero endpoint-trace kernel. -/
theorem firstNativeBracket_clock_no_boundaryZero_profile (k : ℕ)
    (y : FiniteRealSpectralHilbert 3) (hy : finiteMaterialCauchyProfile k 3 y 1 = 0) :
    ContinuousMap.toLp 2 volume ℂ (finiteMaterialCauchyProfile k 3 (materialJet 1 firstNativeBracket)) ≠
      ContinuousMap.toLp 2 volume ℂ (finiteMaterialCauchyProfile k 3 y) := by
  intro he
  rw [finiteMaterialCauchyProfile_toLp, finiteMaterialCauchyProfile_toLp] at he
  have hd := radialIncidentSynthesis_injective k 3 he
  have hx : materialJet 1 firstNativeBracket = y := by
    ext i
    exact congrFun hd i
  have ht := congrArg (fun z => finiteMaterialCauchyProfile k 3 z 1) hx
  exact firstNativeBracket_clock_trace_ne_zero k (ht.trans hy)

end
end CarrySelfAdjointOperator.NativeCauchyPorts
