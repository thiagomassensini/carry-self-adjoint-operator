import CarrySelfAdjointOperator.CompletedNativeC2ExactTailTransport
import CarrySelfAdjointOperator.CompletedNativeTfvdWronskianMoments
import CarrySelfAdjointOperator.C2SourceFormErrorTransport
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

open Filter
open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Camera

namespace CarrySelfAdjointOperator

noncomputable section

/-! ## The even projection as an exact repartition -/

/-- Projection of a complex germ onto its even part. -/
def c2EvenProjection : (ℂ → ℂ) →ₗ[ℂ] (ℂ → ℂ) where
  toFun f z := (f z + f (-z)) / 2
  map_add' f g := by
    funext z
    change ((f z + g z) + (f (-z) + g (-z))) / 2 =
      (f z + f (-z)) / 2 + (g z + g (-z)) / 2
    ring
  map_smul' c f := by
    funext z
    change (c * f z + c * f (-z)) / 2 =
      c * ((f z + f (-z)) / 2)
    ring

@[simp] theorem c2EvenProjection_apply (f : ℂ → ℂ) (z : ℂ) :
    c2EvenProjection f z = (f z + f (-z)) / 2 := rfl

/-- The even projection is idempotent. -/
theorem c2EvenProjection_idempotent (f : ℂ → ℂ) :
    c2EvenProjection (c2EvenProjection f) = c2EvenProjection f := by
  funext z
  simp [c2EvenProjection_apply]
  ring

/-- Every projected function is even, as a pointwise identity. -/
theorem c2EvenProjection_eventually_even (f : ℂ → ℂ) :
    (fun z : ℂ => c2EvenProjection f (-z)) =ᶠ[nhds 0]
      c2EvenProjection f := by
  filter_upwards [] with z
  simp [c2EvenProjection_apply]
  ring

/-- If a source splits locally as head plus tail and the whole source is
locally even, applying the projection repartitions that same local source as
the even head plus the even tail. -/
theorem c2EvenProjection_repartitions_eventually
    {F H T : ℂ → ℂ}
    (hsplit : F =ᶠ[nhds 0] fun z => H z + T z)
    (hEven : (fun z => F (-z)) =ᶠ[nhds 0] F) :
    F =ᶠ[nhds 0] fun z => c2EvenProjection H z + c2EvenProjection T z := by
  have hsplitNeg : (fun z : ℂ => F (-z)) =ᶠ[nhds 0]
      fun z => H (-z) + T (-z) := by
    have hneg : Tendsto (fun z : ℂ => -z) (nhds 0) (nhds 0) := by
      simpa using (continuous_neg.continuousAt (x := (0 : ℂ))).tendsto
    simpa [Function.comp_def] using hsplit.comp_tendsto hneg
  filter_upwards [hEven, hsplit, hsplitNeg] with z hpar hheadTail hheadTailNeg
  calc
    F z = (F z + F (-z)) / 2 := by rw [hpar]; ring
    _ = ((H z + T z) + (H (-z) + T (-z))) / 2 := by
      rw [hheadTail, hheadTailNeg]
    _ = c2EvenProjection H z + c2EvenProjection T z := by
      simp only [c2EvenProjection_apply]
      ring

/-! ## Derivatives and logarithmic responses -/

/-- Differentiating the projected head differentiates its two reflected
legs with opposite signs. -/
theorem c2EvenProjection_hasDerivAt
    (H : ℂ → ℂ) (z a b : ℂ)
    (hAt : HasDerivAt H a z)
    (hAtNeg : HasDerivAt H b (-z)) :
    HasDerivAt (c2EvenProjection H) ((a - b) / 2) z := by
  have hReflected : HasDerivAt (fun w : ℂ => H (-w)) (-b) z := by
    simpa [Function.comp_def] using hAtNeg.comp z (hasDerivAt_neg z)
  have hsum : HasDerivAt (fun w : ℂ => H w + H (-w)) (a - b) z := by
    have hfun : (H + fun w : ℂ => H (-w)) =
        fun w : ℂ => H w + H (-w) := by
      funext w
      rfl
    rw [← hfun]
    simpa [sub_eq_add_neg] using hAt.add hReflected
  change HasDerivAt (fun w : ℂ => (H w + H (-w)) / 2) ((a - b) / 2) z
  simpa using hsum.div_const (2 : ℂ)

/-- The projected companion is the negative of that derivative. -/
theorem c2EvenProjection_companion_eq_neg_deriv
    (H : ℂ → ℂ) (z a b : ℂ)
    (hAt : HasDerivAt H a z)
    (hAtNeg : HasDerivAt H b (-z)) :
    -deriv (c2EvenProjection H) z = -((a - b) / 2) := by
  rw [(c2EvenProjection_hasDerivAt H z a b hAt hAtNeg).deriv]

/-- The logarithmic derivative of a function. -/
def c2LogDerivative (f : ℂ → ℂ) : ℂ → ℂ := fun z => deriv f z / f z

/-- The logarithmic derivative of an analytic germ is analytic when its
center value is explicitly nonzero. -/
theorem c2LogDerivative_analyticAt
    (f : ℂ → ℂ)
    (hAnalytic : AnalyticAt ℂ f 0)
    (h0 : f 0 ≠ 0) :
    AnalyticAt ℂ (c2LogDerivative f) 0 := by
  change AnalyticAt ℂ (deriv f / f) 0
  exact hAnalytic.deriv.div hAnalytic h0

/-- The logarithmic derivative of an even germ is odd as a germ. -/
theorem c2LogDerivative_eventually_odd
    (f : ℂ → ℂ)
    (hEven : (fun z => f (-z)) =ᶠ[nhds 0] f) :
    (fun z => c2LogDerivative f (-z)) =ᶠ[nhds 0]
      fun z => -c2LogDerivative f z := by
  have hEvenDeriv : (fun z => -deriv f (-z)) =ᶠ[nhds 0] deriv f := by
    filter_upwards [hEven.deriv] with z h
    rw [deriv_comp_neg] at h
    exact h
  filter_upwards [hEven, hEvenDeriv] with z hValue hDeriv
  change deriv f (-z) / f (-z) = -(deriv f z / f z)
  have hDeriv' : deriv f (-z) = -deriv f z := by
    linear_combination -hDeriv
  rw [hValue, hDeriv']
  ring

/-- The response associated with the even projection, with the negative
logarithmic-derivative convention used by the completed characteristic. -/
def c2EvenProjectedResponse (H : ℂ → ℂ) : ℂ → ℂ :=
  fun z => -deriv (c2EvenProjection H) z /
    (2 * c2EvenProjection H z)

/-- Analyticity of the response requires the nonvanishing of the projected
head at the center; it is not inferred from positivity. -/
theorem c2EvenProjectedResponse_analyticAt
    (H : ℂ → ℂ)
    (hAnalytic : AnalyticAt ℂ (c2EvenProjection H) 0)
    (h0 : c2EvenProjection H 0 ≠ 0) :
    AnalyticAt ℂ (c2EvenProjectedResponse H) 0 := by
  unfold c2EvenProjectedResponse
  exact hAnalytic.deriv.neg.div
    (analyticAt_const.mul hAnalytic)
    (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) h0)

/-- The response of the even projection is odd on the same local germ. -/
theorem c2EvenProjectedResponse_eventually_odd (H : ℂ → ℂ) :
    (fun z => c2EvenProjectedResponse H (-z)) =ᶠ[nhds 0]
      fun z => -c2EvenProjectedResponse H z := by
  have hEven := c2EvenProjection_eventually_even H
  have hEvenDeriv :
      (fun z => -deriv (c2EvenProjection H) (-z)) =ᶠ[nhds 0]
        deriv (c2EvenProjection H) := by
    filter_upwards [hEven.deriv] with z h
    rw [deriv_comp_neg] at h
    exact h
  filter_upwards [hEven, hEvenDeriv] with z hValue hDeriv
  change -(deriv (c2EvenProjection H) (-z)) /
      (2 * c2EvenProjection H (-z)) =
    -(-deriv (c2EvenProjection H) z /
      (2 * c2EvenProjection H z))
  rw [hValue, hDeriv]
  ring

/-! ## The radial logarithmic derivative and its finite polynomial quotient -/

/-- Restriction of an even head to the radial line `z = i y`. -/
def c2RadialEvenHead (H : ℂ → ℂ) : ℂ → ℂ :=
  fun y => c2EvenProjection H (Complex.I * y)

theorem c2RadialEvenHead_eventually_even (H : ℂ → ℂ) :
    (fun y => c2RadialEvenHead H (-y)) =ᶠ[nhds 0]
      c2RadialEvenHead H := by
  filter_upwards [] with y
  simp [c2RadialEvenHead, mul_neg, c2EvenProjection_apply]
  ring

/-- Analyticity of the radial even head follows by composing the projected
head with the linear radial parameter. -/
theorem c2RadialEvenHead_analyticAt
    (H : ℂ → ℂ)
    (hAnalytic : AnalyticAt ℂ (c2EvenProjection H) 0) :
    AnalyticAt ℂ (c2RadialEvenHead H) 0 := by
  have hline : AnalyticAt ℂ (fun y : ℂ => Complex.I * y) 0 :=
    analyticAt_const.mul analyticAt_id
  have hcenter : AnalyticAt ℂ (c2EvenProjection H) (Complex.I * (0 : ℂ)) := by
    simpa using hAnalytic
  have h := hcenter.comp hline
  change AnalyticAt ℂ
    (fun y : ℂ => c2EvenProjection H (Complex.I * y)) 0
  simpa [Function.comp_def] using h

/-- The radial logarithmic derivative `u = f'/f` is analytic and odd when
the radial head is analytic and nonzero at zero. -/
def c2RadialLogDerivative (H : ℂ → ℂ) : ℂ → ℂ :=
  c2LogDerivative (c2RadialEvenHead H)

theorem c2RadialLogDerivative_analyticAt
    (H : ℂ → ℂ)
    (hAnalytic : AnalyticAt ℂ (c2EvenProjection H) 0)
    (h0 : c2EvenProjection H 0 ≠ 0) :
    AnalyticAt ℂ (c2RadialLogDerivative H) 0 := by
  have hRadial := c2RadialEvenHead_analyticAt H hAnalytic
  have hRadial0 : c2RadialEvenHead H 0 ≠ 0 := by
    simpa [c2RadialEvenHead] using h0
  exact c2LogDerivative_analyticAt _ hRadial hRadial0

theorem c2RadialLogDerivative_eventually_odd (H : ℂ → ℂ) :
    (fun y => c2RadialLogDerivative H (-y)) =ᶠ[nhds 0]
      fun y => -c2RadialLogDerivative H y :=
  c2LogDerivative_eventually_odd (c2RadialEvenHead H)
    (c2RadialEvenHead_eventually_even H)

/-- The finite polynomial which divides the sum of two odd monomials. -/
def c2OddDivisionPolynomial (j : ℕ) (y t : ℂ) : ℂ :=
  ∑ ell ∈ Finset.range (2 * j + 1),
    (-1 : ℂ)^ell * y^(2 * j - ell) * t^ell

/-- Polynomial factorization for one odd monomial. This identity is proved
without division, so it also records the value on the diagonal `y + t = 0`. -/
theorem c2OddDivisionPolynomial_mul
    (j : ℕ) (y t : ℂ) :
    (y + t) * c2OddDivisionPolynomial j y t =
      y^(2 * j + 1) + t^(2 * j + 1) := by
  have hgeom := (Commute.all y (-t)).geom_sum₂_mul (2 * j + 1)
  have hcomm :
      (∑ ell ∈ Finset.range (2 * j + 1),
        y^ell * (-t)^(2 * j + 1 - 1 - ell)) =
      ∑ ell ∈ Finset.range (2 * j + 1),
        (-t)^ell * y^(2 * j + 1 - 1 - ell) := by
    simpa using geom_sum₂_comm y (-t) (2 * j + 1)
  rw [hcomm] at hgeom
  have hterms :
      (∑ ell ∈ Finset.range (2 * j + 1),
        (-t)^ell * y^(2 * j + 1 - 1 - ell)) =
      c2OddDivisionPolynomial j y t := by
    unfold c2OddDivisionPolynomial
    apply Finset.sum_congr rfl
    intro ell hell
    have hell' : ell ≤ 2 * j := by
      have hlt := Finset.mem_range.mp hell
      omega
    have hexp : 2 * j + 1 - 1 - ell = 2 * j - ell := by omega
    rw [hexp]
    rw [neg_pow]
    ring
  rw [hterms] at hgeom
  have hnegEven : (-t : ℂ)^(2 * j) = t^(2 * j) := by
    rw [pow_mul]
    simp [pow_mul]
  have hodd : (-t : ℂ)^(2 * j + 1) = -(t^(2 * j + 1)) := by
    calc
      (-t : ℂ)^(2 * j + 1) = (-t)^(2 * j) * (-t) := by rw [pow_succ]
      _ = -(t^(2 * j) * t) := by rw [hnegEven]; ring
      _ = -(t^(2 * j + 1)) := by rw [pow_succ]
  rw [hodd] at hgeom
  simp only [sub_eq_add_neg, neg_neg] at hgeom
  calc
    (y + t) * c2OddDivisionPolynomial j y t =
        c2OddDivisionPolynomial j y t * (y + t) := by ring
    _ = y^(2 * j + 1) + t^(2 * j + 1) := hgeom

/-- Off the diagonal, the finite polynomial is exactly the quotient shown in
the source expansion. -/
theorem c2OddDivisionPolynomial_eq_quotient
    (j : ℕ) (y t : ℂ) (hyt : y + t ≠ 0) :
    (y^(2 * j + 1) + t^(2 * j + 1)) / (y + t) =
      c2OddDivisionPolynomial j y t := by
  rw [← c2OddDivisionPolynomial_mul]
  exact mul_div_cancel_left₀ _ hyt

/-! ## Reuse of the existing coefficient-to-form error transport -/

/-- Once the analytic argument supplies the coefficient estimate at radius
`1/4`, the existing source-form theorem transports it to the full complex
Hankel form, including all crossed terms. This adapter adds no sign
hypothesis; the analytic coefficient estimate remains a separate input. -/
theorem c2ProjectedMomentForm_error_transport
    (m mProjected : ℕ → ℝ) (shift N : ℕ) (B : ℝ)
    (hcoeff : ∀ j, |m j - mProjected j| ≤
      ((j + 1 : ℕ) : ℝ) * (16 : ℝ)^(j + 1) * B)
    (x : Fin N → ℂ) :
    complexSourceMomentForm m shift N x ≥
      complexSourceMomentForm mProjected shift N x -
        (16 : ℝ)^(shift + 1) * B *
          (((shift + 1 : ℕ) : ℝ) * (c2ErrorA0 x)^2 +
            2 * c2ErrorA0 x * c2ErrorA1 x) :=
  complexSourceMomentForm_error_lower m mProjected shift N B hcoeff x

/-! ## The original completed C2 source -/

/-- The original finite C2 head after the original completion dressing. -/
def completedNativeC2OriginalHead (M : ℕ) : ℂ → ℂ :=
  c2FiniteChartHeightCharacteristic M

/-- The omitted C2 tail after the same original completion dressing. -/
def completedNativeC2OriginalFullTail (M : ℕ) : ℂ → ℂ :=
  fun z => c2CompletionDressing z *
    nativeC2ExactCenterTail M (operatorHeightParameter z)

/-- The actual completed C2 characteristic is the original dressed head plus
its original dressed omitted-center tail on the centered germ. -/
theorem completedNativeC2OriginalHeadTail_eq_characteristic_eventually
    (M : ℕ) :
    (fun z => completedNativeOperatorCharacteristic z) =ᶠ[nhds 0]
      fun z => completedNativeC2OriginalHead M z +
        completedNativeC2OriginalFullTail M z := by
  have hdomain : ∀ᶠ z : ℂ in nhds 0,
      z ∈ completedNativeHeightDomain :=
    isOpen_completedNativeHeightDomain.mem_nhds
      zero_mem_completedNativeHeightDomain
  filter_upwards [hdomain] with z hz
  have hs : operatorHeightParameter z ∈ genuineCriticalStrip := by
    simpa [completedNativeHeightDomain] using hz
  have h := completedNativeC2Characteristic_sub_finite_eq_completion_mul_exactTail
    M z hs
  change completedNativeOperatorCharacteristic z =
    completedNativeC2OriginalHead M z +
      completedNativeC2OriginalFullTail M z
  dsimp [completedNativeC2OriginalHead, completedNativeC2OriginalFullTail]
  calc
    completedNativeOperatorCharacteristic z =
        (completedNativeOperatorCharacteristic z -
          c2FiniteChartHeightCharacteristic M z) +
            c2FiniteChartHeightCharacteristic M z := by ring
    _ = (c2CompletionDressing z *
          nativeC2ExactCenterTail M (operatorHeightParameter z)) +
            c2FiniteChartHeightCharacteristic M z := by rw [h]
    _ = c2FiniteChartHeightCharacteristic M z +
          c2CompletionDressing z *
            nativeC2ExactCenterTail M (operatorHeightParameter z) := by ring

/-- Exact even repartition of the original dressed C2 head and tail. The
projection is applied after both pieces have received the original dressing. -/
theorem completedNativeC2OriginalHeadTail_even_repartition_eventually
    (M : ℕ) :
    (fun z => completedNativeOperatorCharacteristic z) =ᶠ[nhds 0]
      fun z =>
        c2EvenProjection (completedNativeC2OriginalHead M) z +
          c2EvenProjection (completedNativeC2OriginalFullTail M) z := by
  exact c2EvenProjection_repartitions_eventually
    (completedNativeC2OriginalHeadTail_eq_characteristic_eventually M)
    completedNativeOperatorCharacteristic_eventually_even

private theorem genuineCriticalStrip_subset_nativeScalarDomain
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) : s ∈ nativeScalarDomain := by
  rcases hs with ⟨hlo, hhi⟩
  constructor <;> linarith

/-- Values of the original finite dressed heads converge to the completed
characteristic at the center, by the exact-tail convergence theorem. -/
theorem completedNativeC2OriginalHead_value_tendsto_center :
    Tendsto (fun M : ℕ => completedNativeC2OriginalHead M 0)
      atTop (nhds (completedNativeOperatorCharacteristic 0)) := by
  have hstrip : operatorHeightParameter 0 ∈ genuineCriticalStrip := by
    simpa [completedNativeHeightDomain] using zero_mem_completedNativeHeightDomain
  have hsNative : operatorHeightParameter 0 ∈ nativeScalarDomain :=
    genuineCriticalStrip_subset_nativeScalarDomain hstrip
  have htail := nativeC2ExactCenterTail_tendsto_zero hsNative
  have hweighted : Tendsto
      (fun M : ℕ => completedNativeC2OriginalFullTail M 0)
      atTop (nhds 0) := by
    simpa [completedNativeC2OriginalFullTail] using
      (tendsto_const_nhds.mul htail)
  have hlimit :=
    (tendsto_const_nhds : Tendsto
      (fun _ : ℕ => completedNativeOperatorCharacteristic 0) atTop
      (nhds (completedNativeOperatorCharacteristic 0))).sub hweighted
  have hheads : (fun M : ℕ => completedNativeC2OriginalHead M 0) =
      fun M => completedNativeOperatorCharacteristic 0 -
        completedNativeC2OriginalFullTail M 0 := by
    funext M
    have h := completedNativeC2Characteristic_sub_finite_eq_completion_mul_exactTail
      M 0 hstrip
    dsimp [completedNativeC2OriginalHead, completedNativeC2OriginalFullTail]
    linear_combination -h
  rw [hheads]
  simpa using hlimit

/-- Since the full characteristic is nonzero at zero, the projected original
heads are eventually nonzero there. This condition is obtained by
convergence, not by a sign assumption. -/
theorem completedNativeC2EvenOriginalHead_center_eventually_ne_zero :
    ∀ᶠ M : ℕ in atTop,
      c2EvenProjection (completedNativeC2OriginalHead M) 0 ≠ 0 := by
  have h := completedNativeC2OriginalHead_value_tendsto_center.eventually_ne
    completedNativeOperatorCharacteristic_zero_ne_zero
  filter_upwards [h] with M hM
  simpa [c2EvenProjection_apply] using hM

end
end CarrySelfAdjointOperator
