import CarrySelfAdjointOperator.NativePhysicalLaguerreObservability
import CarrySelfAdjointOperator.NativePhysicalMaterialProducer
import CarrySelfAdjointOperator.NativeCompletedAllDistanceStencil

namespace CarrySelfAdjointOperator.PhysicalSewing
open scoped BigOperators Matrix ComplexConjugate InnerProductSpace
open NativeLaguerre NativeCauchyPorts
open NativeCarrySpectralWeyl.Camera.FiniteBridge
noncomputable section
set_option autoImplicit false

theorem physicalPair_signed_camera_crosses {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : ι → CanonicalCompletedNativeProjectiveChiralCarrier)
    (G : κ → CanonicalCompletedNativeProjectiveChiralCarrier) :
    canonicalCompletedNativeProjectiveChiralForm (∑ b, F b) (∑ c, G c) =
      ∑ b, ∑ c, canonicalCompletedNativeProjectiveChiralForm (F b) (G c) := by
  simp only [canonicalCompletedNativeProjectiveChiralForm, Prod.fst_sum, Prod.snd_sum,
    sum_inner, inner_sum, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
  congr 1 <;> exact Finset.sum_comm

theorem physicalPair_camera_fourSectors {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F E : ι → CanonicalCompletedNativeProjectiveChiralCarrier)
    (G D : κ → CanonicalCompletedNativeProjectiveChiralCarrier) :
    canonicalCompletedNativeProjectiveChiralForm (∑ b, (F b+E b)) (∑ c, (G c+D c)) =
      ∑ b, ∑ c,
        (canonicalCompletedNativeProjectiveChiralForm (F b) (G c) +
         canonicalCompletedNativeProjectiveChiralForm (F b) (D c) +
         canonicalCompletedNativeProjectiveChiralForm (E b) (G c) +
         canonicalCompletedNativeProjectiveChiralForm (E b) (D c)) := by
  rw [physicalPair_signed_camera_crosses]
  simp only [completed_residual_four_sectors]

def twoPortSignedTail (N R : ℕ) (v s w t : Fin N → ℂ) : ℂ :=
  matrixPairing (tailDiagonal R N * cauchyMatrix N * tailDiagonal R N) s w -
    matrixPairing (tailDiagonal R N * cauchyMatrix N * tailDiagonal R N) v t

theorem twoPort_signed_headTail (N k R : ℕ) (v s w t : Fin N → ℂ) :
    canonicalCompletedNativeProjectiveChiralForm
      (twoPortSynthesis N k v s) (twoPortSynthesis N k w t) =
    (Complex.I*((k : ℂ)+1)/2) *
      ((∑ r : Fin (R+1), (
        conj (laguerreReadout r.val s) * laguerreReadout r.val w -
          conj (laguerreReadout r.val v) * laguerreReadout r.val t)) +
        twoPortSignedTail N R v s w t) := by
  rw [twoPort_signed_form, matrixPairing_head_tail R N s w,
    matrixPairing_head_tail R N v t]
  unfold twoPortSignedTail
  rw [Finset.sum_sub_distrib]
  ring

/-- Independent labels and inputs, with a tail in every ordered pair. -/
theorem twoPort_camera_headTail {ι κ : Type*} [Fintype ι] [Fintype κ]
    (N k R : ℕ) (v s : ι → Fin N → ℂ) (w t : κ → Fin N → ℂ) :
    canonicalCompletedNativeProjectiveChiralForm
      (∑ b, twoPortSynthesis N k (v b) (s b)) (∑ c, twoPortSynthesis N k (w c) (t c)) =
    ∑ b, ∑ c, (Complex.I*((k : ℂ)+1)/2) *
      ((∑ r : Fin (R+1), (
        conj (laguerreReadout r.val (s b)) * laguerreReadout r.val (w c) -
          conj (laguerreReadout r.val (v b)) * laguerreReadout r.val (t c))) +
        twoPortSignedTail N R (v b) (s b) (w c) (t c)) := by
  rw [physicalPair_signed_camera_crosses]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  exact twoPort_signed_headTail N k R (v b) (s b) (w c) (t c)

def twoPortPolarizedHeadTail (N k R : ℕ) (v s w t : Fin N → ℂ) : ℂ :=
  (Complex.I*((k : ℂ)+1)/2) *
    ((∑ r : Fin (R+1), (conj (laguerreReadout r.val s) * laguerreReadout r.val w -
      conj (laguerreReadout r.val v) * laguerreReadout r.val t)) +
      twoPortSignedTail N R v s w t)

theorem twoPortSynthesis_add_secondDefect (N k : ℕ) (v s d : Fin N → ℂ) :
    twoPortSynthesis N k v (s+d) = twoPortSynthesis N k v s + twoPortSynthesis N k 0 d := by
  unfold twoPortSynthesis twoPortReconstruct
  simp only [map_add, map_zero]
  apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> module

/-- Four sectors in independent camera labels and independent input
defects; every sector includes its exact Cauchy/Laguerre tail. -/
theorem twoPort_camera_defect_fourHeadTails {ι κ : Type*} [Fintype ι] [Fintype κ]
    (N k R : ℕ) (v s d : ι → Fin N → ℂ) (w t e : κ → Fin N → ℂ) :
    canonicalCompletedNativeProjectiveChiralForm
      (∑ b, twoPortSynthesis N k (v b) (s b+d b))
      (∑ c, twoPortSynthesis N k (w c) (t c+e c)) =
    ∑ b, ∑ c,
      (twoPortPolarizedHeadTail N k R (v b) (s b) (w c) (t c) +
       twoPortPolarizedHeadTail N k R (v b) (s b) 0 (e c) +
       twoPortPolarizedHeadTail N k R 0 (d b) (w c) (t c) +
       twoPortPolarizedHeadTail N k R 0 (d b) 0 (e c)) := by
  simp only [twoPortSynthesis_add_secondDefect]
  rw [physicalPair_camera_fourSectors]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  unfold twoPortPolarizedHeadTail
  rw [twoPort_signed_headTail N k R (v b) (s b) (w c) (t c),
    twoPort_signed_headTail N k R (v b) (s b) 0 (e c),
    twoPort_signed_headTail N k R 0 (d b) (w c) (t c),
    twoPort_signed_headTail N k R 0 (d b) 0 (e c)]

/-- Observe EACH camera defect before any cancellation in the global sum. -/
theorem cameraDefectFamily_faithful {ι : Type*} (N k : ℕ) (theta : Fin N → ℂ)
    (d : ι → Fin N → ℂ) :
    (∀ b a, mixedPhysicalProbes N k theta (d b) a = 0) ↔ ∀ b, d b = 0 := by
  constructor
  · intro h b
    exact (mixedPhysicalProbes_faithful N k theta (d b)).mp (h b)
  · intro h b
    exact (mixedPhysicalProbes_faithful N k theta (d b)).mpr (h b)

theorem cameraDefectCancellation_canary (N : ℕ) (d : Fin N → ℂ) :
    (∑ b : Fin 2, (![d,-d] : Fin 2 → Fin N → ℂ) b) = 0 := by
  simp [Fin.sum_univ_two]

theorem originalMaterialBracket_threeChannels (k p r : ℕ) :
    originalMaterialCompletedSource k (centeredBracketStencil (p+r+1) r) =
      ∑ t ∈ Finset.range r, ∑ gamma : Fin 3,
        (FirstEdgeSewing.radialChiralEdgeChannels k (p+r+t) gamma -
          FirstEdgeSewing.radialChiralEdgeChannels k (p+t) gamma) := by
  rw [originalMaterialCompletedSource_bracket]
  simpa only [← Nat.cast_smul_eq_nsmul ℂ, Nat.cast_ofNat] using
    FirstEdgeSewing.completed_stencil_all_distance k p r

theorem originalC2_camera_literal (k M : ℕ) :
    originalMaterialCompletedSource k (finiteStencil 2 M) =
      canonicalCompletedNativeRadialProjectiveChiralState k 0 +
        ∑ a ∈ Finset.range M,
          (canonicalCompletedNativeRadialProjectiveChiralState k (4*(a+1)-2) -
            (2 : ℂ) • canonicalCompletedNativeRadialProjectiveChiralState k (4*(a+1)-1) +
            canonicalCompletedNativeRadialProjectiveChiralState k (4*(a+1))) := by
  rw [originalMaterialCompletedSource_camera]
  have hseed : originalMaterialCompletedSource k (seedStencil 2) =
      canonicalCompletedNativeRadialProjectiveChiralState k 0 := by
    simp [seedStencil, originalMaterialCompletedSource, atom]
  rw [hseed]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  have he : 4*(a+1) = (4*(a+1)-2)+1+1 := by omega
  have hc : centerStencil 2 a = centeredBracketStencil (4*(a+1)) 1 := by
    simp [centerStencil, FiniteNativeCarryOperator.Camera.alignedCenter]
  rw [hc, he, originalMaterialCompletedSource_bracket]
  congr 2

theorem originalNaturalCamera_literal (b k M : ℕ) (hb : 3 ≤ b) :
    originalMaterialCompletedSource k (finiteStencil b M) =
      (∑ r ∈ FiniteNativeCarryOperator.Camera.radiusSet b,
        canonicalCompletedNativeRadialProjectiveChiralState k (r-1)) +
      ∑ a ∈ Finset.range M, ∑ r ∈ FiniteNativeCarryOperator.Camera.radiusSet b,
        originalMaterialCompletedSource k (centeredBracketStencil (b*(a+1)) r) := by
  have hb2 : b ≠ 2 := by omega
  rw [originalMaterialCompletedSource_camera]
  simp only [seedStencil, centerStencil, if_neg hb2, map_sum,
    FiniteNativeCarryOperator.Camera.alignedCenter]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  have hrpos : 0 < r := (Finset.mem_Icc.mp hr).1
  have he : r = (r-1)+1 := by omega
  rw [he, originalMaterialCompletedSource_atom]
  simp

end
end CarrySelfAdjointOperator.PhysicalSewing
