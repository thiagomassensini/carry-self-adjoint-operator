import CarrySelfAdjointOperator.FiniteMultibaseMaterialBracketTransport
import NativeCarrySpectralWeyl.Camera.BracketProfileBridge

/-! Literal camera borders before any scalar readout. The core is the
existing periodic profile on its slope-scaled prefix. The border is the
independently specified block of unit atoms, including the even antipode. -/
namespace CarrySelfAdjointOperator.MaterialBoundarySewing
open NativeCarrySpectralWeyl.Camera NativeCarrySpectralWeyl.Camera.FiniteBridge
open NativeCarrySpectralWeyl.Limits
open scoped BigOperators
noncomputable section
set_option autoImplicit false

def unitBorderStencil (start width : ℕ) : FormalStencil :=
  ∑ r ∈ Finset.range width, atom (start+r+1)

theorem unitBorderStencil_apply (start width p : ℕ) :
    unitBorderStencil start width p = if start < p ∧ p ≤ start+width then 1 else 0 := by
  induction width with
  | zero => simp [unitBorderStencil]
  | succ w ih =>
    rw [show unitBorderStencil start (w+1) = unitBorderStencil start w + atom (start+w+1) by
      simp [unitBorderStencil,Finset.sum_range_succ]]
    rw [Finsupp.add_apply,ih,atom_apply]
    split_ifs <;> omega

def cameraCoreStencil (b M : ℕ) : FormalStencil :=
  coefficientPrefixStencil (profile b) (cameraSlope b*M)

def cameraBorderStencil (b M : ℕ) : FormalStencil :=
  unitBorderStencil (cameraSlope b*M) (cameraBoundaryWidth b)

theorem not_dvd_in_translated_interval (d start p : ℕ)
    (hd : d ∣ start) (hp : start < p) (hpd : p < start+d) : ¬ d ∣ p := by
  intro h
  have hsub : d ∣ p-start := Nat.dvd_sub h hd
  exact (Nat.not_dvd_of_pos_of_lt (by omega : 0 < p-start) (by omega)) hsub

theorem half_dvd_even_mul (b M : ℕ) (hb : Even b) : b/2 ∣ b*M := by
  obtain ⟨q,rfl⟩ := hb
  rw [show (q+q)/2=q by omega]
  exact ⟨M+M,by ring⟩

/-- The entire emitted border consists of unit coefficients. In particular
the natural even antipode is one, rather than its periodic value two. -/
theorem finiteCoefficient_border_one (b M p : ℕ) (hb : 2 ≤ b)
    (hp : cameraSlope b*M < p) (hup : p ≤ finiteCameraWindow b M) :
    finiteCoefficient b M p = 1 := by
  by_cases h2 : b=2
  · subst b
    simp only [cameraSlope_two,finiteCameraWindow_two] at hp hup
    have he : p=4*M+1 := by omega
    subst p
    rw [c2_finiteCoefficient_eq_profile_window]
    have hnd2 : ¬ 2 ∣ 4*M+1 := by omega
    have hnd4 : ¬ 4 ∣ 4*M+1 := by omega
    simp [c2Profile,dvdIndicator,hnd2,hnd4]
  · have hb3 : 3 ≤ b := by omega
    rw [cameraSlope_of_ne_two h2] at hp
    rw [finiteCameraWindow_of_ne_two h2] at hup
    have hndb : ¬ b ∣ p := not_dvd_in_translated_interval b (b*M) p
      (dvd_mul_right b M) hp (by omega)
    rcases Nat.even_or_odd b with heven | hodd
    · have hb4 : 4 ≤ b := by obtain ⟨q,hq⟩ := heven; omega
      rw [even_finiteCoefficient_eq_profile_window hb4 heven]
      by_cases he : p=b*M+b/2
      · simp [he]
      · have hlt : p < b*M+b/2 := by omega
        have hndhalf := not_dvd_in_translated_interval (b/2) (b*M) p
          (half_dvd_even_mul b M heven) hp hlt
        simp [evenProfile,dvdIndicator,hndb,hndhalf,show 1 ≤ p by omega,hlt]
    · rw [odd_finiteCoefficient_eq_profile_window hb3 hodd]
      simp [oddProfile,dvdIndicator,hndb,show 1 ≤ p by omega,hup]

theorem finiteCoefficient_at_zero (b M : ℕ) (hb : 2 ≤ b) :
    finiteCoefficient b M 0 = 0 := by
  by_cases h2 : b=2
  · subst b
    rw [c2_finiteCoefficient_eq_profile_window]
    norm_num
  · have hb3 : 3 ≤ b := by omega
    rcases Nat.even_or_odd b with he | ho
    · have hb4 : 4 ≤ b := by obtain ⟨q,hq⟩ := he; omega
      rw [even_finiteCoefficient_eq_profile_window hb4 he]
      have hne : 0 ≠ b*M+b/2 := by omega
      simp [hne]
    · rw [odd_finiteCoefficient_eq_profile_window hb3 ho]
      simp

/-- Universal integer-vector identity, at every supported camera and cutoff.
No Gram or positivity premise enters this cancellation. -/
theorem finiteStencil_eq_core_add_border (b M : ℕ) (hb : 2 ≤ b) :
    finiteStencil b M = cameraCoreStencil b M + cameraBorderStencil b M := by
  ext p
  rw [finiteStencil_apply,Finsupp.add_apply,cameraCoreStencil,
    coefficientPrefixStencil_apply,cameraBorderStencil,unitBorderStencil_apply]
  by_cases hc : 1 ≤ p ∧ p ≤ cameraSlope b*M
  · rw [if_pos hc,finiteCoefficient_eq_profile_of_le_core hb hc.1 hc.2]
    have hn : ¬ (cameraSlope b*M < p ∧ p ≤ cameraSlope b*M+cameraBoundaryWidth b) := by omega
    simp [hn]
  · rw [if_neg hc,zero_add]
    by_cases he : cameraSlope b*M < p ∧ p ≤ cameraSlope b*M+cameraBoundaryWidth b
    · rw [if_pos he]
      exact finiteCoefficient_border_one b M p hb he.1 he.2
    · rw [if_neg he]
      by_cases hz : p=0
      · subst p
        exact finiteCoefficient_at_zero b M hb
      · exact finiteCoefficient_eq_zero_of_window_lt hb (by
          unfold finiteCameraWindow
          omega)

end
end CarrySelfAdjointOperator.MaterialBoundarySewing
