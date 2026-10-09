import CarrySelfAdjointOperator.FiniteQuadraticRelativeControl
import CarrySelfAdjointOperator.CompletedNativeChiralReturnSevenMarginLoss

/-!
# Relative control of the complete seven-source storage

The old full synthesis and entire analytic remainder are retained. The relative
bound uses only their continuity, homogeneity and the certified source face.
Its neighborhood belongs to N=7; no all-dimension threshold is asserted.
-/
namespace CarrySelfAdjointOperator
open scoped BigOperators ComplexConjugate
open Filter Topology ChiralReturn
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

private theorem real_cross_smul (z u v : ℂ) :
    (conj (z*u)*(z*v)).re = Complex.normSq z * (conj u*v).re := by
  have he : conj (z*u)*(z*v) = (Complex.normSq z : ℂ)*(conj u*v) := by
    rw [map_mul, Complex.normSq_eq_conj_mul_self]
    ring
  rw [he, Complex.re_ofReal_mul]

theorem radialSevenRegularizedBoundary_smul (h : ℝ) (z : ℂ)
    (x : Fin 7 → ℂ) (m : ℕ) :
    radialSevenRegularizedBoundary h (z • x) m = z * radialSevenRegularizedBoundary h x m := by
  unfold radialSevenRegularizedBoundary
  split_ifs with hm
  · rfl
  · simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring

theorem radialSevenRegularizedBoundaryEnergy_smul (h : ℝ) (z : ℂ) (x : Fin 7 → ℂ) :
    radialSevenRegularizedBoundaryEnergy h (z • x) =
      Complex.normSq z * radialSevenRegularizedBoundaryEnergy h x := by
  unfold radialSevenRegularizedBoundaryEnergy
  simp_rw [radialSevenRegularizedBoundary_smul, real_cross_smul]
  have hs (j : ℕ) :
      (∑ a ∈ Finset.range (2*j+1), (-1 : ℝ)^a *
        (Complex.normSq z * (conj (radialSevenRegularizedBoundary h x a) *
          radialSevenRegularizedBoundary h x (2*j-a)).re)) =
      Complex.normSq z * (∑ a ∈ Finset.range (2*j+1), (-1 : ℝ)^a *
        (conj (radialSevenRegularizedBoundary h x a) *
          radialSevenRegularizedBoundary h x (2*j-a)).re) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  simp_rw [hs]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem radialSevenRegularizedStorage_smul (R : ℂ → ℂ) (h : ℝ)
    (z : ℂ) (x : Fin 7 → ℂ) :
    radialSevenRegularizedStorage R h (z • x) =
      Complex.normSq z * radialSevenRegularizedStorage R h x := by
  change radialSevenRegularizedBoundaryEnergy h (z • x) +
    4*h*radialSevenRemainderQuadraticReadout R h (z • x) =
    Complex.normSq z * (radialSevenRegularizedBoundaryEnergy h x +
      4*h*radialSevenRemainderQuadraticReadout R h x)
  rw [radialSevenRegularizedBoundaryEnergy_smul,
    radialSevenRemainderQuadraticReadout_smul]
  ring

/-- Arbitrarily small relative control of the SUM of all finite-step crosses
and the full analytic remainder, uniformly over coefficient directions. -/
theorem radialSevenRegularizedStorage_eventually_relative_control
    (R : ℂ → ℂ) (hR : ContinuousAt R 0) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ h : ℝ in nhds 0, ∀ x : Fin 7 → ℂ,
      |radialSevenRegularizedStorage R h x - nativeSourceSevenBoundaryEnergy x| ≤
        η * nativeSourceSevenBoundaryEnergy x := by
  obtain ⟨ε,hε,hb⟩ := nativeSourceSevenBoundaryEnergy_uniform_margin
  exact fixedFiniteQuadratic_relative_control 7 (radialSevenRegularizedStorage R)
    nativeSourceSevenBoundaryEnergy (radialSevenRegularizedStorage_zero R)
    (radialSevenRegularizedStorage_continuousAt R hR)
    (radialSevenRegularizedStorage_smul R) ε hε hb η hη

/-- A two-sided estimate on the same complete source storage, without replacing
its metric or its readout by a positive proxy. -/
theorem storage_one_sevenSample_eventually_relative_control (η : ℝ) (hη : 0 < η) :
    ∀ᶠ k : ℕ in atTop, ∀ x : Fin 7 → ℂ,
      |(storage k (radialCompletedInputCoefficients k
          (radialSevenNormalizedBoundaryInput (radialFourSourceStep k) x)) 1).re -
        nativeSourceSevenBoundaryEnergy x| ≤ η * nativeSourceSevenBoundaryEnergy x := by
  obtain ⟨R,hRa,hE⟩ := storage_one_sevenSample_eventually_regularized
  have hc := radialFourSourceStep_tendsto_zero.eventually
    (radialSevenRegularizedStorage_eventually_relative_control R hRa.continuousAt η hη)
  filter_upwards [hE,hc] with k hk hc
  intro x
  rw [hk]
  exact hc x

/-- An actual radius for the fixed seven-dimensional regularized source.
The analogous finite-dimensional lemma has n before this existential radius. -/
theorem radialSevenRegularizedStorage_positive_radius
    (R : ℂ → ℂ) (hR : ContinuousAt R 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, |h| < δ → ∀ x : Fin 7 → ℂ,
      x ≠ 0 → 0 < radialSevenRegularizedStorage R h x := by
  obtain ⟨ε,hε,hb⟩ := nativeSourceSevenBoundaryEnergy_uniform_margin
  exact fixedFiniteQuadratic_positive_radius 7 (radialSevenRegularizedStorage R)
    nativeSourceSevenBoundaryEnergy (radialSevenRegularizedStorage_zero R)
    (radialSevenRegularizedStorage_continuousAt R hR)
    (radialSevenRegularizedStorage_smul R) ε hε hb
/-- Relative retention of the certified margin, controlling the complete
correction as a sum rather than taking independent bounds on each cross. -/
theorem storage_one_sevenSample_eventually_relative_sandwich (η : ℝ) (hη : 0 < η) :
    ∀ᶠ k : ℕ in atTop, ∀ x : Fin 7 → ℂ,
      (1-η)*nativeSourceSevenBoundaryEnergy x ≤
        (storage k (radialCompletedInputCoefficients k
          (radialSevenNormalizedBoundaryInput (radialFourSourceStep k) x)) 1).re ∧
      (storage k (radialCompletedInputCoefficients k
          (radialSevenNormalizedBoundaryInput (radialFourSourceStep k) x)) 1).re ≤
        (1+η)*nativeSourceSevenBoundaryEnergy x := by
  filter_upwards [storage_one_sevenSample_eventually_relative_control η hη] with k hk
  intro x
  have hb := abs_le.mp (hk x)
  constructor <;> linarith
end
end CarrySelfAdjointOperator
