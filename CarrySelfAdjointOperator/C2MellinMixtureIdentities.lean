import CarrySelfAdjointOperator.C2MellinPositiveDensity
import Mathlib.Tactic

namespace CarrySelfAdjointOperator

noncomputable section

/-- Relative correction expressed using the original C2 head and tail values
and their negative Dirichlet derivatives `J_M` and `J_T`. -/
def nativeC2MellinRelativeXi
    (V J_M T J_T : ℝ) : ℝ :=
  (V * J_T - J_M * T) / (V * (V + T))

/-- Relative tail mass in the source mixture. -/
def nativeC2MellinTailMassFraction (V T : ℝ) : ℝ :=
  T / (V + T)

/-- Difference between the head and tail logarithmic means after cancellation
of their common Gamma contribution. -/
def nativeC2MellinLogMeanDifference
    (V J_M T J_T : ℝ) : ℝ :=
  -J_M / V - (-J_T / T)

/-- The relative Wronskian correction is exactly tail mass times the
logarithmic-mean difference. -/
theorem nativeC2MellinRelativeXi_eq_mass_mul_logMeanDifference
    (V J_M T J_T : ℝ)
    (hV : V ≠ 0) (hT : T ≠ 0) (hVT : V + T ≠ 0) :
    nativeC2MellinRelativeXi V J_M T J_T =
      nativeC2MellinTailMassFraction V T *
        nativeC2MellinLogMeanDifference V J_M T J_T := by
  unfold nativeC2MellinRelativeXi nativeC2MellinTailMassFraction
    nativeC2MellinLogMeanDifference
  field_simp [hV, hT, hVT]
  ring

/-- The common logarithmic derivative of Gamma cancels from the difference
of the head and tail logarithmic means. -/
theorem nativeC2Mellin_commonGamma_cancels
    (gamma gammaPrime V J_M T J_T : ℝ) :
    (gammaPrime / gamma - J_M / V) -
        (gammaPrime / gamma - J_T / T) =
      -J_M / V - (-J_T / T) := by
  ring

/-- Mean of a two-component probability mixture. -/
def nativeC2MellinMixtureMean (p muH muT : ℝ) : ℝ :=
  (1 - p) * muH + p * muT

/-- Raw second moment of a mixture, expressed through component means and
variances. -/
def nativeC2MellinMixtureRawSecondMoment
    (p muH muT varH varT : ℝ) : ℝ :=
  (1 - p) * (varH + muH ^ 2) + p * (varT + muT ^ 2)

/-- Variance obtained by subtracting the square of the mixture mean from its
raw second moment. -/
def nativeC2MellinMixtureVariance
    (p muH muT varH varT : ℝ) : ℝ :=
  nativeC2MellinMixtureRawSecondMoment p muH muT varH varT -
    nativeC2MellinMixtureMean p muH muT ^ 2

/-- The second cumulant of a two-component mixture includes both the
component variances and the positive between-means term. -/
theorem nativeC2MellinMixtureVariance_eq_components
    (p muH muT varH varT : ℝ) :
    nativeC2MellinMixtureVariance p muH muT varH varT =
      (1 - p) * varH + p * varT +
        p * (1 - p) * (muH - muT) ^ 2 := by
  unfold nativeC2MellinMixtureVariance nativeC2MellinMixtureRawSecondMoment
    nativeC2MellinMixtureMean
  ring

/-- Comparison with the head variance retains the signed difference of the
component variances; only the between-means term has a fixed sign. -/
theorem nativeC2MellinMixtureVariance_sub_headVariance
    (p muH muT varH varT : ℝ) :
    nativeC2MellinMixtureVariance p muH muT varH varT - varH =
      p * (varT - varH) + p * (1 - p) * (muH - muT) ^ 2 := by
  rw [nativeC2MellinMixtureVariance_eq_components]
  ring

theorem nativeC2MellinMixture_betweenMeans_nonneg
    {p muH muT : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ p * (1 - p) * (muH - muT) ^ 2 := by
  exact mul_nonneg (mul_nonneg hp0 (by linarith)) (sq_nonneg _)

end

end CarrySelfAdjointOperator
