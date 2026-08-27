import CarrySelfAdjointOperator.LinearPMapPointSpectrum
import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import Mathlib.Tactic

/-!
# Point spectrum from a meromorphic graph resolvent

For a closed partial operator, a genuine vector-valued meromorphic resolvent
cannot acquire a pole without producing a point eigenvector. The proof keeps
both graph coordinates: the trailing coefficient remains in the closed graph,
while the leading part of the resolvent equation becomes the eigenvalue
equation.
-/

open Filter Set Topology

namespace LinearPMap

noncomputable section

/-- If one bounded linear readout of a meromorphic vector escapes every
bounded set, then the vector-valued function itself has negative meromorphic
order. -/
theorem meromorphicOrderAt_neg_of_continuousLinearReadout_cobounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {g : ℂ → E} {z₀ : ℂ}
    (hg : MeromorphicAt g z₀) (readout : E →L[ℂ] ℂ)
    (hreadout : Tendsto (fun z => readout (g z))
      (nhdsWithin z₀ {z₀}ᶜ) (Bornology.cobounded ℂ)) :
    meromorphicOrderAt g z₀ < 0 := by
  by_contra hneg
  have hnonneg : 0 ≤ meromorphicOrderAt g z₀ := le_of_not_gt hneg
  obtain ⟨v, hv⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hg hnonneg
  have hfinite : Tendsto (fun z => readout (g z))
      (nhdsWithin z₀ {z₀}ᶜ) (nhds (readout v)) :=
    readout.continuous.continuousAt.tendsto.comp hv
  have hnormFinite := hfinite.norm
  have hnormInfinite : Tendsto (fun z => ‖readout (g z)‖)
      (nhdsWithin z₀ {z₀}ᶜ) atTop := by
    rwa [tendsto_norm_atTop_iff_cobounded]
  exact (not_tendsto_atTop_of_tendsto_nhds hnormFinite) hnormInfinite

/-- A pole of a vector-valued resolvent living in the closed graph of `A`
produces the reciprocal value of its continuous parameter as a point
eigenvalue of `A`.

The function `graphResolvent z = (x z, A x z)` retains both graph channels.
The equation `x z - parameter z A x z = source` is required only in a
punctured neighborhood, exactly where meromorphic continuation is compared. -/
theorem hasEigenvalue_inv_parameter_of_meromorphic_graphResolvent
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →ₗ.[ℂ] E) (hA : A.IsClosed)
    {z₀ : ℂ} {parameter : ℂ → ℂ}
    (hparameter : ContinuousAt parameter z₀)
    (hparameterNe : parameter z₀ ≠ 0)
    {graphResolvent : ℂ → E × E}
    {source : E}
    (hmeromorphic : MeromorphicAt graphResolvent z₀)
    (hpole : meromorphicOrderAt graphResolvent z₀ < 0)
    (hgraph : ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ,
      graphResolvent z ∈ A.graph)
    (hresolvent : ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ,
      (graphResolvent z).1 - parameter z • (graphResolvent z).2 = source) :
    HasEigenvalue A (parameter z₀)⁻¹ := by
  let order : ℤ := (meromorphicOrderAt graphResolvent z₀).untop₀
  let scale : ℂ → ℂ := fun z => (z - z₀) ^ (-order)
  let scaled : ℂ → E × E :=
    ((fun z : ℂ => z - z₀) ^ (-order)) • graphResolvent
  let residue : E × E := meromorphicTrailingCoeffAt graphResolvent z₀
  have horderFinite : meromorphicOrderAt graphResolvent z₀ ≠ ⊤ :=
    hpole.ne_top
  have horderCoe : (order : WithTop ℤ) =
      meromorphicOrderAt graphResolvent z₀ := by
    exact WithTop.coe_untop₀_of_ne_top horderFinite
  have horderNeg : order < 0 := by
    have h := hpole
    rw [← horderCoe] at h
    exact_mod_cast h
  have hscalePos : 0 < -order := neg_pos.mpr horderNeg
  have hscaled_apply (z : ℂ) :
      scaled z = scale z • graphResolvent z := by
    simp only [scaled, scale, Pi.smul_apply', Pi.pow_apply]
  have hscaledTendsto : Tendsto scaled
      (nhdsWithin z₀ {z₀}ᶜ) (nhds residue) := by
    simpa only [scaled, order, residue] using
      hmeromorphic.tendsto_nhds_meromorphicTrailingCoeffAt
  have hscaledGraph : ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ,
      scaled z ∈ A.graph := by
    filter_upwards [hgraph] with z hz
    rw [hscaled_apply]
    exact A.graph.smul_mem (scale z) hz
  have hresidueGraph : residue ∈ A.graph := by
    change _root_.IsClosed (A.graph : Set (E × E)) at hA
    exact hA.mem_of_tendsto hscaledTendsto hscaledGraph
  have hscaleZero : Tendsto scale (nhdsWithin z₀ {z₀}ᶜ) (nhds 0) := by
    have hcontinuous : ContinuousAt scale z₀ := by
      dsimp only [scale]
      exact (continuousAt_id.sub continuousAt_const).zpow₀ (-order)
        (Or.inr hscalePos.le)
    have hvalue : scale z₀ = 0 := by
      dsimp only [scale]
      rw [sub_self]
      exact zero_zpow (-order) hscalePos.ne'
    have ht : Tendsto scale (nhdsWithin z₀ {z₀}ᶜ)
        (nhds (scale z₀)) := hcontinuous.continuousWithinAt.tendsto
    rw [hvalue] at ht
    exact ht
  have hparameterTendsto : Tendsto parameter
      (nhdsWithin z₀ {z₀}ᶜ) (nhds (parameter z₀)) :=
    hparameter.continuousWithinAt.tendsto
  have hfirstTendsto : Tendsto
      (fun z => (scaled z).1)
      (nhdsWithin z₀ {z₀}ᶜ) (nhds residue.1) :=
    continuousAt_fst.tendsto.comp hscaledTendsto
  have hsecondTendsto : Tendsto
      (fun z => (scaled z).2)
      (nhdsWithin z₀ {z₀}ᶜ) (nhds residue.2) :=
    continuousAt_snd.tendsto.comp hscaledTendsto
  have hleftTendsto : Tendsto
      (fun z => (scaled z).1 - parameter z • (scaled z).2)
      (nhdsWithin z₀ {z₀}ᶜ)
      (nhds (residue.1 - parameter z₀ • residue.2)) :=
    hfirstTendsto.sub (hparameterTendsto.smul hsecondTendsto)
  have hrightTendsto : Tendsto (fun z => scale z • source)
      (nhdsWithin z₀ {z₀}ᶜ) (nhds 0) := by
    simpa using hscaleZero.smul_const source
  have hscaledResolvent : ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ,
      (scaled z).1 - parameter z • (scaled z).2 = scale z • source := by
    filter_upwards [hresolvent] with z hz
    rw [hscaled_apply, Prod.smul_fst, Prod.smul_snd, ← hz]
    module
  have hscaledResolvent' :
      (fun z => (scaled z).1 - parameter z • (scaled z).2) =ᶠ[
        nhdsWithin z₀ {z₀}ᶜ] fun z => scale z • source :=
    hscaledResolvent
  have hleading : residue.1 - parameter z₀ • residue.2 = 0 := by
    exact tendsto_nhds_unique hleftTendsto
      (hrightTendsto.congr' hscaledResolvent'.symm)
  have hresidueNe : residue ≠ 0 :=
    hmeromorphic.meromorphicTrailingCoeffAt_ne_zero horderFinite
  have hfirstNe : residue.1 ≠ 0 := by
    intro hzero
    have hsecondZero : residue.2 = 0 := by
      have : parameter z₀ • residue.2 = 0 := by
        simpa [hzero] using hleading.symm
      exact (smul_eq_zero.mp this).resolve_left hparameterNe
    apply hresidueNe
    exact Prod.ext hzero hsecondZero
  rw [LinearPMap.mem_graph_iff] at hresidueGraph
  obtain ⟨x, hx, hAx⟩ := hresidueGraph
  refine ⟨x, ?_, ?_⟩
  · simpa [hx] using hfirstNe
  · have hsecond : residue.2 = (parameter z₀)⁻¹ • residue.1 := by
      rw [sub_eq_zero.mp hleading]
      simp [hparameterNe]
    calc
      A x = residue.2 := hAx
      _ = (parameter z₀)⁻¹ • residue.1 := hsecond
      _ = (parameter z₀)⁻¹ • (x : E) := by rw [hx]

/-- Identity-parameter specialization of
`hasEigenvalue_inv_parameter_of_meromorphic_graphResolvent`. -/
theorem hasEigenvalue_inv_of_meromorphic_graphResolvent
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →ₗ.[ℂ] E) (hA : A.IsClosed)
    {z₀ : ℂ} (hz₀ : z₀ ≠ 0) {graphResolvent : ℂ → E × E}
    {source : E}
    (hmeromorphic : MeromorphicAt graphResolvent z₀)
    (hpole : meromorphicOrderAt graphResolvent z₀ < 0)
    (hgraph : ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ,
      graphResolvent z ∈ A.graph)
    (hresolvent : ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ,
      (graphResolvent z).1 - z • (graphResolvent z).2 = source) :
    HasEigenvalue A z₀⁻¹ := by
  exact hasEigenvalue_inv_parameter_of_meromorphic_graphResolvent
    A hA continuousAt_id hz₀ hmeromorphic hpole hgraph hresolvent

/-- Readout form for an arbitrary continuous resolvent parameter. -/
theorem hasEigenvalue_inv_parameter_of_meromorphic_graphResolvent_readout
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →ₗ.[ℂ] E) (hA : A.IsClosed)
    {z₀ : ℂ} {parameter : ℂ → ℂ}
    (hparameter : ContinuousAt parameter z₀)
    (hparameterNe : parameter z₀ ≠ 0)
    {graphResolvent : ℂ → E × E} {source : E}
    (hmeromorphic : MeromorphicAt graphResolvent z₀)
    (readout : (E × E) →L[ℂ] ℂ)
    (hreadout : Tendsto (fun z => readout (graphResolvent z))
      (nhdsWithin z₀ {z₀}ᶜ) (Bornology.cobounded ℂ))
    (hgraph : ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ,
      graphResolvent z ∈ A.graph)
    (hresolvent : ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ,
      (graphResolvent z).1 - parameter z • (graphResolvent z).2 = source) :
    HasEigenvalue A (parameter z₀)⁻¹ := by
  exact hasEigenvalue_inv_parameter_of_meromorphic_graphResolvent
    A hA hparameter hparameterNe hmeromorphic
      (meromorphicOrderAt_neg_of_continuousLinearReadout_cobounded
        hmeromorphic readout hreadout)
      hgraph hresolvent

/-- Readout form of `hasEigenvalue_inv_of_meromorphic_graphResolvent`: an
escaping bounded linear readout proves that the graph-valued continuation has
a pole, after which closedness extracts the point eigenvector. -/
theorem hasEigenvalue_inv_of_meromorphic_graphResolvent_readout
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →ₗ.[ℂ] E) (hA : A.IsClosed)
    {z₀ : ℂ} (hz₀ : z₀ ≠ 0) {graphResolvent : ℂ → E × E}
    {source : E}
    (hmeromorphic : MeromorphicAt graphResolvent z₀)
    (readout : (E × E) →L[ℂ] ℂ)
    (hreadout : Tendsto (fun z => readout (graphResolvent z))
      (nhdsWithin z₀ {z₀}ᶜ) (Bornology.cobounded ℂ))
    (hgraph : ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ,
      graphResolvent z ∈ A.graph)
    (hresolvent : ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ,
      (graphResolvent z).1 - z • (graphResolvent z).2 = source) :
    HasEigenvalue A z₀⁻¹ := by
  exact hasEigenvalue_inv_of_meromorphic_graphResolvent A hA hz₀
    hmeromorphic
    (meromorphicOrderAt_neg_of_continuousLinearReadout_cobounded
      hmeromorphic readout hreadout)
    hgraph hresolvent

end

end LinearPMap
