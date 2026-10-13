import HolomorphicAnosov.Ghys.CurveJetReparametrizationData
import HolomorphicAnosov.Ghys.CurveGermReparametrizeAdmissible
import HolomorphicAnosov.Ghys.ScalarFirstReparam
import HolomorphicAnosov.Ghys.CurveGermMapReparam
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

open Filter Set
open scoped Topology _root_.Topology Manifold ContDiff
noncomputable section
namespace HolomorphicAnosov.Ghys
universe u
variable (L : Type u) [TopologicalSpace L] [ChartedSpace ℂ L]
/-- The first coefficient of a reparametrized admissible germ is the original coefficient multiplied
by the derivative of the source map at zero. (Ghys, p.591) -/
theorem curve_first_reparam (p : CurveJetReparametrization)
    (γ : CurveParamGerm L) (c : LeafChart L)
    (hbase : curveGermBase L γ.1 ∈ c.1.source) :
    curveGermFirst L c (curveParamGermReparametrize L p γ) =
      deriv p.apply 0 * curveGermFirst L c γ := by
  obtain ⟨g, hg0, hg, hgs, hge⟩ := γ.2
  have hbaseg : g 0 ∈ c.1.source := by
    have hb := hbase
    rw [← hge] at hb
    change g 0 ∈ c.1.source at hb
    exact hb
  let φ : ℂ → ℂ := (c.1 : L → ℂ) ∘ (g : ℂ → L)
  have hcm : ContMDiffOn (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) ∞ (c.1 : L → ℂ) c.1.source :=
    contMDiffOn_of_mem_maximalAtlas c.2
  have hφ : ContDiffAt ℂ 2 φ 0 := by
    have hc0 : g 0 ∈ c.1.source := hbaseg
    have hcg : ContMDiffOn (modelWithCornersSelf ℂ ℂ)
        (modelWithCornersSelf ℂ ℂ) ∞ φ
        (g.source ∩ (g : ℂ → L) ⁻¹' c.1.source) := by
      rw [show φ = (c.1 : L → ℂ) ∘ (g : ℂ → L) by rfl]
      exact hcm.comp' hg
    have hset : g.source ∩ (g : ℂ → L) ⁻¹' c.1.source ∈ 𝓝 (0 : ℂ) := by
      exact inter_mem (g.open_source.mem_nhds hg0)
        ((hg.continuousOn.continuousAt (g.open_source.mem_nhds hg0)).preimage_mem_nhds
          (c.1.open_source.mem_nhds hc0))
    exact (hcg.contDiffOn.contDiffAt hset).of_le (by simp)
  have hgm : γ.1.map (c.1 : L → ℂ) = (φ : ScalarGerm) := by
    simpa [φ] using congrArg (fun z : CurveGerm L ↦ z.map (c.1 : L → ℂ)) hge.symm
  have hcomp : (curveGermReparametrize L p γ.1).map (c.1 : L → ℂ) =
      ((φ : ScalarGerm).compTendsto p.apply p.tendsto_zero) := by
    rw [curveGermReparametrize, map_reparam, hgm]
  change germFirst ((curveGermReparametrize L p γ.1).map (c.1 : L → ℂ)) = _
  rw [hcomp, scalar_first_reparam p φ hφ]
  change _ = deriv p.apply 0 * germFirst (γ.1.map (c.1 : L → ℂ))
  have horig : germFirst (γ.1.map (c.1 : L → ℂ)) = deriv φ 0 := by
    rw [hgm]
    rfl
  rw [horig]
  ring

end HolomorphicAnosov.Ghys
