import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

namespace HolomorphicAnosov
open Set Filter _root_.Topology

/-- The compact containment step in Lehto–Virtanen I.Theorem 5.2, p.29.
The limit image of a compact inner set has a positive open neighborhood inside the chosen
image region. Uniform convergence on that compact set puts every sufficiently late image
inside the same neighborhood. No common target of the approximating maps is required. -/
theorem qc_limit_eventually_mapsTo
    {U C V : Set ℂ} {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hC : IsCompact C) (hCU : C ⊆ U) (hg : ContinuousOn g C)
    (hV : IsOpen V) (hgV : MapsTo g C V)
    (hF : TendstoLocallyUniformlyOn F g atTop U) :
    ∀ᶠ n in atTop, MapsTo (F n) C V := by
  obtain ⟨δ, hδ, hδV⟩ := (hC.image_of_continuousOn hg).exists_thickening_subset_open
    hV (image_subset_iff.mpr hgV)
  have hFC : TendstoUniformlyOn F g atTop C :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hC).mp (hF.mono hCU)
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hFC) δ hδ] with n hn x hx
  exact hδV (Metric.mem_thickening_iff.mpr
    ⟨g x, mem_image_of_mem g hx, (dist_comm _ _).trans_lt (hn x hx)⟩)


end HolomorphicAnosov
