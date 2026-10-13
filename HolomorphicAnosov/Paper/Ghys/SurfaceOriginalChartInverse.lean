import HolomorphicAnosov.Analysis.Complex.LeblInjectiveHolomorphicBiholomorphism
import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility

/-!
# Holomorphic inverse in the original surface chart

This file transfers the holomorphic inverse theorem from coordinates to a partial homeomorphism in an original surface chart (Lebl, Thm. 1.6.5).
-/

open Set
open scoped ContDiff

namespace HolomorphicAnosov.Ghys

/-- A holomorphic injective partial homeomorphism whose image lies in an original holomorphic chart has a holomorphic inverse on its image (Lebl, Thm. 1.6.5). -/
theorem surface_original_chart_inverse
    {n : ℕ} (hn : 0 < n) {S : Type*}
    [TopologicalSpace S] [ChartedSpace (ComplexModel n) S]
    (e : OpenPartialHomeomorph (ComplexModel n) S)
    (c : OpenPartialHomeomorph S (ComplexModel n))
    (hec : e.target ⊆ c.source)
    (he : ContMDiffOn (complexModel n) (complexModel n) ∞ e e.source)
    (hc : ContMDiffOn (complexModel n) (complexModel n) ∞ c c.source) :
    ContMDiffOn (complexModel n) (complexModel n) ∞ e.symm e.target := by
  have hF : DifferentiableOn ℂ (c ∘ e) e.source :=
    (hc.comp he (fun _ hx ↦ hec (e.map_source hx))).contDiffOn.differentiableOn (by simp)
  have hi : InjOn (c ∘ e) e.source := by
    intro x hx y hy hxy
    exact e.injOn hx hy (c.injOn (hec (e.map_source hx)) (hec (e.map_source hy)) hxy)
  obtain ⟨_, ho, G, hG, hleft, _⟩ :=
    lebl_injective_holomorphic_biholomorphism hn e.open_source hF hi
  have hm : MapsTo c e.target ((c ∘ e) '' e.source) := by
    intro y hy
    exact ⟨e.symm y, e.map_target hy, by simp [e.right_inv hy]⟩
  have hGc : ContMDiffOn (complexModel n) (complexModel n) ∞ G
      ((c ∘ e) '' e.source) :=
    ((complex_contDiffOn_iff_differentiableOn ho).mpr hG).contMDiffOn
  have hcomp : ContMDiffOn (complexModel n) (complexModel n) ∞ (G ∘ c) e.target :=
    hGc.comp (hc.mono hec) hm
  apply hcomp.congr
  intro y hy
  have h := hleft (e.symm y) (e.map_target hy)
  simpa only [Function.comp_apply, e.right_inv hy] using h.symm


end HolomorphicAnosov.Ghys
