import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.ComplexModel
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
Complex differentiable scalar functions on open subsets of complex manifolds are smooth.
(Demailly, I §3.B–C, pp. 22–23)
-/

open scoped Manifold ContDiff Topology _root_.Topology

namespace HolomorphicAnosov

/-- A complex differentiable scalar function on an open subset of a complex manifold is complex
smooth there. (Demailly, I §3.B–C, pp. 22–23) -/
theorem complex_scalar_contMDiffOn_of_mdifferentiableOn
    {d : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X] {U : Set X} (hU : IsOpen U) {q : X → ℂ}
    (hq : MDifferentiableOn (complexModel d) 𝓘(ℂ) q U) :
    ContMDiffOn (complexModel d) 𝓘(ℂ) ∞ q U := by
  intro x hx
  let c := chartAt (ComplexModel d) x
  let V := c.target ∩ c.symm ⁻¹' U
  have hV : IsOpen V := c.continuousOn_symm.isOpen_inter_preimage c.open_target hU
  have hcx : c x ∈ V := ⟨mem_chart_target _ x, by simpa [c] using hx⟩
  have hdiff : DifferentiableOn ℂ (q ∘ c.symm) V := by
    intro z hz
    have hqi := (hq (c.symm z) hz.2).mdifferentiableAt (hU.mem_nhds hz.2)
    have hci := contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I := complexModel d) (n := ∞) x) hz.1
    exact (hqi.comp z (hci.mdifferentiableAt (by simp))).differentiableAt.differentiableWithinAt
  have hsmooth : ContDiffOn ℂ ∞ (q ∘ c.symm) V := by
    have hpi : DifferentiableOn ℂ (fun z (_ : Fin 1) ↦ q (c.symm z)) V :=
      differentiableOn_pi.mpr (fun _ ↦ hdiff)
    exact contDiffOn_pi.mp ((complex_contDiffOn_iff_differentiableOn hV).mpr hpi) 0
  have hlocal := (hsmooth.contMDiffOn.contMDiffAt (hV.mem_nhds hcx)).comp x
    (contMDiffAt_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I := complexModel d) (n := ∞) x) (mem_chart_source _ x))
  apply ContMDiffAt.contMDiffWithinAt
  apply hlocal.congr_of_eventuallyEq
  filter_upwards [c.open_source.mem_nhds (mem_chart_source _ x)] with y hy
  simp only [Function.comp_apply, c.left_inv hy]

end HolomorphicAnosov

