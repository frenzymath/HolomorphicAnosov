import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
Reusable EuclideanInverse declarations from the Riemannian exponential construction.
-/ 

open Set Bundle TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology

namespace HolomorphicAnosov.W07ManifoldInverseFunction

noncomputable section

theorem euclidean_inverse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : E → F} {S : Set E} (hS : IsOpen S) {a : E} (ha : a ∈ S)
    (hg : ContDiffOn ℝ ∞ g S) (e : E ≃L[ℝ] F)
    (he : HasFDerivAt g e.toContinuousLinearMap a) :
    ∃ p : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞,
      a ∈ p.source ∧ p.source ⊆ S ∧ (p : E → F) = g := by
  have hga := hg.contDiffAt (hS.mem_nhds ha)
  let p := hga.toOpenPartialHomeomorph g he (by simp)
  have hd := (hga.continuousAt_fderiv (by simp))
  have hi : (fderiv ℝ g a).IsInvertible := by
    rw [he.fderiv]
    exact ⟨e, rfl⟩
  obtain ⟨R, hR, hRo, haR⟩ := mem_nhds_iff.mp (hd hi.eventually_nhds)
  let q := p.restr (S ∩ R)
  have hqo : q.source = p.source ∩ (S ∩ R) := p.restr_source' _ (hS.inter hRo)
  have hqg : (q : E → F) = g := rfl
  have hqS : q.source ⊆ S := by rw [hqo]; exact fun _ h ↦ h.2.1
  have hqsm : ContDiffOn ℝ ∞ q q.source := by rw [hqg]; exact hg.mono hqS
  have hqinv : ContDiffOn ℝ ∞ q.symm q.target := by
    intro y hy
    have hx := q.map_target hy
    have hxS := hqS hx
    have hxi : (fderiv ℝ g (q.symm y)).IsInvertible := hR (by
      rw [hqo] at hx
      exact hx.2.2)
    obtain ⟨b, hb⟩ := hxi
    have hder : HasFDerivAt q b.toContinuousLinearMap (q.symm y) := by
      rw [hqg, hb]
      exact (hg.contDiffAt (hS.mem_nhds hxS)).differentiableAt (by simp) |>.hasFDerivAt
    exact (q.contDiffAt_symm hy hder
      (hqsm.contDiffAt (q.open_source.mem_nhds hx))).contDiffWithinAt
  refine ⟨{ toPartialEquiv := q.toPartialEquiv
            open_source := q.open_source
            open_target := q.open_target
            contMDiffOn_toFun := hqsm.contMDiffOn
            contMDiffOn_invFun := hqinv.contMDiffOn }, ?_, hqS, hqg⟩
  rw [hqo]
  exact ⟨hga.mem_toOpenPartialHomeomorph_source he (by simp), ha, haR⟩

end
end HolomorphicAnosov.W07ManifoldInverseFunction
