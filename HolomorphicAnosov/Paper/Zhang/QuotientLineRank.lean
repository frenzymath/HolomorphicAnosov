import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicTangentSubbundle
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine.Basic
import Mathlib.LinearAlgebra.Dimension.RankNullity

open scoped Manifold ContDiff Topology _root_.Topology
noncomputable section
universe u
namespace HolomorphicAnosov

/-- The quotient of the complex tangent bundle by a rank-`d - 1` holomorphic
subbundle has one-dimensional fibres when `1 ≤ d`. (Zhang, §2.1, p.4) -/
theorem quotient_line_of_holomorphic_codimension_one
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    (hd : 1 ≤ d)
    (U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    (hU : IsHolomorphicTangentSubbundle (d - 1) U) :
    IsQuotientTangentLine U := by
  intro x
  obtain ⟨V, s, hxV, hs, hspan⟩ := hU x
  have hdim : Module.finrank ℂ (U x) = d - 1 := by
    rw [← hspan x hxV, finrank_span_eq_card (hs.2.2 x hxV)]
    simp
  have htotal : Module.finrank ℂ (TangentSpace (complexModel d) x) = d := by
    rw [(tangentSpaceCastModel (complexModel d) x).toLinearEquiv.finrank_eq]
    simp [ComplexModel]
  have hr := (U x).finrank_quotient_add_finrank
  change Module.finrank ℂ (TangentSpace (complexModel d) x ⧸ U x) = 1
  rw [hdim, htotal] at hr
  omega

end HolomorphicAnosov
