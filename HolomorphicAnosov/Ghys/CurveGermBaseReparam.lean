import HolomorphicAnosov.Ghys.CurveJetReparametrizationData

/-! Rational source reparametrization preserves the base point of a curve germ. (Ghys, §3 p.591) -/

open Filter Set
open scoped Topology _root_.Topology Manifold ContDiff
noncomputable section
namespace HolomorphicAnosov.Ghys
universe u
variable (L : Type u) [TopologicalSpace L] [ChartedSpace ℂ L]
omit [TopologicalSpace L] [ChartedSpace ℂ L] in
/-- Rational source reparametrization preserves the base point of a curve germ. (Ghys, p.591) -/
theorem base_reparam (p : CurveJetReparametrization) (γ : CurveGerm L) :
    curveGermBase L (γ.compTendsto p.apply p.tendsto_zero) = curveGermBase L γ := by
  induction γ using Filter.Germ.inductionOn with
  | h f =>
      change f (p.apply 0) = f 0
      simp [CurveJetReparametrization.apply]

end HolomorphicAnosov.Ghys
