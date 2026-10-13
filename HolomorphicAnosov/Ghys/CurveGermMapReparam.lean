import HolomorphicAnosov.Ghys.CurveJetReparametrizationData

/-! Target maps commute with rational source reparametrization of curve germs. (Ghys, §3 p.591) -/

open Filter Set
open scoped Topology _root_.Topology Manifold ContDiff
noncomputable section
namespace HolomorphicAnosov.Ghys
universe u
variable (L : Type u) [TopologicalSpace L] [ChartedSpace ℂ L]
omit [TopologicalSpace L] [ChartedSpace ℂ L] in
/-- Mapping the target of a curve germ commutes with rational source reparametrization. (Ghys,
p.591) -/
theorem map_reparam (p : CurveJetReparametrization) (γ : CurveGerm L) (c : L → ℂ) :
    (γ.compTendsto p.apply p.tendsto_zero).map c =
      (γ.map c).compTendsto p.apply p.tendsto_zero := by
  induction γ using Filter.Germ.inductionOn with
  | h f => rfl

end HolomorphicAnosov.Ghys
