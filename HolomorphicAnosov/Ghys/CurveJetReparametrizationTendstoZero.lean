import HolomorphicAnosov.Ghys.CurveJetReparametrizationParameters

/-! The rational source map tends to zero at zero. (Ghys, p.591) -/

open Filter
open scoped Topology _root_.Topology
namespace HolomorphicAnosov.Ghys

/-- The rational source map tends to zero as its argument tends to zero. (Ghys, p.591) -/
theorem CurveJetReparametrization.tendsto_zero (p : CurveJetReparametrization) :
    Tendsto p.apply (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
  have h : ContinuousAt p.apply (0 : ℂ) :=
    (continuousAt_const.mul continuousAt_id).div
      (continuousAt_const.add (continuousAt_const.mul continuousAt_id)) (by simp)
  simpa [CurveJetReparametrization.apply] using h.tendsto

end HolomorphicAnosov.Ghys
