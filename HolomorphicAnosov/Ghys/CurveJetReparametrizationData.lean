import HolomorphicAnosov.Ghys.LeafJetComplexManifold
import HolomorphicAnosov.Ghys.CurveJetReparametrizationParameters
import HolomorphicAnosov.Ghys.CurveJetReparametrizationTendstoZero

/-! Rational source precomposition on curve germs at zero. (Ghys, §3 p.591) -/

noncomputable section
namespace HolomorphicAnosov.Ghys
universe u

variable (L : Type u) [TopologicalSpace L] [ChartedSpace ℂ L]

/-- Precomposition of a curve germ with the rational source map. (Ghys, p.591) -/
def curveGermReparametrize (p : CurveJetReparametrization) (γ : CurveGerm L) :
    CurveGerm L := γ.compTendsto p.apply p.tendsto_zero


end HolomorphicAnosov.Ghys
