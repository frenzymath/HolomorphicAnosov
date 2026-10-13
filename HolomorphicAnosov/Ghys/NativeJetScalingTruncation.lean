import HolomorphicAnosov.Ghys.NativeLeafwiseParametrizationJetBundle
import HolomorphicAnosov.Ghys.CurveJetReparametrization

noncomputable section
namespace HolomorphicAnosov.Ghys

open scoped ContDiff Manifold
universe u

/-- Native two-jet pure scaling commutes with truncation. (Ghys, §3) -/
theorem nativeJetScalingTruncation
    {ι : Type u} {L : ι → Type u}
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace ℂ (L i)]
    [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]
    [∀ i, T2Space (L i)] [∀ i, SecondCountableTopology (L i)]
    (omega : ℂˣ) (j : NativeLeafwiseJet2 L) :
    nativeLeafwiseJetTruncation L
        (nativeLeafwiseJet2Reparametrize L (.scale omega) j) =
      nativeLeafwiseJet1Scale L omega (nativeLeafwiseJetTruncation L j) := by
  rcases j with ⟨i, j⟩
  change (⟨i, curveJetTruncation (L i)
      (curveJet2Reparametrize (L i) (.scale omega) j)⟩ : NativeLeafwiseJet1 L) =
    (⟨i, curveJet1Scale (L i) omega (curveJetTruncation (L i) j)⟩ : NativeLeafwiseJet1 L)
  congr 1
  exact ((curve_jet_reparametrization (L i)).2.2.1 (.scale omega) j).2.1

end HolomorphicAnosov.Ghys
