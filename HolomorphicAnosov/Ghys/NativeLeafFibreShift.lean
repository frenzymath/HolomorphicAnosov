import HolomorphicAnosov.Ghys.NativeLeafwiseParametrizationJetBundle
import HolomorphicAnosov.Ghys.CurveJetReparametrization

noncomputable section
namespace HolomorphicAnosov.Ghys

open scoped ContDiff Manifold
universe u

/-- The rational reparametrization action is uniquely transitive on every native two-jet truncation fibre. (Ghys, §3) -/
theorem nativeLeafFibreShiftUnique
    {ι : Type u} {L : ι → Type u}
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace ℂ (L i)]
    [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]
    [∀ i, T2Space (L i)] [∀ i, SecondCountableTopology (L i)]
    (i : ι) {j k : CurveJet2 (L i)}
    (h : curveJetTruncation (L i) j = curveJetTruncation (L i) k) :
    ∃! μ : ℂ,
      curveJet2Reparametrize (L i) ⟨1, μ⟩ j = k := by
  rcases curve_jet_reparametrization (L i) with
    ⟨_, _, _, _, _, _, _, _, _, hshift⟩
  exact hshift j k h

end HolomorphicAnosov.Ghys
