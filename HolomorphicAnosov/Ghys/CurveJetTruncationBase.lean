import HolomorphicAnosov.Ghys.LeafJetComplexManifold

noncomputable section
namespace HolomorphicAnosov.Ghys
open scoped Manifold ContDiff
universe u

/-- Truncation from a second curve jet to a first curve jet preserves its base point. (Ghys, p.591;
Michor, Thm 1.10(6)(7), pp.6–7) -/
theorem curve_jet_truncation_base
    (L : Type u) [TopologicalSpace L] [ChartedSpace ℂ L]
    [IsManifold 𝓘(ℂ) ∞ L] [T2Space L] [SecondCountableTopology L]
    (q : CurveJet2 L) :
    curveJet1Base L (curveJetTruncation L q) = curveJet2Base L q := by
  obtain ⟨gamma, rfl⟩ := Quotient.exists_rep q
  have h1 : CurveContact1 L (curveJet1Class L gamma).out gamma :=
    Quotient.exact (Quotient.out_eq (curveJet1Class L gamma))
  have h2 : CurveContact2 L (curveJet2Class L gamma).out gamma :=
    Quotient.exact (Quotient.out_eq (curveJet2Class L gamma))
  exact h1.1.trans h2.1.symm

end HolomorphicAnosov.Ghys
