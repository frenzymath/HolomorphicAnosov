import HolomorphicAnosov.Ghys.LeafJetComplexManifold

namespace HolomorphicAnosov.Ghys

open Set Topology _root_.Topology
open scoped Topology _root_.Topology Manifold ContDiff

universe u v

variable {Q : Type u} {L : Q → Type u}
variable [∀ q, TopologicalSpace (L q)] [∀ q, ChartedSpace ℂ (L q)]
  [∀ q, IsManifold (modelWithCornersSelf ℂ ℂ) ∞ (L q)]
  [∀ q, T2Space (L q)] [∀ q, SecondCountableTopology (L q)]

/-- The canonical coefficient charts of the leafwise curve-jet manifold vary uniformly over the leaf family. (Ghys, p. 591) -/
theorem jet_dynamics_leaf_chart_witness :
    ∃ (jetChart1 : ∀ q, ChartedSpace (ℂ × ℂ) (CurveJet1 (L q)))
      (jetChart2 : ∀ q, ChartedSpace ((ℂ × ℂ) × ℂ) (CurveJet2 (L q))),
    letI := jetChart1
    letI := jetChart2
    (∀ q, IsManifold (modelWithCornersSelf ℂ (ℂ × ℂ)) ∞ (CurveJet1 (L q)) ∧
      IsManifold (modelWithCornersSelf ℂ ((ℂ × ℂ) × ℂ)) ∞ (CurveJet2 (L q))) ∧
    (∀ q (b : LeafChart (L q)),
      ∃ (e₁ : OpenPartialHomeomorph (CurveJet1 (L q)) (ℂ × ℂ))
        (e₂ : OpenPartialHomeomorph (CurveJet2 (L q)) ((ℂ × ℂ) × ℂ)),
        e₁ ∈ atlas (ℂ × ℂ) (CurveJet1 (L q)) ∧
        e₂ ∈ atlas ((ℂ × ℂ) × ℂ) (CurveJet2 (L q)) ∧
        e₁.source = curveJet1Base (L q) ⁻¹' b.val.source ∧
        e₂.source = curveJet2Base (L q) ⁻¹' b.val.source ∧
        e₁.target = curveJet1Target (L q) b ∧ e₂.target = curveJet2Target (L q) b ∧
        EqOn e₁ (curveJet1Coeff (L q) b) e₁.source ∧
        EqOn e₂ (curveJet2Coeff (L q) b) e₂.source) := by
  classical
  let jetChart1 : ∀ q, ChartedSpace (ℂ × ℂ) (CurveJet1 (L q)) :=
    fun q ↦ (leaf_jet_complex_manifold (L := L q)).2.2.2.2.choose
  let jetChart2 : ∀ q, ChartedSpace ((ℂ × ℂ) × ℂ) (CurveJet2 (L q)) :=
    fun q ↦ (leaf_jet_complex_manifold (L := L q)).2.2.2.2.choose_spec.choose
  refine ⟨jetChart1, jetChart2, ?_, ?_⟩
  · intro q
    have h := (leaf_jet_complex_manifold (L := L q)).2.2.2.2.choose_spec.choose_spec
    let := jetChart1 q
    let := jetChart2 q
    rcases h with ⟨_, _, _, _, hm1, hm2, _, _, _, _, _, hcharts, _, _⟩
    exact ⟨hm1, hm2⟩
  · intro q b
    have h := (leaf_jet_complex_manifold (L := L q)).2.2.2.2.choose_spec.choose_spec
    let := jetChart1 q
    let := jetChart2 q
    rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, hcharts, _, _⟩
    rcases hcharts b with
      ⟨e₁, e₂, he₁, he₂, hs₁, hs₂, ht₁, ht₂, hc₁, hc₂, _, _, _, _⟩
    exact ⟨e₁, e₂, he₁, he₂, hs₁, hs₂, ht₁, ht₂, hc₁, hc₂⟩


end HolomorphicAnosov.Ghys
