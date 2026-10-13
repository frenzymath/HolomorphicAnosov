import HolomorphicAnosov.Ghys.NativeInvariantJetAffineLeafFamily
import HolomorphicAnosov.Ghys.CurvePostcomposeJetEquivalences

/-! The invariant section graph is preserved and reflected by the native leaf biholomorphisms. (Ghys, Lemma 3.3) -/
noncomputable section
open Set Filter _root_.Topology
open scoped Manifold ContDiff
namespace HolomorphicAnosov.Ghys
universe u
attribute [local instance] complex_isManifold_real curveScalarToProductChartedSpace
variable {d : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
  (f : Biholomorph d d M M) (a : AnosovDatum f)
  {ι : Type u} (L : ι → Type u)
  [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
  [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
  [∀ i, ChartedSpace ℂ (L i)] [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]
  (U : HPS.LeafPartition a.splitting.unstable.toDistribution ι L (fun _ ↦ 2))


/-- The actual native leaf map preserves and reflects the section graph. (Ghys, Lemma 3.3) -/
theorem native_invariant_jet_graph_equiv_g1
    (G : NativeInvariantJetAffineLeafFamily f a L U) (i : ι)
    (gamma eta : CurveParamGerm (L i)) :
    G.jetSection (nativeLeafwiseJet1Inclusion L i (curveJet1Class (L i) gamma)) =
        nativeLeafwiseJet2Inclusion L i (curveJet2Class (L i) eta) ↔
      G.jetSection (nativeLeafwiseJet1Inclusion L (G.permutation i)
          (curveJet1Class (L (G.permutation i)) (curveParamGermPostcompose (G.leafMap i) gamma))) =
        nativeLeafwiseJet2Inclusion L (G.permutation i)
          (curveJet2Class (L (G.permutation i)) (curveParamGermPostcompose (G.leafMap i) eta)) := by
  have hforward (gamma eta : CurveParamGerm (L i))
      (h : G.jetSection (nativeLeafwiseJet1Inclusion L i (curveJet1Class (L i) gamma)) =
        nativeLeafwiseJet2Inclusion L i (curveJet2Class (L i) eta)) :
      G.jetSection (nativeLeafwiseJet1Inclusion L (G.permutation i)
          (curveJet1Class (L (G.permutation i)) (curveParamGermPostcompose (G.leafMap i) gamma))) =
        nativeLeafwiseJet2Inclusion L (G.permutation i)
          (curveJet2Class (L (G.permutation i)) (curveParamGermPostcompose (G.leafMap i) eta)) := by
    obtain ⟨delta, theta, hd, ht, hgraph⟩ := G.section_invariant i gamma eta h
    have hd' : delta = curveParamGermPostcompose (G.leafMap i) gamma := Subtype.ext hd
    have ht' : theta = curveParamGermPostcompose (G.leafMap i) eta := Subtype.ext ht
    simpa only [hd', ht'] using hgraph
  refine ⟨hforward gamma eta, ?_⟩
  intro h
  obtain ⟨tau, htau, _⟩ := G.leaf_holomorphic i
  obtain ⟨beta, hbeta⟩ := Quotient.exists_rep (tau (curveJet1Class (L i) gamma))
  change curveJet2Class (L i) beta = tau (curveJet1Class (L i) gamma) at hbeta
  have hsource : G.jetSection (nativeLeafwiseJet1Inclusion L i (curveJet1Class (L i) gamma)) =
      nativeLeafwiseJet2Inclusion L i (curveJet2Class (L i) beta) := by rw [htau, hbeta]
  have himages := (hforward gamma beta hsource).symm.trans h
  have heq : curveJet2Class (L (G.permutation i)) (curveParamGermPostcompose (G.leafMap i) beta) =
      curveJet2Class (L (G.permutation i)) (curveParamGermPostcompose (G.leafMap i) eta) :=
    eq_of_heq (Sigma.mk.inj_iff.mp himages).2
  obtain ⟨_, E2, _, hE2⟩ := curve_postcompose_jet_equivalences (G.leafMap i)
  have hbe : curveJet2Class (L i) beta = curveJet2Class (L i) eta := by
    apply E2.injective
    simpa only [hE2] using heq
  rwa [hbe] at hsource

/-- Pulling an affine chart back by the actual native dynamical leaf map gives an affine chart of the source leaf. (Ghys, Lemma 3.3) -/
theorem native_invariant_affine_chart_pullback_g1
    (G : NativeInvariantJetAffineLeafFamily f a L U) (i : ι)
    (e : OpenPartialHomeomorph (L (G.permutation i)) ℂ)
    (he : e ∈ ComplexAffineStructure.maximalAtlas _ (G.affineAt f a L U (G.permutation i))) :
    (G.leafMap i).toHomeomorph.toOpenPartialHomeomorph.trans e ∈
      ComplexAffineStructure.maximalAtlas _ (G.affineAt f a L U i) := by
  let c := (G.leafMap i).toHomeomorph.toOpenPartialHomeomorph.trans e
  have heflat := (G.flat_chart_iff (G.permutation i) e).mp he
  apply (G.flat_chart_iff i c).mpr
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact heflat.1.1.comp
      (curveScalarToProduct_contMDiff (G.leafMap i).contMDiff).contMDiffOn
      (fun _ hx ↦ hx.2)
  · have ht : c.target = e.target := by simp [c]
    change ContMDiffOn 𝓘(ℂ) (complexModel 1) ∞ c.symm c.target
    rw [ht]
    exact (curveScalarToProduct_contMDiff (G.leafMap i).symm.contMDiff).comp_contMDiffOn heflat.1.2
  · intro gamma hg
    have hbase : curveGermBase (L (G.permutation i))
        (curveParamGermPostcompose (G.leafMap i) gamma).1 =
        (G.leafMap i) (curveGermBase (L i) gamma.1) := by
      change curveGermBase _ (gamma.1.map (G.leafMap i : L i → L (G.permutation i))) = _
      induction gamma.1 using Filter.Germ.inductionOn with
      | h g => rfl
    have hg' : curveGermBase (L (G.permutation i))
        (curveParamGermPostcompose (G.leafMap i) gamma).1 ∈ e.source := by
      rw [hbase]
      exact hg.2
    have htarget := heflat.2 (curveParamGermPostcompose (G.leafMap i) gamma) hg'
    have hgerm : (curveParamGermPostcompose (G.leafMap i) gamma).1.map (e : _ → ℂ) =
        gamma.1.map (c : L i → ℂ) := by
      change (gamma.1.map (G.leafMap i : L i → L (G.permutation i))).map (e : _ → ℂ) = _
      rw [Filter.Germ.map_map]
      rfl
    rw [native_invariant_jet_graph_equiv_g1 f a L U G i gamma gamma, htarget, hgerm]

end HolomorphicAnosov.Ghys

