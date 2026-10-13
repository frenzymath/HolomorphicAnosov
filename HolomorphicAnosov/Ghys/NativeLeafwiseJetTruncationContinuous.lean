import HolomorphicAnosov.Ghys.NativeLeafwiseParametrizationJetBundle

/-! This module proves continuity of native jet truncation in the flowbox coefficient topologies. (Ghys, §3) -/

noncomputable section
namespace HolomorphicAnosov.Ghys
open Set Filter Topology _root_.Topology
open scoped Manifold ContDiff
universe u
variable {ι : Type u} (L : ι → Type u)
variable [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace ℂ (L i)]
variable [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]
variable {d : ℕ} {M : Type u} [TopologicalSpace M]
variable [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
attribute [local instance] complex_isManifold_real
variable [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
variable [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
variable {D : RealTangentDistribution (realModel d) M}

omit [IsManifold (complexModel d) ∞ M] in
/-- Truncation is continuous in the full transverse coefficient topology when all scalar box coordinates are complex smooth along the original leaves on their source. (Ghys, §3) -/
theorem nativeLeafwiseJetTruncation_continuous
    (U : HPS.LeafPartition D ι L (fun _ ↦ 2)) {n s : ℕ}
    (c : Fin n → OpenPartialHomeomorph M (ℂ × (Fin s → ℝ)))
    (hscalar : ∀ k i z, (U.leaf i).inclusion z ∈ (c k).source →
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞ (nativeLeafFlowboxScalar L U (c k) i) z) :
    @Continuous (NativeLeafwiseJet2 L) (NativeLeafwiseJet1 L)
      (nativeLeafwiseJet2Topology L U c) (nativeLeafwiseJet1Topology L U c)
      (nativeLeafwiseJetTruncation L) := by
  have hformula (i : ι) (φ : L i → ℂ) (γ : CurveParamGerm (L i))
      (e : LeafChart (L i)) (he : curveGermBase (L i) γ.1 ∈ e.1.source)
      (hφ : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞ φ (curveGermBase (L i) γ.1)) :
      germFirst (γ.1.map φ) =
        deriv (φ ∘ e.1.symm) (e.1 (curveGermBase (L i) γ.1)) *
          curveGermFirst (L i) e γ := by
    obtain ⟨g, hg0, hg, _, hge⟩ := γ.2
    have hb : curveGermBase (L i) γ.1 = g 0 := by rw [← hge]; rfl
    rw [hb] at he hφ ⊢
    have hg' := hg.contMDiffAt (g.open_source.mem_nhds hg0)
    have hc := (contMDiffAt_of_mem_maximalAtlas e.2 he).comp 0 hg'
    have hi := contMDiffAt_symm_of_mem_maximalAtlas e.2 (e.1.map_source he)
    have hφ' : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞ φ (e.1.symm (e.1 (g 0))) := by
      simpa only [e.1.left_inv he] using hφ
    have hh := (hφ'.comp _ hi).contDiffAt.differentiableAt (by simp)
    have heq : (φ ∘ g) =ᶠ[𝓝 (0 : ℂ)] (φ ∘ e.1.symm) ∘ (e.1 ∘ g) := by
      filter_upwards [hg'.continuousAt.preimage_mem_nhds (e.1.open_source.mem_nhds he)] with t ht
      simp only [Function.comp_apply, e.1.left_inv ht]
    unfold curveGermFirst
    rw [← hge]
    change deriv (φ ∘ g) 0 = _ * deriv (e.1 ∘ g) 0
    rw [heq.deriv_eq, deriv_comp 0 hh (hc.contDiffAt.differentiableAt (by simp))]
    rfl
  have hbase (j : NativeLeafwiseJet2 L) :
      nativeLeafwiseJet1Base L U (nativeLeafwiseJetTruncation L j) =
        nativeLeafwiseJet2Base L U j := by
    have hr : CurveContact1 (L j.1) (curveJetTruncation (L j.1) j.2).out j.2.out :=
      Quotient.exact ((Quotient.out_eq _).trans
        (congrArg (curveJetTruncation (L j.1)) (Quotient.out_eq j.2)).symm)
    exact congrArg (U.leaf j.1).inclusion hr.1
  have hcoeff (k : Fin n) (j : NativeLeafwiseJet2 L)
      (hj : nativeLeafwiseJet2Base L U j ∈ (c k).source) :
      nativeLeafwiseJet1Coeff L U (c k) (nativeLeafwiseJetTruncation L j) =
        (nativeLeafwiseJet2Coeff L U (c k) j).1 := by
    have hr : CurveContact1 (L j.1) (curveJetTruncation (L j.1) j.2).out j.2.out :=
      Quotient.exact ((Quotient.out_eq _).trans
        (congrArg (curveJetTruncation (L j.1)) (Quotient.out_eq j.2)).symm)
    obtain ⟨hb, e, he, ha⟩ := hr
    apply Prod.ext
    · exact congrArg (c k) (hbase j)
    · change germFirst ((curveJetTruncation (L j.1) j.2).out.1.map
          (nativeLeafFlowboxScalar L U (c k) j.1)) =
        germFirst (j.2.out.1.map (nativeLeafFlowboxScalar L U (c k) j.1))
      change (U.leaf j.1).inclusion (curveGermBase (L j.1) j.2.out.1) ∈ (c k).source at hj
      rw [hformula j.1 _ _ e he (hscalar k j.1 _ (by simpa only [hb] using hj)),
        hformula j.1 _ _ e (hb ▸ he) (hscalar k j.1 _ hj), hb, ha]
  let := nativeLeafwiseJet2Topology L U c
  apply continuous_generateFrom_iff.mpr
  rintro S ⟨k, O, hO, rfl⟩
  have hset : (nativeLeafwiseJetTruncation L) ⁻¹'
      {j | nativeLeafwiseJet1Base L U j ∈ (c k).source ∧ nativeLeafwiseJet1Coeff L U (c k) j ∈ O} =
      {j | nativeLeafwiseJet2Base L U j ∈ (c k).source ∧
        nativeLeafwiseJet2Coeff L U (c k) j ∈ Prod.fst ⁻¹' O} := by
    ext j
    simp only [mem_preimage, mem_ofPred_eq, hbase]
    exact and_congr_right (fun hj ↦ by rw [hcoeff k j hj])
  rw [hset]
  exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨k, Prod.fst ⁻¹' O,
    hO.preimage continuous_fst, rfl⟩

end HolomorphicAnosov.Ghys
