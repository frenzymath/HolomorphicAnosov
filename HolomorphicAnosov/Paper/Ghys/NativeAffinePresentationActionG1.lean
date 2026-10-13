import HolomorphicAnosov.Ghys.NativeInvariantJetGraphEquivG1
import HolomorphicAnosov.Ghys.AnosovIntrinsicFoliationPresentation

/-! The ambient dynamics acts affinely on leaf atlases transported by point-preserving
biholomorphisms. (Ghys, Prop. 3.1(i), Lemmas 3.2–3.3, pp. 590–592) -/
noncomputable section
open Set Filter _root_.Topology
open scoped Manifold ContDiff
namespace HolomorphicAnosov.Ghys
universe u
attribute [local instance] complex_isManifold_real curveScalarToProductChartedSpace

/-- Point-preserving transport of the maximal leaf atlases makes the ambient dynamics affine. (Ghys,
Prop. 3.1(i), Lemmas 3.2–3.3, pp. 590–592) -/
theorem native_affine_presentation_action_g1
    {d : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (P : AnosovIntrinsicFoliationPresentation f a)
    {ι : Type u} (L : ι → Type u)
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
    [∀ i, ChartedSpace ℂ (L i)] [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]
    (U : HPS.LeafPartition a.splitting.unstable.toDistribution ι L (fun _ ↦ 2))
    (G : NativeInvariantJetAffineLeafFamily f a L U)
    : letI := P.realCharts
    ∀ (A : AffineUnstableLeafStructures P.foliations P.complexLeaves),
      (∀ q : Quotient P.foliations.unstablePartition,
        letI := P.foliations.unstableTopology q
        letI := P.complexLeaves.charts q
        ∃ (i : ι) (T : Diffeomorph (complexModel 1) (complexModel 1) (L i)
            (IntrinsicFoliationLeaf P.foliations.unstablePartition q) ∞),
          (∀ z, (T z).val = (U.leaf i).inclusion z) ∧
          ∀ e : OpenPartialHomeomorph
              (IntrinsicFoliationLeaf P.foliations.unstablePartition q) ℂ,
            e ∈ ComplexAffineStructure.maximalAtlas _ (A.structureAt q) ↔
              T.toHomeomorph.toOpenPartialHomeomorph.trans e ∈
                ComplexAffineStructure.maximalAtlas _ (G.affineAt f a L U i)) →
      A.ActsAffinely P.foliations P.complexLeaves f := by
  let := P.realCharts
  intro A hA x c e hc he hxc hxe
  let := P.foliations.unstableTopology (Quotient.mk P.foliations.unstablePartition x)
  let := P.complexLeaves.charts (Quotient.mk P.foliations.unstablePartition x)
  let := P.foliations.unstableTopology (Quotient.mk P.foliations.unstablePartition (f x))
  let := P.complexLeaves.charts (Quotient.mk P.foliations.unstablePartition (f x))
  obtain ⟨i, S, hS, hSc⟩ := hA (Quotient.mk P.foliations.unstablePartition x)
  obtain ⟨j, T, hT, hTc⟩ := hA (Quotient.mk P.foliations.unstablePartition (f x))
  let z₀ := S.symm (P.foliations.uPoint x)
  have hz₀ : (U.leaf i).inclusion z₀ = x := by
    rw [← hS]
    simp [z₀, TransverseContinuousFoliations.uPoint]
  have hj : G.permutation i = j := by
    apply U.disjoint (G.permutation i) j ((G.leafMap i) z₀)
      (T.symm (P.foliations.uPoint (f x)))
    rw [G.leafMap_inclusion, hz₀, ← hT]
    simp [TransverseContinuousFoliations.uPoint]
  subst j
  let c₀ := S.toHomeomorph.toOpenPartialHomeomorph.trans c
  let e₀ := T.toHomeomorph.toOpenPartialHomeomorph.trans e
  let e₁ := (G.leafMap i).toHomeomorph.toOpenPartialHomeomorph.trans e₀
  have hc₀ : c₀ ∈ ComplexAffineStructure.maximalAtlas _ (G.affineAt f a L U i) :=
    (hSc c).mp hc
  have he₁ : e₁ ∈ ComplexAffineStructure.maximalAtlas _ (G.affineAt f a L U i) :=
    native_invariant_affine_chart_pullback_g1 f a L U G i e₀ ((hTc e).mp he)
  have hTeq : T ((G.leafMap i) z₀) = P.foliations.uPoint (f x) := by
    apply Subtype.ext
    rw [hT, G.leafMap_inclusion, hz₀]
    rfl
  have hmem : z₀ ∈ c₀.source ∩ e₁.source := by
    constructor
    · simpa [c₀, z₀] using hxc
    · simpa [e₁, e₀, hTeq] using hxe
  obtain ⟨d₀, hd₀, hzd₀⟩ := (G.affineAt f a L U i).out.cover z₀
  obtain ⟨b₁, hb₁⟩ := hc₀.2 d₀ hd₀ z₀ ⟨hzd₀, hmem.1⟩
  obtain ⟨b₂, hb₂⟩ := he₁.2 d₀ hd₀ z₀ ⟨hzd₀, hmem.2⟩
  let b : ComplexAffineTransformation :=
    ⟨b₂.slope / b₁.slope, div_ne_zero b₂.slope_ne_zero b₁.slope_ne_zero,
      b₂.translation - (b₂.slope / b₁.slope) * b₁.translation⟩
  have htransition : ∀ᶠ z in 𝓝 z₀, e₁ z = b.apply (c₀ z) := by
    filter_upwards [hb₁, hb₂] with z hz₁ hz₂
    rw [hz₁, hz₂]
    dsimp [b, ComplexAffineTransformation.apply]
    field_simp [b₁.slope_ne_zero]
    ring
  let R : P.foliations.ULeaf x → P.foliations.ULeaf (f x) :=
    fun y ↦ T ((G.leafMap i) (S.symm y))
  have hRcont : Continuous R := T.continuous.comp ((G.leafMap i).continuous.comp S.symm.continuous)
  have hRx : R (P.foliations.uPoint x) = P.foliations.uPoint (f x) := hTeq
  refine ⟨b, ?_⟩
  have ht := S.symm.continuous.tendsto (P.foliations.uPoint x) htransition
  have hevent : ∀ᶠ y in 𝓝 (P.foliations.uPoint x), R y ∈ e.source :=
    hRcont.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds (hRx ▸ hxe))
  filter_upwards [ht, c.open_source.mem_nhds hxc, hevent] with y hy hyc hye
  refine ⟨hyc, R y, ?_, hye, ?_⟩
  · change (T ((G.leafMap i) (S.symm y))).val = _
    rw [hT, G.leafMap_inclusion, ← hS]
    simp
  · simpa [e₁, e₀, c₀, R, OpenPartialHomeomorph.trans_apply] using hy

end HolomorphicAnosov.Ghys
