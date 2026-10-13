import HolomorphicAnosov.Paper.Ghys.Proposition31AffineFamily
import HolomorphicAnosov.Paper.Ghys.IntrinsicPresentationHolonomyHolomorphic
import HolomorphicAnosov.Paper.Ghys.Proposition41SchwarzianVanishing

noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff Manifold
namespace HolomorphicAnosov.Ghys
universe u
attribute [local instance] complex_isManifold_real

/-- Every native smooth presentation has projective holonomy in affine coordinates. (Ghys, Propositions 3.1 and 4.1) -/
theorem native_presentation_projective_holonomy
    {d : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (hRank : HasComplexRankOne a.splitting.unstable.toDistribution)
    (P : AnosovIntrinsicFoliationPresentation f a) :
      letI := P.realCharts
      ∃ A : AffineUnstableLeafStructures P.foliations P.complexLeaves,
        A.ActsAffinely P.foliations P.complexLeaves f ∧
        A.ContinuousAlongStableHolonomy P.foliations P.complexLeaves ∧
        (∀ B : AffineUnstableLeafStructures P.foliations P.complexLeaves,
          B.ActsAffinely P.foliations P.complexLeaves f →
          B.ContinuousAlongStableHolonomy P.foliations P.complexLeaves → B = A) ∧
        (∀ q : Quotient P.foliations.unstablePartition,
          letI := P.foliations.unstableTopology q
          letI := P.complexLeaves.charts q
          ComplexAffineStructure.Complete
            (IntrinsicFoliationLeaf P.foliations.unstablePartition q) (A.structureAt q)) ∧
        (∀ (q : Quotient P.foliations.stablePartition)
          (x y : IntrinsicFoliationLeaf P.foliations.stablePartition q) (γ : Path x y)
          (H : PathHolonomyRepresentative P.foliations γ 0 1)
          (c : OpenPartialHomeomorph (P.foliations.ULeaf (γ 0).val) ℂ)
          (e : OpenPartialHomeomorph (P.foliations.ULeaf (γ 1).val) ℂ),
          (letI := P.complexLeaves.charts
              (Quotient.mk P.foliations.unstablePartition (γ 0).val);
            c ∈ ComplexAffineStructure.maximalAtlas _
              (A.atPoint P.foliations P.complexLeaves (γ 0).val)) →
          (letI := P.complexLeaves.charts
              (Quotient.mk P.foliations.unstablePartition (γ 1).val);
            e ∈ ComplexAffineStructure.maximalAtlas _
              (A.atPoint P.foliations P.complexLeaves (γ 1).val)) →
          P.foliations.uPoint (γ 0).val ∈ c.source →
          P.foliations.uPoint (γ 1).val ∈ e.source →
          ∃ g : ComplexMobiusTransformation,
            ∀ᶠ z in 𝓝 (P.foliations.uPoint (γ 0).val),
              z ∈ H.map.source ∧ z ∈ c.source ∧ H.map z ∈ e.source ∧
                complexProjectiveLineFinite (e (H.map z)) =
                  g.apply (complexProjectiveLineFinite (c z))) := by
  let := P.realCharts
  obtain ⟨A, hAct, hCont, hUnique, hComplete⟩ := proposition31_affine_family f a hRank P
  refine ⟨A, hAct, hCont, hUnique, hComplete, ?_⟩
  intro q x y γ H c e hc he hxc hye
  by_cases hEmpty : IsEmpty M
  · let := hEmpty
    exact isEmptyElim x.val
  ·
    let : ∀ w : M, ChartedSpace (ComplexModel 1) (P.foliations.ULeaf w) :=
      fun w ↦ P.complexLeaves.charts (Quotient.mk P.foliations.unstablePartition w)
    let : ∀ w : M, IsManifold (complexModel 1) ∞ (P.foliations.ULeaf w) :=
      fun w ↦ P.complexLeaves.complex_manifold
        (Quotient.mk P.foliations.unstablePartition w)
    have hxe : H.map (P.foliations.uPoint (γ 0).val) ∈ e.source := by
      rw [H.map_point]
      exact hye
    have hAnalytic : IsHolomorphicCurveLocalMap H.map ∧
        ∀ᶠ w in 𝓝 (c (P.foliations.uPoint (γ 0).val)),
          schwarzian (affineLocalMapExpression c H.map e) w = 0 := by
      refine ⟨intrinsicPresentation_holonomy_holomorphic f a hRank P q x y γ 0 1 H, ?_⟩
      exact proposition_4_1_schwarzian_vanishing f a hRank P A hAct hCont hComplete
        q x y γ H c e hc he hxc hye
        (intrinsicPresentation_holonomy_holomorphic f a hRank P q x y γ 0 1 H)
    obtain ⟨_, _, _, _, hcriterion, _, _⟩ := schwarzian_affine_curve_calculus
      (A.atPoint P.foliations P.complexLeaves (γ 0).val)
      (A.atPoint P.foliations P.complexLeaves (γ 1).val)
      (A.atPoint P.foliations P.complexLeaves (γ 0).val)
      H.map hAnalytic.1 c e hc he (P.foliations.uPoint (γ 0).val)
      hxc H.source_point hxe
    obtain ⟨g, hg⟩ := hcriterion.mp hAnalytic.2
    refine ⟨g, ?_⟩
    have hg' := (c.continuousAt hxc).eventually hg
    have he' := (H.map.continuousAt H.source_point).eventually
      (e.open_source.mem_nhds hxe)
    filter_upwards [H.map.open_source.mem_nhds H.source_point,
      c.open_source.mem_nhds hxc, he', hg'] with z hzh hzc hze hzg
    refine ⟨hzh, hzc, hze, ?_⟩
    simpa only [affineLocalMapExpression, c.left_inv hzc] using hzg

end HolomorphicAnosov.Ghys

