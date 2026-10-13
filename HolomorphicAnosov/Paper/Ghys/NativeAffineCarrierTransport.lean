import HolomorphicAnosov.Paper.Ghys.NativePresentationUnstableComparisonG19
import HolomorphicAnosov.Paper.Ghys.ProjectivePlaqueCoordinatesG19
import HolomorphicAnosov.Paper.Ghys.NativePresentationProjectiveHolonomyG19

noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff Manifold
namespace HolomorphicAnosov.Ghys
universe u
attribute [local instance] complex_isManifold_real curveScalarToProductChartedSpace

/-- This theorem assembles the fixed-carrier conclusion from native projective presentations. (HPS, §7; Ghys, §§4–5) -/
theorem native_affine_carrier_assembly
    {d : ℕ} {M : Type u} [MetricSpace M] [CompactSpace M]
    [SecondCountableTopology M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (s : ℕ)
    (A : NativeTransverseAsymptoticIdentification.{u, u}
      f.toHomeomorph a.splitting.stable.toDistribution
      a.splitting.unstable.toDistribution s 2)
    (C : letI := A.realAmbientCharts; IntrinsicComplexUnstableLeaves A.F)
    (hC : letI := A.realAmbientCharts
      ∀ q : Quotient A.F.unstablePartition,
        letI := A.F.unstableTopology q
        letI := C.charts q
        ContMDiff (complexModel 1) (complexModel d) ∞
          (Subtype.val : IntrinsicFoliationLeaf A.F.unstablePartition q → M) ∧
        ∀ z : IntrinsicFoliationLeaf A.F.unstablePartition q,
          Manifold.IsImmersionAt (complexModel 1) (complexModel d) ∞
            (Subtype.val : IntrinsicFoliationLeaf A.F.unstablePartition q → M) z)
    (P : AnosovIntrinsicFoliationPresentation f a)
    (hFamily : ∀ Q : AnosovIntrinsicFoliationPresentation f a,
      letI := Q.realCharts
      ∃ affine : AffineUnstableLeafStructures Q.foliations Q.complexLeaves,
        (∀ q : Quotient Q.foliations.unstablePartition,
          letI := Q.foliations.unstableTopology q; letI := Q.complexLeaves.charts q
          ComplexAffineStructure.Complete _ (affine.structureAt q)) ∧
        FullBoxHolomorphic Q.foliations Q.complexLeaves ∧
        FullBoxProjectiveHolonomy Q.foliations Q.complexLeaves affine) :
    letI := A.realAmbientCharts
    ∃ affine : AffineUnstableLeafStructures A.F C,
    (∀ q : Quotient A.F.unstablePartition,
      letI := A.F.unstableTopology q
      letI := C.charts q
      ComplexAffineStructure.Complete _ (affine.structureAt q)) ∧
    ∃ atlas : TransverseProjectiveAtlas A.F C,
    (∀ c ∈ atlas.charts, ∀ x : M, ∀ z : A.F.ULeaf x,
      letI := A.F.unstableTopology (Quotient.mk A.F.unstablePartition x)
      letI := C.charts (Quotient.mk A.F.unstablePartition x)
      z.val ∈ c.domain A.F C →
      ∃ b ∈ ComplexAffineStructure.maximalAtlas _ (affine.atPoint A.F C x),
        z ∈ b.source ∧ ∃ g : ComplexMobiusTransformation,
          ∀ᶠ w in 𝓝 z,
            w ∈ b.source ∧ w.val ∈ c.domain A.F C ∧
              c.transverseCoordinate A.F C w.val = g.apply (complexProjectiveLineFinite (b w))) := by
  classical
  have hs := native_fixed_stable_dimension A
  subst s
  let := A.realAmbientCharts
  obtain ⟨B⟩ := native_fixed_carrier_smooth_data f a P A C hC
  let Q := fixedCarrierPresentation f a A C B (fun q ↦ (hC q).1)
  obtain ⟨affine,hComplete,hHol,hProj⟩ := hFamily Q
  have hsep : ∀ q : Quotient Q.foliations.stablePartition,
      letI := Q.foliations.stableTopology q
      TopologicalSpace.SeparableSpace (IntrinsicFoliationLeaf Q.foliations.stablePartition q) := by
    intro q
    let := Q.foliations.stableTopology q
    let := Q.foliations.stableCharts q
    let := Q.stableSmooth q
    let := (Q.stableNative q).countable
    infer_instance
  obtain ⟨atlas,hAtlas⟩ := transverseProjectiveAtlas_of_complete_affine_holonomy
    Q.foliations Q.complexLeaves hsep affine hComplete hHol hProj
  exact fixedCarrier_transverse_atlas_transport f a A C B affine hComplete atlas hAtlas


/-- The fixed native partition carriers admit complete affine and transverse projective structures with the supplied intrinsic complex atlas. (Ghys, Props. 3.1 and 4.1) -/
theorem native_affine_carrier_transport
    {d : ℕ} {M : Type u} [MetricSpace M] [CompactSpace M]
    [SecondCountableTopology M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (hRank : HasComplexRankOne a.splitting.unstable.toDistribution)
    (s : ℕ)
    (A : NativeTransverseAsymptoticIdentification.{u, u}
      f.toHomeomorph a.splitting.stable.toDistribution
      a.splitting.unstable.toDistribution s 2)
    (C : letI := A.realAmbientCharts; IntrinsicComplexUnstableLeaves A.F)
    (hC : letI := A.realAmbientCharts
      ∀ q : Quotient A.F.unstablePartition,
        letI := A.F.unstableTopology q
        letI := C.charts q
        ContMDiff (complexModel 1) (complexModel d) ∞
          (Subtype.val : IntrinsicFoliationLeaf A.F.unstablePartition q → M) ∧
        ∀ z : IntrinsicFoliationLeaf A.F.unstablePartition q,
          Manifold.IsImmersionAt (complexModel 1) (complexModel d) ∞
            (Subtype.val : IntrinsicFoliationLeaf A.F.unstablePartition q → M) z) :
    letI := A.realAmbientCharts
    ∃ affine : AffineUnstableLeafStructures A.F C,
    (∀ q : Quotient A.F.unstablePartition,
      letI := A.F.unstableTopology q
      letI := C.charts q
      ComplexAffineStructure.Complete _ (affine.structureAt q)) ∧
    ∃ atlas : TransverseProjectiveAtlas A.F C,
    (∀ c ∈ atlas.charts, ∀ x : M, ∀ z : A.F.ULeaf x,
      letI := A.F.unstableTopology (Quotient.mk A.F.unstablePartition x)
      letI := C.charts (Quotient.mk A.F.unstablePartition x)
      z.val ∈ c.domain A.F C →
      ∃ b ∈ ComplexAffineStructure.maximalAtlas _ (affine.atPoint A.F C x),
        z ∈ b.source ∧ ∃ g : ComplexMobiusTransformation,
          ∀ᶠ w in 𝓝 z,
            w ∈ b.source ∧ w.val ∈ c.domain A.F C ∧
              c.transverseCoordinate A.F C w.val = g.apply (complexProjectiveLineFinite (b w))) := by
  obtain ⟨P,hP⟩ := proposition_3_1 f a hRank
  apply native_affine_carrier_assembly f a s A C hC P
  intro Q
  let := Q.realCharts
  obtain ⟨affine,hAct,hCont,hUnique,hComplete,hPath⟩ :=
    native_presentation_projective_holonomy f a hRank Q
  refine ⟨affine,hComplete,?_,?_⟩
  · intro b z z' w
    exact intrinsicPresentation_plaque_holomorphic f a hRank Q _ _
      (fullBoxPlaqueTransport Q.foliations b z z' w)
  · exact fullBoxProjectiveHolonomy_of_paths Q.foliations Q.complexLeaves affine hPath

end HolomorphicAnosov.Ghys
