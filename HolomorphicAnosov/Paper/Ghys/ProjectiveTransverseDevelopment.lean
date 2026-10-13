import HolomorphicAnosov.Paper.Ghys.NativeAffineTransverseProjectiveAtlas
import HolomorphicAnosov.Geometry.ComplexMobiusPSLNormalization
import HolomorphicAnosov.Geometry.NativePartitionComplexStructure
import HolomorphicAnosov.Geometry.NativeReceivingBiholomorphs
import HolomorphicAnosov.Paper.Ghys.ProjectiveLocalGermsEffectiveCocycle
import HolomorphicAnosov.Ghys.AffineProjectiveStructure
import HolomorphicAnosov.Ghys.AnosovIntrinsicFoliationPresentation
import HolomorphicAnosov.Geometry.NativeTransverseAsymptoticIdentification
import HolomorphicAnosov.Paper.Zhang.Anosov

/-! The intrinsic unstable leaves carry compatible complex charts, complete affine structures, and a
transverse projective atlas. (Ghys, §5 p.597) -/

noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff Manifold
namespace HolomorphicAnosov.Ghys

universe u

attribute [local instance] complex_isManifold_real

/-- The intrinsic unstable leaves admit compatible complex charts and complete affine structures
with a transverse projective atlas locally expressed by PSL transformations of affine
coordinates. (Ghys, Props.2.2,3.1,4.1 and §5 p.597) -/
theorem projective_transverse_development
    {d : ℕ} {M : Type u} [MetricSpace M] [CompactSpace M]
    [SecondCountableTopology M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (hu : ∀ x : M,
      Module.finrank ℝ (a.splitting.unstable.toDistribution x) = 2)
    (s : ℕ)
    (A : NativeTransverseAsymptoticIdentification.{u, u}
      f.toHomeomorph a.splitting.stable.toDistribution
      a.splitting.unstable.toDistribution s 2) :
    letI := A.realAmbientCharts
    ∃ C : IntrinsicComplexUnstableLeaves A.F,
    (∀ x : M,
      letI := A.F.unstableTopology (Quotient.mk A.F.unstablePartition x)
      letI := C.charts (Quotient.mk A.F.unstablePartition x)
      letI := A.F.unstableCharts (Quotient.mk A.F.unstablePartition x)
      letI := (A.nativeU x).topology
      letI := (A.nativeU x).charts
      letI := (A.complexU1 x).charts
      ContMDiff (complexModel 1) (complexModel 1) ∞ (A.unstableIdentification x) ∧
        ContMDiff (complexModel 1) (complexModel 1) ∞ (A.unstableIdentification x).symm) ∧
    (∀ x : M,
      letI := A.F.unstableTopology (Quotient.mk A.F.unstablePartition x)
      letI := C.charts (Quotient.mk A.F.unstablePartition x)
      ContMDiff (complexModel 1) (complexModel d) ∞
        (Subtype.val : A.F.ULeaf x → M)) ∧
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
        z ∈ b.source ∧ ∃ g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ,
          ∀ᶠ w in 𝓝 z,
            w ∈ b.source ∧ w.val ∈ c.domain A.F C ∧
              c.transverseCoordinate A.F C w.val = g • complexProjectiveLineFinite (b w)) := by
  classical
  let := A.realAmbientCharts
  obtain ⟨C, hC⟩ := native_partition_complex_structure A
  obtain ⟨e, he⟩ := native_receiving_biholomorphs A C hC
  refine ⟨C, ?_, ?_, ?_⟩
  · intro x
    let := A.F.unstableTopology (Quotient.mk A.F.unstablePartition x)
    let := C.charts (Quotient.mk A.F.unstablePartition x)
    let := A.F.unstableCharts (Quotient.mk A.F.unstablePartition x)
    let := (A.nativeU x).topology
    let := (A.nativeU x).charts
    let := (A.complexU1 x).charts
    have hforward : (e x : A.F.ULeaf x → UnstableAsymptoticLeaf f.toHomeomorph x) =
        A.unstableIdentification x := by
      funext z
      exact congrArg (fun h : A.F.ULeaf x ≃ₜ UnstableAsymptoticLeaf f.toHomeomorph x ↦ h z) (he x)
    have hinverse : ((e x).symm : UnstableAsymptoticLeaf f.toHomeomorph x → A.F.ULeaf x) =
        (A.unstableIdentification x).symm :=
      by
      funext z
      exact congrArg (fun h : A.F.ULeaf x ≃ₜ UnstableAsymptoticLeaf f.toHomeomorph x ↦ h.symm z) (he x)
    exact ⟨hforward ▸ (e x).contMDiff, hinverse ▸ (e x).symm.contMDiff⟩
  · intro x
    exact (hC (Quotient.mk A.F.unstablePartition x)).1
  · obtain ⟨affine, hcomplete, atlas, hagree⟩ :=
      native_affine_transverse_projective_atlas f a hu s A C hC
    refine ⟨affine, hcomplete, atlas, ?_⟩
    intro c hc x z hz
    obtain ⟨b, hb, hzb, g, hg⟩ := hagree c hc x z hz
    obtain ⟨g', hg', _⟩ := complex_mobius_psl_normalization g
    refine ⟨b, hb, hzb, g', ?_⟩
    filter_upwards [hg] with w hw
    exact ⟨hw.1, hw.2.1, hw.2.2.trans (hg' _).symm⟩


end HolomorphicAnosov.Ghys
