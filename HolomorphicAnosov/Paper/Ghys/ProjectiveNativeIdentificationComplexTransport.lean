import HolomorphicAnosov.Geometry.NativeReceivingBiholomorphs
import HolomorphicAnosov.Geometry.NativePartitionComplexStructure
import HolomorphicAnosov.Geometry.NativeTransverseAsymptoticIdentification
import HolomorphicAnosov.Paper.Zhang.Anosov

/-! Complex charts on intrinsic unstable leaves make the native unstable identifications
biholomorphic and the leaf inclusions holomorphic immersions. -/

noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff Manifold
namespace HolomorphicAnosov.Ghys

universe u

attribute [local instance] complex_isManifold_real

/-- The intrinsic unstable leaves admit complex charts making their inclusions holomorphic
immersions and their point-preserving native identifications biholomorphic. (Ghys, §§2–3
pp.588–593; Lee, Prop.1.15 p.9) -/
theorem projective_native_identification_complex_transport
    {d : ℕ} {M : Type u} [MetricSpace M] [CompactSpace M]
    [SecondCountableTopology M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (s : ℕ)
    (A : NativeTransverseAsymptoticIdentification.{u, u}
      f.toHomeomorph a.splitting.stable.toDistribution
      a.splitting.unstable.toDistribution s 2) :
    letI := A.realAmbientCharts
    ∃ C : IntrinsicComplexUnstableLeaves A.F,
      (∀ q : Quotient A.F.unstablePartition,
        letI := A.F.unstableTopology q
        letI := C.charts q
        ContMDiff (complexModel 1) (complexModel d) ∞
          (Subtype.val : IntrinsicFoliationLeaf A.F.unstablePartition q → M) ∧
        ∀ z : IntrinsicFoliationLeaf A.F.unstablePartition q,
          Manifold.IsImmersionAt (complexModel 1) (complexModel d) ∞
            (Subtype.val : IntrinsicFoliationLeaf A.F.unstablePartition q → M) z) ∧
      (∀ x : M,
        letI := A.F.unstableTopology (Quotient.mk A.F.unstablePartition x)
        letI := C.charts (Quotient.mk A.F.unstablePartition x)
        letI := A.F.unstableCharts (Quotient.mk A.F.unstablePartition x)
        letI := (A.nativeU x).topology
        letI := (A.nativeU x).charts
        letI := (A.complexU1 x).charts
        ContMDiff (complexModel 1) (complexModel 1) ∞ (A.unstableIdentification x) ∧
          ContMDiff (complexModel 1) (complexModel 1) ∞
            (A.unstableIdentification x).symm) := by
  let := A.realAmbientCharts
  obtain ⟨C, hC⟩ := native_partition_complex_structure A
  obtain ⟨E, hE⟩ := native_receiving_biholomorphs A C hC
  refine ⟨C, hC, ?_⟩
  intro x
  let := A.F.unstableTopology (Quotient.mk A.F.unstablePartition x)
  let := C.charts (Quotient.mk A.F.unstablePartition x)
  let := A.F.unstableCharts (Quotient.mk A.F.unstablePartition x)
  let := (A.nativeU x).topology
  let := (A.nativeU x).charts
  let := (A.complexU1 x).charts
  have hf : (E x : _ → _) = (A.unstableIdentification x : _ → _) := by
    exact congrArg (fun H : A.F.ULeaf x ≃ₜ UnstableAsymptoticLeaf f.toHomeomorph x ↦ (H : _ → _)) (hE x)
  have hi : ((E x).symm : _ → _) = ((A.unstableIdentification x).symm : _ → _) := by
    exact congrArg (fun H : A.F.ULeaf x ≃ₜ UnstableAsymptoticLeaf f.toHomeomorph x ↦ (H.symm : _ → _)) (hE x)
  exact ⟨hf ▸ (E x).contMDiff, hi ▸ (E x).symm.contMDiff⟩


end HolomorphicAnosov.Ghys
