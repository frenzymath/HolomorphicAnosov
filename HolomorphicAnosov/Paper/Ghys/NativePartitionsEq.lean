import HolomorphicAnosov.Geometry.NativeTransverseAsymptoticIdentification
import HolomorphicAnosov.Paper.Ghys.PartitionRelationOfPointIdentification
import HolomorphicAnosov.Paper.Zhang.Anosov

namespace HolomorphicAnosov.Ghys
open scoped ContDiff Manifold
universe u v w
attribute [local instance] complex_isManifold_real
/-- Any two native identifications of the same dynamics induce identical stable and unstable point partitions. (Ghys, §§2, 5) -/
theorem native_identification_partitions_eq
    {d s t s' t' : ℕ} {M : Type u} [MetricSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (realModel d) ∞ M] [T2Space M] [SecondCountableTopology M]
    (f : M ≃ₜ M) (Ps Pu : RealTangentDistribution (realModel d) M)
    (A : NativeTransverseAsymptoticIdentification.{u, v} (d := d)
      f Ps Pu s t)
    (B : NativeTransverseAsymptoticIdentification.{u, w} (d := d)
      f Ps Pu s' t') :
    (letI := A.realAmbientCharts; A.F.stablePartition) =
        (letI := B.realAmbientCharts; B.F.stablePartition) ∧
      (letI := A.realAmbientCharts; A.F.unstablePartition) =
        (letI := B.realAmbientCharts; B.F.unstablePartition) := by
  let AS := letI := A.realAmbientCharts; A.F.stablePartition
  let BS := letI := B.realAmbientCharts; B.F.stablePartition
  let AU := letI := A.realAmbientCharts; A.F.unstablePartition
  let BU := letI := B.realAmbientCharts; B.F.unstablePartition
  have hAS : ∀ x y, AS.r x y ↔ ForwardAsymptotic f x y := by
    let := A.realAmbientCharts
    exact partition_relation_of_point_identification AS (ForwardAsymptotic f)
      (fun x ↦
        letI := A.F.stableTopology (Quotient.mk A.F.stablePartition x)
        letI := A.stableTopology x
        (A.stableClassHomeomorph x).toEquiv) A.stable_points
  have hBS : ∀ x y, BS.r x y ↔ ForwardAsymptotic f x y := by
    let := B.realAmbientCharts
    exact partition_relation_of_point_identification BS (ForwardAsymptotic f)
      (fun x ↦
        letI := B.F.stableTopology (Quotient.mk B.F.stablePartition x)
        letI := B.stableTopology x
        (B.stableClassHomeomorph x).toEquiv) B.stable_points
  have hAU : ∀ x y, AU.r x y ↔ ForwardAsymptotic f.symm x y := by
    let := A.realAmbientCharts
    exact partition_relation_of_point_identification AU (ForwardAsymptotic f.symm)
      (fun x ↦
        letI := A.F.unstableTopology (Quotient.mk A.F.unstablePartition x)
        letI := A.unstableTopology x
        (A.unstableClassHomeomorph x).toEquiv) A.unstable_points
  have hBU : ∀ x y, BU.r x y ↔ ForwardAsymptotic f.symm x y := by
    let := B.realAmbientCharts
    exact partition_relation_of_point_identification BU (ForwardAsymptotic f.symm)
      (fun x ↦
        letI := B.F.unstableTopology (Quotient.mk B.F.unstablePartition x)
        letI := B.unstableTopology x
        (B.unstableClassHomeomorph x).toEquiv) B.unstable_points
  constructor
  · exact Setoid.ext fun x y ↦ (hAS x y).trans (hBS x y).symm
  · exact Setoid.ext fun x y ↦ (hAU x y).trans (hBU x y).symm


/-- Any two native identifications of the same dynamics induce identical stable and unstable point partitions. (Ghys, §§2, 5) -/
theorem native_partitions_eq
    {d s s' : ℕ} {M : Type u} [MetricSpace M]
    [ChartedSpace (ComplexModel d) M] [IsCompactComplexManifold d M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (A : NativeTransverseAsymptoticIdentification.{u, v} (d := d)
      f.toHomeomorph a.splitting.stable.toDistribution
      a.splitting.unstable.toDistribution s 2)
    (B : NativeTransverseAsymptoticIdentification.{u, w} (d := d)
      f.toHomeomorph a.splitting.stable.toDistribution
      a.splitting.unstable.toDistribution s' 2) :
    (letI := A.realAmbientCharts; A.F.stablePartition) =
        (letI := B.realAmbientCharts; B.F.stablePartition) ∧
      (letI := A.realAmbientCharts; A.F.unstablePartition) =
        (letI := B.realAmbientCharts; B.F.unstablePartition) := by
  exact native_identification_partitions_eq f.toHomeomorph
    a.splitting.stable.toDistribution a.splitting.unstable.toDistribution A B

end HolomorphicAnosov.Ghys
