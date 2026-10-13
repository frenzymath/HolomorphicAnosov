import HolomorphicAnosov.Geometry.NativeTransverseAsymptoticIdentification

noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff Manifold
namespace HolomorphicAnosov
universe u

variable {d : ℕ} {M : Type u} [MetricSpace M]
  [ChartedSpace (ComplexModel d) M] [IsManifold (realModel d) ∞ M]
  [T2Space M] [SecondCountableTopology M]

/-- A point-preserving identification equates the stable partition relation with forward
asymptoticity. -/
theorem native_identification_stable_partition_iff_asymptotic
    {f : M ≃ₜ M} {Ps Pu : RealTangentDistribution (realModel d) M}
    {s t : ℕ}
    (A : NativeTransverseAsymptoticIdentification.{u,u} f Ps Pu s t)
    (x y : M) :
    letI := A.realAmbientCharts
    A.F.stablePartition x y ↔ ForwardAsymptotic f x y := by
  let := A.realAmbientCharts
  let q := Quotient.mk A.F.stablePartition x
  let := A.F.stableTopology q
  let := A.F.stableCharts q
  let := A.stableTopology x
  let := A.stableCharts x
  constructor
  · intro hxy
    have hq : Quotient.mk A.F.stablePartition y = q := by
      exact Quotient.sound (@Setoid.symm M A.F.stablePartition x y hxy)
    let z : IntrinsicFoliationLeaf A.F.stablePartition q := ⟨y, hq⟩
    let e := A.stableIdentification x
    let w := e z
    have hw : w.val = y := by
      exact A.stable_points x z
    simpa [w, hw] using w.property
  · intro hxy
    let e := A.stableIdentification x
    let w : StableAsymptoticLeaf f x := ⟨y, hxy⟩
    let z := e.symm w
    have hz : z.val = y := by
      have hpoint := A.stable_points x z
      have he : e z = w := e.apply_symm_apply w
      rw [he] at hpoint
      exact hpoint.symm
    have hq : Quotient.mk A.F.stablePartition z.val = q := z.property
    have hq' : Quotient.mk A.F.stablePartition y = q := by simpa [hz] using hq
    exact Quotient.exact hq'.symm

/-- A point-preserving identification equates the unstable partition relation with forward
asymptoticity under the inverse map. -/
theorem native_identification_unstable_partition_iff_asymptotic
    {f : M ≃ₜ M} {Ps Pu : RealTangentDistribution (realModel d) M}
    {s t : ℕ}
    (A : NativeTransverseAsymptoticIdentification.{u,u} f Ps Pu s t)
    (x y : M) :
    letI := A.realAmbientCharts
    A.F.unstablePartition x y ↔ ForwardAsymptotic f.symm x y := by
  let := A.realAmbientCharts
  let q := Quotient.mk A.F.unstablePartition x
  let := A.F.unstableTopology q
  let := A.F.unstableCharts q
  let := A.unstableTopology x
  let := A.unstableCharts x
  constructor
  · intro hxy
    have hq : Quotient.mk A.F.unstablePartition y = q := by
      exact Quotient.sound (@Setoid.symm M A.F.unstablePartition x y hxy)
    let z : A.F.ULeaf x := ⟨y, hq⟩
    let e := A.unstableIdentification x
    let w := e z
    have hw : w.val = y := by
      exact A.unstable_points x z
    simpa [w, hw] using w.property
  · intro hxy
    let e := A.unstableIdentification x
    let w : UnstableAsymptoticLeaf f x := ⟨y, hxy⟩
    let z := e.symm w
    have hz : z.val = y := by
      have hpoint := A.unstable_points x z
      have he : e z = w := e.apply_symm_apply w
      rw [he] at hpoint
      exact hpoint.symm
    have hq : Quotient.mk A.F.unstablePartition z.val = q := z.property
    have hq' : Quotient.mk A.F.unstablePartition y = q := by simpa [hz] using hq
    exact Quotient.exact hq'.symm

end HolomorphicAnosov
