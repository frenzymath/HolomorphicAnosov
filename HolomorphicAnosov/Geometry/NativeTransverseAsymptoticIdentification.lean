import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Geometry.TransverseFoliationsIntrinsicComplexLeaves
import HolomorphicAnosov.Geometry.NativeAsymptoticLeaf
import HolomorphicAnosov.Geometry.NativeLeafComplexUpgrade
import HolomorphicAnosov.Geometry.LocalHolonomyPathContinuation
import Mathlib.Geometry.Manifold.Diffeomorph

/-! This file defines point-preserving diffeomorphisms between native asymptotic leaves and the
intrinsic partition classes used by stable holonomy. It also defines real coordinate recharts
and transport of local holonomy maps. (HPS, §§6B–7, pp. 114–116; Ghys, §2, pp. 588–590 and p.
594; Demailly, I §3.A,C, pp. 20, 23) -/

open scoped ContDiff Manifold Topology _root_.Topology

namespace HolomorphicAnosov

universe u v

noncomputable section

variable {d s t : ℕ} {M : Type u} [MetricSpace M]
  [ChartedSpace (ComplexModel d) M]

/-- The real atlas obtained by postcomposing each original complex chart with a real linear
coordinate homeomorphism. (Demailly, I §3.C, p. 23) -/
@[instance_reducible]
def realCoordinateRechart
    (B : ComplexModel d ≃L[ℝ] (Fin (s + t) → ℝ)) :
    ChartedSpace (Fin (s + t) → ℝ) M where
  atlas := (fun a : OpenPartialHomeomorph M (ComplexModel d) ↦
    a.transHomeomorph B.toHomeomorph) '' atlas (ComplexModel d) M
  chartAt x := (chartAt (ComplexModel d) x).transHomeomorph B.toHomeomorph
  mem_chart_source x := ChartedSpace.mem_chart_source x
  chart_mem_atlas x := Set.mem_image_of_mem _ (ChartedSpace.chart_mem_atlas x)

variable [IsManifold (realModel d) ∞ M] [T2Space M]
  [SecondCountableTopology M]

/-- Point-preserving diffeomorphisms identifying stable and unstable partition classes with native
asymptotic leaves, together with real ambient coordinates and a complex rank-one upgrade of the
unstable leaves. (HPS, §§6B–7, pp. 114–116; Ghys, §2, pp. 588–590 and p. 594) -/
structure NativeTransverseAsymptoticIdentification
    (f : M ≃ₜ M) (Ps Pu : RealTangentDistribution (realModel d) M)
    (s t : ℕ) where
  /-- A real linear coordinate equivalence for the complex chart model. -/
  realCoordinates : ComplexModel d ≃L[ℝ] (Fin (s + t) → ℝ)
  /-- The transverse foliations and product boxes in the recharted real ambient manifold. -/
  F : letI := realCoordinateRechart (M := M) realCoordinates
    TransverseContinuousFoliations.{u, v} s t M
  /-- The intrinsic stable leaf structure on each forward asymptotic carrier. -/
  nativeS : ∀ x : M, NativeAsymptoticLeafDatum (realModel d) f Ps x
  /-- The intrinsic unstable leaf structure on each inverse asymptotic carrier. -/
  nativeU : ∀ x : M, NativeUnstableAsymptoticLeafDatum (realModel d) f Pu x
  /-- The native stable leaf dimension equals the stable partition dimension. -/
  rankS : ∀ x : M, (nativeS x).rank = s
  /-- The native unstable leaf dimension equals the unstable partition dimension. -/
  rankU : ∀ x : M, (nativeU x).rank = t
  /-- A complex dimension-one upgrade of each intrinsic real unstable leaf. -/
  complexU1 : ∀ x : M,
    letI := (nativeU x).topology
    letI := (nativeU x).charts
    NativeLeafComplexUpgrade (d := d) (r := (nativeU x).rank) 1
      (Subtype.val : UnstableAsymptoticLeaf f x → M)
  /-- A diffeomorphism from each stable partition class to its native asymptotic carrier. -/
  stableIdentification : ∀ x : M,
    letI := realCoordinateRechart (M := M) realCoordinates
    letI := F.stableTopology (Quotient.mk F.stablePartition x)
    letI := F.stableCharts (Quotient.mk F.stablePartition x)
    letI := (nativeS x).topology
    letI := (nativeS x).charts
    Diffeomorph 𝓘(ℝ, Fin s → ℝ) 𝓘(ℝ, Fin (nativeS x).rank → ℝ)
      (IntrinsicFoliationLeaf F.stablePartition (Quotient.mk F.stablePartition x))
      (StableAsymptoticLeaf f x) ∞
  /-- The stable identification preserves the underlying ambient point. -/
  stable_points : ∀ x : M,
    letI := realCoordinateRechart (M := M) realCoordinates
    ∀ z : IntrinsicFoliationLeaf F.stablePartition (Quotient.mk F.stablePartition x),
      (stableIdentification x z).val = z.val
  /-- A diffeomorphism from each unstable partition class to its native asymptotic carrier. -/
  unstableIdentification : ∀ x : M,
    letI := realCoordinateRechart (M := M) realCoordinates
    letI := F.unstableTopology (Quotient.mk F.unstablePartition x)
    letI := F.unstableCharts (Quotient.mk F.unstablePartition x)
    letI := (nativeU x).topology
    letI := (nativeU x).charts
    Diffeomorph 𝓘(ℝ, Fin t → ℝ) 𝓘(ℝ, Fin (nativeU x).rank → ℝ)
      (F.ULeaf x) (UnstableAsymptoticLeaf f x) ∞
  /-- The unstable identification preserves the underlying ambient point. -/
  unstable_points : ∀ x : M,
    letI := realCoordinateRechart (M := M) realCoordinates
    ∀ z : F.ULeaf x, (unstableIdentification x z).val = z.val

namespace NativeTransverseAsymptoticIdentification

variable {f : M ≃ₜ M} {Ps Pu : RealTangentDistribution (realModel d) M}
  (A : NativeTransverseAsymptoticIdentification.{u, v} (d := d) f Ps Pu s t)

/-- The real ambient atlas obtained from the original complex atlas by the stored linear coordinate
equivalence. (Demailly, I §3.C, p. 23) -/
abbrev realAmbientCharts : ChartedSpace (Fin (s + t) → ℝ) M :=
  realCoordinateRechart (d := d) A.realCoordinates

/-- The intrinsic topology of the native stable asymptotic leaf. (HPS, p. 116) -/
abbrev stableTopology (x : M) : TopologicalSpace (StableAsymptoticLeaf f x) :=
  (A.nativeS x).topology

/-- The intrinsic topology of the native unstable asymptotic leaf. (HPS, p. 116) -/
abbrev unstableTopology (x : M) : TopologicalSpace (UnstableAsymptoticLeaf f x) :=
  (A.nativeU x).topology

/-- The real atlas of the native stable leaf on its intrinsic topology. (HPS, pp. 114–116) -/
abbrev stableCharts (x : M) : letI := A.stableTopology x
    ChartedSpace (Fin (A.nativeS x).rank → ℝ) (StableAsymptoticLeaf f x) :=
  (A.nativeS x).charts

/-- The real atlas of the native unstable leaf on its intrinsic topology. (HPS, pp. 114–116) -/
abbrev unstableCharts (x : M) : letI := A.unstableTopology x
    ChartedSpace (Fin (A.nativeU x).rank → ℝ) (UnstableAsymptoticLeaf f x) :=
  (A.nativeU x).charts

/-- The point-preserving homeomorphism underlying the stable class diffeomorphism. (HPS, p. 116) -/
def stableClassHomeomorph (x : M) :
    letI := A.realAmbientCharts
    letI := A.F.stableTopology (Quotient.mk A.F.stablePartition x)
    letI := A.stableTopology x
    IntrinsicFoliationLeaf A.F.stablePartition (Quotient.mk A.F.stablePartition x)
      ≃ₜ StableAsymptoticLeaf f x :=
  letI := A.realAmbientCharts
  letI := A.F.stableTopology (Quotient.mk A.F.stablePartition x)
  letI := A.F.stableCharts (Quotient.mk A.F.stablePartition x)
  letI := A.stableTopology x
  letI := A.stableCharts x
  (A.stableIdentification x).toHomeomorph

/-- The point-preserving homeomorphism underlying the unstable class diffeomorphism. (HPS, p. 116) -/
def unstableClassHomeomorph (x : M) :
    letI := A.realAmbientCharts
    letI := A.unstableTopology x
    A.F.ULeaf x ≃ₜ UnstableAsymptoticLeaf f x :=
  letI := A.realAmbientCharts
  letI := A.F.unstableCharts (Quotient.mk A.F.unstablePartition x)
  letI := A.unstableTopology x
  letI := A.unstableCharts x
  (A.unstableIdentification x).toHomeomorph

/-- The local holonomy partial homeomorphism conjugated by the point-preserving identifications of
its native unstable leaves. (Ghys, pp. 589, 594) -/
def transportUnstableLocalMap (x y : M) :
    letI := A.realAmbientCharts
    letI := A.unstableTopology x
    letI := A.unstableTopology y
    OpenPartialHomeomorph (A.F.ULeaf x) (A.F.ULeaf y) →
      OpenPartialHomeomorph (UnstableAsymptoticLeaf f x) (UnstableAsymptoticLeaf f y) :=
  letI := A.realAmbientCharts
  letI := A.unstableTopology x
  letI := A.unstableTopology y
  fun h ↦ ((A.unstableClassHomeomorph x).symm.toOpenPartialHomeomorph.trans h).trans
    (A.unstableClassHomeomorph y).toOpenPartialHomeomorph

end NativeTransverseAsymptoticIdentification

end

end HolomorphicAnosov
