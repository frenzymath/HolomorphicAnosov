import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Geometry.RegularHolomorphicFoliation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

namespace HolomorphicAnosov

open Set TopologicalSpace _root_.Topology
open scoped ContDiff Manifold

universe u v w

set_option autoImplicit false

/-- At every point of an intrinsic leaf, its actual inclusion derivative has the stored foliation tangent range.    Quotient equality identifies the native charted carrier; no alternate bundle or ambient subspace atlas is used. -/
theorem native_inclusion_range {d r c : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (F : RegularHolomorphicFoliation.{u, v} d r c M)
    (q : Quotient F.partition) :
    letI := F.leafTopology q
    letI := F.leafCharts q
    ∀ z : IntrinsicFoliationLeaf F.partition q,
      (mfderiv (complexModel r) (complexModel d)
        (fun y : IntrinsicFoliationLeaf F.partition q ↦ y.val) z).range =
        F.tangent z.val := by
  let _ := F.leafTopology q
  let _ := F.leafCharts q
  rintro ⟨z, hz⟩
  subst q
  rfl

