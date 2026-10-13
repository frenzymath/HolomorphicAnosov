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

/-- Points in the same actual box with the same transverse coordinate belong to the original generated partition. -/
theorem native_same_box_partition {d r c : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (F : RegularHolomorphicFoliation.{u, v} d r c M) (i : F.boxIndex)
    (a b : M) (ha : a ∈ (F.box i).source) (hb : b ∈ (F.box i).source)
    (hab : ((F.box i) a).2 = ((F.box i) b).2) : F.partition a b := by
  have hat := (F.box i).map_source ha
  have hbt := (F.box i).map_source hb
  rw [F.box_target] at hat hbt
  apply (F.partition_generated a b).mpr
  apply Relation.EqvGen.rel
  refine ⟨i, ⟨((F.box i) a).2, hat.2⟩,
    ⟨((F.box i) a).1, hat.1⟩, ⟨((F.box i) b).1, hbt.1⟩, ?_, ?_⟩
  · exact (F.box i).left_inv ha
  · simpa only [hab, Prod.mk.eta] using (F.box i).left_inv hb

