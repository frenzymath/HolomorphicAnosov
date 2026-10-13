import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Geometry.RegularHolomorphicFoliation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import HolomorphicAnosov.Geometry.HolomorphicGlobalLeafProductLeafRelationIff
import HolomorphicAnosov.Geometry.HolomorphicGlobalLeafProductAffineIntersectionUnique

namespace HolomorphicAnosov

open Set TopologicalSpace _root_.Topology
open scoped ContDiff Manifold

universe u v w

set_option autoImplicit false

/-- Pointwise global leaf intersections on the original carriers, with no assumption about continuity into their intrinsic topologies. -/
theorem partition_intersection_unique {M : Type u} [TopologicalSpace M]
    {V : Type w} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Fs Fu : Setoid M) (S U : Submodule ℝ V) (hSU : IsCompl S U) (H : M ≃ₜ V)
    (hs : ∀ x, H '' {y | Fs x y} = {z | z - H x ∈ S})
    (hu : ∀ x, H '' {y | Fu x y} = {z | z - H x ∈ U}) (a b : M) :
    ∃! y : M, Fs a y ∧ Fu b y := by
  obtain ⟨v, hv, hvuniq⟩ := affine_intersection_unique S U hSU (H a) (H b)
  refine ⟨H.symm v, ?_, ?_⟩
  · constructor
    · apply (leaf_relation_iff Fs H S hs _ _).mpr
      simpa using hv.1
    · apply (leaf_relation_iff Fu H U hu _ _).mpr
      simpa using hv.2
  · intro y hy
    apply H.injective
    rw [H.apply_symm_apply]
    exact hvuniq (H y) ⟨(leaf_relation_iff Fs H S hs _ _).mp hy.1,
      (leaf_relation_iff Fu H U hu _ _).mp hy.2⟩

