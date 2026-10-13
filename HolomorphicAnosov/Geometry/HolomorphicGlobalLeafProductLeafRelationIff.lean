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

/-- The complete affine-leaf hypothesis identifies the literal partition relation; this uses only the bijectivity of the original homeomorphism. -/
theorem leaf_relation_iff {M : Type u} [TopologicalSpace M]
    {V : Type w} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : Setoid M) (H : M ≃ₜ V) (W : Submodule ℝ V)
    (hW : ∀ x, H '' {y | F x y} = {z | z - H x ∈ W}) (x y : M) :
    F x y ↔ H y - H x ∈ W := by
  constructor
  · intro hxy
    have hy : H y ∈ H '' {z | F x z} := ⟨y, hxy, rfl⟩
    rwa [hW] at hy
  · intro hy
    have hm : H y ∈ H '' {z | F x z} := by rwa [hW]
    obtain ⟨z, hz, hzy⟩ := hm
    exact H.injective hzy ▸ hz

