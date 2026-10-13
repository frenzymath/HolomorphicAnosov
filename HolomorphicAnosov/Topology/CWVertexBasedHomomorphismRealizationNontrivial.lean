import HolomorphicAnosov.Topology.CWComplex.CompatibleSkeletalMapsG6
import HolomorphicAnosov.Topology.CWVertexRealizationCompatibleSkeletaG6
import HolomorphicAnosov.Topology.CWVertexRealizationFromOneSkeleton
import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

namespace HolomorphicAnosov

universe u v w

/-- Nontrivial-homomorphism branch of the CW based realization theorem.

Source: Hatcher, *Algebraic Topology*, Proposition 1B.9, pp.90–91. The
remaining existence construction is recorded as a named admission so its
covering-space lifting, cellwise extension, and CW gluing obligations remain
independently visible to the DAG.
-/
theorem cw_vertex_based_homomorphism_realization_nontrivial
    {K : Type u} {Y : Type v} {E : Type w}
    [TopologicalSpace K] [TopologicalSpace Y] [TopologicalSpace E]
    [T2Space K] [ConnectedSpace K] [Topology.CWComplex (Set.univ : Set K)]
    [PathConnectedSpace Y] [ContractibleSpace E]
    (k₀ : K) (hk₀ : k₀ ∈ (Topology.CWComplex.skeleton (Set.univ : Set K) 0 : Set K))
    (y₀ : Y) (p : E → Y)
    (hp : IsCoveringMap p) (hp_surjective : Function.Surjective p)
    (φ : FundamentalGroup K k₀ →* FundamentalGroup Y y₀)
    (hφ : φ ≠ 1) :
    ∃ f : C(K, Y), ∃ hf : f k₀ = y₀, FundamentalGroup.mapOfEq f hf = φ := by
  obtain ⟨F, hcompat, hF, hπ⟩ :=
    cw_vertex_realization_compatible_skeleta_g6 k₀ hk₀ y₀ p hp hp_surjective φ hφ
  obtain ⟨f, hf⟩ := cw_map_of_compatible_skeleta F hcompat
  refine ⟨f, ?_⟩
  apply cw_vertex_realization_from_one_skeleton k₀ hk₀ y₀ φ (F 1) hF f
  · ext x
    exact hf 1 x
  · exact hπ

end HolomorphicAnosov
