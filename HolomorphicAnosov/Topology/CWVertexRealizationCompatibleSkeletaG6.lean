import HolomorphicAnosov.Topology.CWComplex.CompatibleExtensionFromTwoSkeletonG6
import HolomorphicAnosov.Topology.CWVertexRealizationTwoSkeletonG6
import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

namespace HolomorphicAnosov
universe u v w

/-- Compatible finite-skeleton realization data for a prescribed nontrivial
fundamental-group homomorphism.

Source: Hatcher, Algebraic Topology, Proposition 1B.9, pp.90–91; Proposition 1A.2,
pp.84–85; Proposition 1.26, pp.50–51; and Appendix A.2, pp.520–523.

Proof: choose a rooted spanning tree of the original one-skeleton. Send every
vertex and tree edge to the target basepoint. For each complementary edge,
choose a based loop representing the prescribed image of its root-based edge
loop, and parameterize it on the original characteristic one-disk. Its endpoint
values agree with the vertex values. The characteristic-map criterion proves
continuity on the one-skeleton. Tree paths map to constant paths, so the induced
homomorphism has the prescribed values on the rooted edge-loop generators and
therefore equals the prescribed composite on the whole fundamental group.
For every two-cell, its attaching loop is nullhomotopic in K. The equality on
fundamental groups makes its image nullhomotopic in Y. A boundary nullhomotopy
fills the original two-disk. For every higher cell, its simply connected
attaching sphere lifts to the contractible covering E; contracting upstairs and
projecting supplies a nullhomotopy and hence a disk filling. At each dimension,
choose these fillings simultaneously. Define the next skeletal map by its
previous values on the lower skeleton and by the fillings on open cell interiors.
Boundary agreement makes this well-defined on the attaching identifications;
the CW characteristic-map criterion proves continuity, with no finiteness or
local finiteness assumption. Recursion yields the finite-skeleton family with
successor agreement; induction gives the displayed agreement for every m ≤ n.
The zero-skeleton map is the constant vertex assignment. Empty cell families
require no choices. Global descent of this family is handled separately. -/
theorem cw_vertex_realization_compatible_skeleta_g6
    {K : Type u} {Y : Type v} {E : Type w}
    [TopologicalSpace K] [TopologicalSpace Y] [TopologicalSpace E]
    [T2Space K] [ConnectedSpace K] [Topology.CWComplex (Set.univ : Set K)]
    [PathConnectedSpace Y] [ContractibleSpace E]
    (k₀ : K) (hk₀ : k₀ ∈ (Topology.CWComplex.skeleton (Set.univ : Set K) 0 : Set K))
    (y₀ : Y) (p : E → Y) (hp : IsCoveringMap p) (hsurj : Function.Surjective p)
    (φ : FundamentalGroup K k₀ →* FundamentalGroup Y y₀) (hφ : φ ≠ 1) :
    let S (n : ℕ) := ↥(Topology.CWComplex.skeleton (Set.univ : Set K) (n : ℕ∞) : Set K)
    let k₁ : S 1 := ⟨k₀, Topology.CWComplex.skeleton_mono (by norm_num) hk₀⟩
    let inclusion : C(S 1, K) := ⟨Subtype.val, continuous_subtype_val⟩
    ∃ F : ∀ n : ℕ, C(S n, Y),
      (∀ (m n : ℕ) (hmn : m ≤ n) (x : S m),
        F m x = F n ⟨x.val, Topology.CWComplex.skeleton_mono
          (by exact_mod_cast hmn) x.property⟩) ∧
      ∃ hF : F 1 k₁ = y₀,
        FundamentalGroup.mapOfEq (F 1) hF = φ.comp (FundamentalGroup.map inclusion k₁) := by
  obtain ⟨f₁, hf₁, hπ, f₂, hext⟩ :=
    cw_vertex_realization_two_skeleton_g6 k₀ hk₀ y₀ p hp hsurj φ hφ
  obtain ⟨F, hcompat, htwo⟩ := cw_compatible_extension_from_two_skeleton_g6 p hp hsurj f₂
  have hone : F 1 = f₁ := by
    ext x
    exact (hcompat 1 2 (by omega) x).trans (by rw [htwo]; exact hext x)
  refine ⟨F, hcompat, ?_⟩
  rw [hone]
  exact ⟨hf₁, hπ⟩

end HolomorphicAnosov
