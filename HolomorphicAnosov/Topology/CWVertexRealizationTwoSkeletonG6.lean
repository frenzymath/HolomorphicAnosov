import HolomorphicAnosov.Topology.CWVertexRealizationOneSkeletonG6
import HolomorphicAnosov.Topology.CWVertexRealizationTwoCellFillingsG6
import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

namespace HolomorphicAnosov
universe u v w

/-- A based one-skeleton realization of the prescribed homomorphism extends
through the two-skeleton.

Source: Hatcher, Algebraic Topology, Proposition 1B.9 pp.90–91, Proposition
1A.2 pp.84–85 and Appendix A.2 pp.520–523. Choose a rooted spanning tree of
K^1, send its vertices and edges to y0, and choose a representative based loop
for the prescribed image of each complementary rooted edge loop. Parameterize
each loop on its original characteristic one-disk, with constant endpoint values.
The original characteristic-map criterion makes the glued one-skeleton map
continuous. Every rooted tree path maps to a constant path, so its induced
map has the prescribed value on each rooted edge-loop generator. Generation
then proves equality with phi composed with the inclusion homomorphism.
For each two-cell its attaching loop, conjugated by a path from k0 to an
attaching point, is nullhomotopic in K because it bounds the characteristic
disk. The homomorphism equality shows its image under the one-skeleton map
is trivial in pi1(Y,y0); basepoint change therefore makes the original image
attaching loop trivial at its own basepoint. An endpoint-fixed nullhomotopy
of this loop descends through the standard interval-to-circle quotient, whose
only nonsingleton fibre identifies the two endpoints. This gives a nullhomotopy
of the full attaching-circle map. The nullhomotopic-sphere disk-extension theorem
fills the original native two-disk with exactly these boundary values. Choose
a filling for every two-cell and apply successor-skeleton gluing, yielding the
displayed extension. Empty edge and two-cell families require no special choices;
infinite families use the CW weak topology and do not require local finiteness.
The required edge-loop computation and two-cell nullhomotopy remain the named
formalization residual; higher-dimensional extension is proved separately. -/
theorem cw_vertex_realization_two_skeleton_g6
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
    ∃ f₁ : C(S 1, Y), ∃ hf₁ : f₁ k₁ = y₀,
      FundamentalGroup.mapOfEq f₁ hf₁ = φ.comp (FundamentalGroup.map inclusion k₁) ∧
      ∃ f₂ : C(S 2, Y), ∀ x : S 1,
        f₂ ⟨x.val, Topology.CWComplex.skeleton_mono (by norm_num) x.property⟩ = f₁ x := by
  obtain ⟨f₁, hf₁, hπ⟩ := cw_vertex_realization_one_skeleton_g6 k₀ hk₀ y₀ p hp hsurj φ hφ
  obtain ⟨f₂, hext⟩ := cw_vertex_realization_two_cell_fillings_g6 k₀ hk₀ y₀ p hp hsurj φ hφ f₁ hf₁ hπ
  exact ⟨f₁, hf₁, hπ, f₂, hext⟩

end HolomorphicAnosov
