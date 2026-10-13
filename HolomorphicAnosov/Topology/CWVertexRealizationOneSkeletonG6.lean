import HolomorphicAnosov.Topology.CWGraphBasedRealizationG6
import HolomorphicAnosov.Topology.CWComplex.CarrierTransportG6

namespace HolomorphicAnosov
universe u v w

/-- Rooted-tree realization of a prescribed fundamental-group homomorphism on the original one-skeleton. Source: Hatcher Proposition 1B.9 pp.90–91 and Proposition 1A.2 pp.84–85.

Proof: choose a rooted spanning tree in the original one-skeleton. Send all
vertices and tree-edge disks to y₀. For every complementary oriented edge choose
a based path representing the image under φ of its rooted edge-loop class in K.
The one-cell loop-disk adapter makes the selected path a continuous map on the
original characteristic disk, with value y₀ at both boundary points. Glue these
maps and the vertex assignment by characteristic-map continuity. Every rooted
tree path is mapped to a constant path. Therefore the image of each rooted edge
loop is homotopic relative endpoints to its chosen representative, and its class
has exactly the prescribed value. The rooted edge-loop classes generate the
fundamental group of the original one-skeleton, so equality on these generators
proves equality of homomorphisms. Loop edges and infinitely many cells are allowed;
empty complementary-edge families give the trivial induced homomorphism. The
original characteristic maps and inherited skeleton topology are retained. -/
theorem cw_vertex_realization_one_skeleton_g6
    {K : Type u} {Y : Type v} {E : Type w} [TopologicalSpace K] [TopologicalSpace Y]
    [TopologicalSpace E] [T2Space K] [ConnectedSpace K]
    [Topology.CWComplex (Set.univ : Set K)] [PathConnectedSpace Y] [ContractibleSpace E]
    (k₀ : K) (hk₀ : k₀ ∈ (Topology.CWComplex.skeleton (Set.univ : Set K) 0 : Set K))
    (y₀ : Y) (p : E → Y) (_hp : IsCoveringMap p) (_hsurj : Function.Surjective p)
    (φ : FundamentalGroup K k₀ →* FundamentalGroup Y y₀) (_hφ : φ ≠ 1) :
    let S := ↥(Topology.CWComplex.skeleton (Set.univ : Set K) (1 : ℕ∞) : Set K)
    let k₁ : S := ⟨k₀, Topology.CWComplex.skeleton_mono (by norm_num) hk₀⟩
    let inclusion : C(S, K) := ⟨Subtype.val, continuous_subtype_val⟩
    ∃ f₁ : C(S, Y), ∃ hf₁ : f₁ k₁ = y₀,
      FundamentalGroup.mapOfEq f₁ hf₁ = φ.comp (FundamentalGroup.map inclusion k₁) := by
  classical
  let S : Set K := Topology.CWComplex.skeleton (Set.univ : Set K) 1
  let k₁ : S := ⟨k₀, Topology.CWComplex.skeleton_mono (by norm_num) hk₀⟩
  let inclusion : C(S, K) := ⟨Subtype.val, continuous_subtype_val⟩
  change ∃ f : C(S, Y), ∃ hf : f k₁ = y₀,
    FundamentalGroup.mapOfEq f hf = φ.comp (FundamentalGroup.map inclusion k₁)
  obtain ⟨n, hn, r, hr⟩ := Topology.CWComplex.mem_skeleton_iff.mp hk₀
  have hn0 : n = 0 := by simpa using hn
  subst n
  have hr0 : Topology.RelCWComplex.map 0 r 0 = k₀ := by
    rw [Topology.RelCWComplex.openCell_zero_eq_singleton] at hr
    exact (congrArg (Topology.RelCWComplex.map 0 r) (Subsingleton.elim 0 ![])).trans hr.symm
  have : PathConnectedSpace S := one_skeleton_pathConnected r
  let := cwCarrierStructureG6 S k₁
  have hrS : r ∈ (Topology.CWComplex.skeleton (Set.univ : Set K) 1).I 0 := by
    simp [Topology.RelCWComplex.skeleton, Topology.RelCWComplex.skeletonLT,
      Topology.RelCWComplex.Subcomplex.mk']
  let rS : Topology.RelCWComplex.cell (Set.univ : Set S) 0 := ⟨r, hrS⟩
  have hbase : Topology.RelCWComplex.map 0 rS 0 = k₁ := by
    apply Subtype.ext
    exact (cwCarrierMapG6_coe S k₁ 0 rS (by simp)).trans hr0
  have hhigh : ∀ n, IsEmpty (Topology.RelCWComplex.cell (Set.univ : Set S) (n + 2)) := by
    intro n
    refine ⟨fun i ↦ ?_⟩
    have hi : ((n + 2 : ℕ) : ℕ∞) < (1 : ℕ∞) + 1 := by
      simpa only [S, Topology.RelCWComplex.skeleton, Topology.RelCWComplex.skeletonLT,
        Topology.RelCWComplex.Subcomplex.mk', Set.mem_ofPred_eq] using i.property
    norm_cast at hi
  have realization_at : ∀ (x : S), Topology.RelCWComplex.map 0 rS 0 = x →
      ∀ ψ : FundamentalGroup S x →* FundamentalGroup Y y₀,
        ∃ f : C(S, Y), ∃ hf : f x = y₀, FundamentalGroup.mapOfEq f hf = ψ := by
    intro x hx ψ
    subst x
    exact cw_graph_based_realization_g6 hhigh rS y₀ ψ
  exact realization_at k₁ hbase (φ.comp (FundamentalGroup.map inclusion k₁))

end HolomorphicAnosov
