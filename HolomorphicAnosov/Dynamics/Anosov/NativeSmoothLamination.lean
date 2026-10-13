import HolomorphicAnosov.Geometry.Manifold.VectorBundle.RealTangentDistribution
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Native smooth real lamination data

Source: Hirsch--Pugh--Shub, *Invariant Manifolds*, LNM 583 (1977), leaf-immersion
conventions pp.68--72, native continuation (6B.1)--(6B.4), pp.111--114, and continuous
foliation, unbranched lamination and intrinsic leaf topology definitions, pp.115--116.

These structures contain the actual supplied leaf maps, intrinsic topologies and smooth
atlases, partitions, product boxes, smooth plaque charts and optional leaf transport.
They assert no existence of a lamination for a tangent distribution or dynamical system.

Ranks vary among leaves and boxes. A rank-zero leaf is a connected zero-dimensional
manifold. The ambient manifold may be empty or disconnected. Global leaf inclusions
are injective immersions and need not be embeddings. Local plaques are intrinsically
open; their chart topology need not equal the ambient subspace topology on a whole leaf.

The existing `TransverseContinuousFoliations` records a simultaneous fixed-rank pair with
an optional intrinsic complex structure. This interface records one smooth real
lamination on an arbitrary real model and allows locally varying ranks. It therefore
supplies the general data required by the HPS theorem without imposing a constant-rank
or connectedness hypothesis. The fixed-rank pair interface applies on valid rank strata.
-/

open scoped ContDiff Manifold Topology _root_.Topology
open TopologicalSpace Set

universe u
namespace HolomorphicAnosov.HPS

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ, E) ∞ M]

/--
 A connected intrinsic smooth leaf with its actual ambient immersion.

Source: HPS pp.68--72 and pp.115--116. The topology is supplied on the leaf; it is not the
topology induced by the immersion.
-/
structure NativeLeaf (D : RealTangentDistribution 𝓘(ℝ, E) M)
    (L : Type u) [TopologicalSpace L] [ChartedSpace (Fin r → ℝ) L]
    [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ L] where
  inclusion : L → M
  injective : Function.Injective inclusion
  immersion : Manifold.IsImmersion 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, E) ∞ inclusion
  connected : ConnectedSpace L
  hausdorff : T2Space L
  countable : SecondCountableTopology L
  tangent : ∀ x : L, (mfderiv 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, E) inclusion x).range = D (inclusion x)

/--
 A family of native connected immersed leaves partitioning the ambient manifold.

Source: HPS pp.115--116. The leaf carrier types and their smooth structures are actual parameters,
while the partition laws are explicit fields.
-/
structure LeafPartition (D : RealTangentDistribution 𝓘(ℝ, E) M)
    (ι : Type u) (L : ι → Type u) (r : ι → ℕ)
    [∀ i, TopologicalSpace (L i)]
    [∀ i, ChartedSpace (Fin (r i) → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin (r i) → ℝ) ∞ (L i)] where
  leaf : ∀ i, NativeLeaf (r := r i) D (L i)
  cover : ∀ p : M, ∃ i x, (leaf i).inclusion x = p
  disjoint : ∀ i j x y, (leaf i).inclusion x = (leaf j).inclusion y → i = j

/--
 A product box whose slices are intrinsic smooth plaques.

Source: HPS p.115. The disc slices are genuine diffeomorph charts into the actual leaf carriers;
no differentiability in the transversal is asserted.
-/
structure NativeProductBox {D : RealTangentDistribution 𝓘(ℝ, E) M}
    {ι : Type u} {L : ι → Type u} {r : ι → ℕ}
    [∀ i, TopologicalSpace (L i)]
    [∀ i, ChartedSpace (Fin (r i) → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin (r i) → ℝ) ∞ (L i)]
    (F : LeafPartition D ι L r) (d : ℕ) (T : Type u) [TopologicalSpace T] where
  transverseRank : ℕ
  transverseDisc : Opens (Fin transverseRank → ℝ)
  transverse_connected : IsConnected (transverseDisc : Set (Fin transverseRank → ℝ))
  transverse_chart : T ≃ₜ transverseDisc
  disc : Opens (Fin d → ℝ)
  disc_connected : IsConnected (disc : Set (Fin d → ℝ))
  ambient : Opens M
  box : (disc × T) ≃ₜ ambient
  label : T → ι
  plaque : ∀ t, Opens (L (label t))
  chart : ∀ t, Diffeomorph 𝓘(ℝ, Fin d → ℝ)
    𝓘(ℝ, Fin (r (label t)) → ℝ) disc (plaque t) ∞
  factorization : ∀ t v, (box (v, t) : M) =
    (F.leaf (label t)).inclusion (chart t v)

/--
 A family of product boxes covering the ambient partition.

Source: HPS pp.115--116. Each transversal is homeomorphic to a connected open real coordinate
domain. The intrinsic topology and compatible smooth plaque transfers come from the receiving
leaf's native atlas, not from its ambient subspace topology.
-/
structure LaminationBoxes {D : RealTangentDistribution 𝓘(ℝ, E) M}
    {ι : Type u} {L : ι → Type u} {r : ι → ℕ}
    [∀ i, TopologicalSpace (L i)]
    [∀ i, ChartedSpace (Fin (r i) → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin (r i) → ℝ) ∞ (L i)]
    (F : LeafPartition D ι L r)
    (β : Type u) (d : β → ℕ) (T : β → Type u) [∀ b, TopologicalSpace (T b)] where
  boxes : ∀ b, NativeProductBox F (d b) (T b)
  cover : ∀ p : M, ∃ b, p ∈ (boxes b).ambient
  topology_generated : ∀ i (W : Set (L i)), IsOpen W ↔
    ∀ b t (h : (boxes b).label t = i),
      IsOpen ((fun v : (boxes b).disc ↦
        (h ▸ ((boxes b).chart t v).val : L i)) ⁻¹' W)

/--
 The original diffeomorphism permutes the partition's actual native leaves.

Source: HPS point-foliation conclusion (6B.3)--(6B.4), pp.111--114, and (7.5)--(7.6), pp.127--129.
Smooth leaf diffeomorphisms are supplied together with the literal ambient intertwining equation.
-/
structure LeafDynamicalInvariance {D : RealTangentDistribution 𝓘(ℝ, E) M}
    {ι : Type u} {L : ι → Type u} {r : ι → ℕ}
    [∀ i, TopologicalSpace (L i)]
    [∀ i, ChartedSpace (Fin (r i) → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin (r i) → ℝ) ∞ (L i)]
    (F : LeafPartition D ι L r) (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) where
  permutation : ι ≃ ι
  transport : ∀ i, Diffeomorph 𝓘(ℝ, Fin (r i) → ℝ)
    𝓘(ℝ, Fin (r (permutation i)) → ℝ) (L i) (L (permutation i)) ∞
  intertwining : ∀ i x,
    (F.leaf (permutation i)).inclusion (transport i x) = f ((F.leaf i).inclusion x)

end HolomorphicAnosov.HPS
