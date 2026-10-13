import HolomorphicAnosov.Topology.Franks.LeafBox
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.RealTangentDistribution
import Mathlib.Geometry.Manifold.Immersion

/-!
# A foliation on specified intrinsic C¹ leaf carriers

Source: Franks, *Anosov Diffeomorphisms*, Global Analysis Part I (1970),
Proposition 1.1 and the intrinsic metric convention, p.65; Lemma 1.2 and
Corollary 1.3, pp.65–66. Native product boxes and intrinsic leaf topology follow
Hirsch–Pugh–Shub, *Invariant Manifolds* (1977), §7, pp.115–116.

This is the actual definition of DAG node `topo.franks_leaf_foliation_g8`.
It packages given intrinsic leaf maps, tangent ranges, partition laws and boxes;
it does not assert existence of a foliation for an arbitrary distribution.
The leaf topologies and C¹ atlases are parameters. A whole leaf can return to a
box in several plaques, and its topology need not be the ambient subspace topology.
-/

open scoped ContDiff Manifold

universe u

namespace HolomorphicAnosov.Franks

variable {n r : ℕ} {P : Type u} [TopologicalSpace P]
variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) P]
variable [IsManifold (𝓡 n) ∞ P]
variable {ι : Type u} {L : ι → Type u}
variable [∀ i, TopologicalSpace (L i)]
variable [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin r)) (L i)]
variable [∀ i, IsManifold (𝓡 r) 1 (L i)]

/-- A fixed-rank real leaf foliation on the given ORIGINAL intrinsic C¹ manifolds.

Source: Franks, Proposition 1.1(b) and intrinsic leaf metric definition, p.65,
Lemma 1.2 and Corollary 1.3, pp.65–66; HPS §7, pp.115–116.

Each inclusion is injective and a C¹ immersion in the specified native atlases,
with tangent image exactly the given real distribution. Every intrinsic leaf is
connected, Hausdorff and second-countable. Coverage and the equality-of-labels law
make the images a partition. Every ambient point belongs to an existing `LeafBox`:
its slices are C¹ diffeomorphisms onto intrinsically open plaques, and the box map
agrees with these same inclusions pointwise. No transverse differentiability is
asserted, and no unrelated leaf atlas or ambient induced topology is substituted.

The immersion is stated pointwise using Mathlib `Manifold.IsImmersionAt`, which
already includes the C¹ chart normal form and differentiability; this avoids
imposing a chosen global complement. The finite-dimensional Euclidean models
specify leaf DIMENSION r, not a global parameterization of L_i by ℝ^r.

This definition has no postponed proof or source proof steps: all maps and proof
fields are literal constructor data, built from its existing definition dependencies.
It contains no dynamical invariance, asymptotic characterization, intrinsic metric,
completeness, leaf transport, global product structure or ambient covering assumption.
It applies equally to a base manifold or a specified lifted manifold, with those
actual supplied carriers; no Euclidean universal-cover conclusion is built in. -/
structure LeafFoliation (D : RealTangentDistribution (𝓡 n) P) where
  /-- Actual inclusion of each specified intrinsic leaf (Franks p.65). -/
  inclusion : ∀ i : ι, L i → P
  /-- Whole leaves are injectively immersed, not assumed embedded (Franks p.65). -/
  injective : ∀ i, Function.Injective (inclusion i)
  /-- C¹ immersion in the given intrinsic and ambient atlases (Franks p.65). -/
  immersion : ∀ i (x : L i), Manifold.IsImmersionAt (𝓡 r) (𝓡 n) 1 (inclusion i) x
  /-- The actual derivative range is exactly the given distribution (Franks p.65). -/
  tangent : ∀ i (x : L i), (mfderiv (𝓡 r) (𝓡 n) (inclusion i) x).range = D (inclusion i x)
  /-- Leaves are connected in their intrinsic topology (Franks p.65; HPS p.115). -/
  connected : ∀ i, ConnectedSpace (L i)
  /-- The specified intrinsic topology is Hausdorff (HPS pp.115–116). -/
  hausdorff : ∀ i, T2Space (L i)
  /-- The specified intrinsic topology is second-countable (HPS pp.115–116). -/
  second_countable : ∀ i, SecondCountableTopology (L i)
  /-- The actual inclusions cover the ambient manifold (Franks Proposition 1.1). -/
  cover : ∀ p : P, ∃ (i : ι) (x : L i), inclusion i x = p
  /-- Distinct labels have disjoint actual ambient leaf images (Franks Proposition 1.1). -/
  disjoint : ∀ i j (x : L i) (y : L j), inclusion i x = inclusion j y → i = j
  /-- Existing native leaf boxes cover every ambient point (HPS pp.115–116). -/
  box_cover : ∀ p : P, ∃ B : LeafBox (n := n) (r := r) inclusion, p ∈ B.ambient

end HolomorphicAnosov.Franks
