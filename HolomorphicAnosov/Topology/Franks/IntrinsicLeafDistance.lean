import HolomorphicAnosov.Topology.FranksPiecewiseC1PathG8
import HolomorphicAnosov.Topology.Franks.LeafPathLength
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Intrinsic finite-piece C¹ leaf distance in the original ambient metric

Source: John Franks, *Anosov Diffeomorphisms*, Global Analysis Part I (1970),
printed p.65, the intrinsic metric paragraph following Proposition 1.1;
Lemma 1.2 and its speed-integral proof, pp.65–66. Native leaf topology and
charts are as in Hirsch–Pugh–Shub, *Invariant Manifolds* (1977), §7,
pp.115–116. DAG node: `topo.franks_intrinsic_leaf_distance_g8`.

This implements the node's explicitly specified finite-piece C¹ convention.
Franks literally writes piecewise smooth paths. No equality between the
piecewise smooth and finite-piece C¹ infima is supplied or assumed here.
The definition uses the already supplied native leaf carrier, topology and
C¹ atlas, the actual inclusion into the ambient manifold, and the given
smooth ambient Riemannian tensor, through `leafPathLength`.

The construction is the real infimum of the range of the length function on
ALL existing `PiecewiseC1Path x y`. It does not restrict that range to paths
which are globally C¹ across their division times, and it does not use the
ambient endpoint distance. No default coordinate norm is substituted.
Connectedness, nonempty path families and finite nonnegative path lengths
are the relevant theorem obligations for using this real infimum as a
metric. In particular, the definition itself neither builds a `MetricSpace`
instance nor assumes completeness or equality with Mathlib's
`Manifold.riemannianEDist`, whose path carrier is different.

Coincident endpoints and zero-rank leaves use the same expression. Constant
paths are permitted by the existing path definition; their admissibility,
zero length and the resulting diagonal equality can be proved subsequently.
An empty path family still has Mathlib's totalized real infimum; no assertion
that this totalized value is an intrinsic metric is made without path
existence. No postponed theorem or unknown data is needed to define the
infimum.
-/

noncomputable section

open Set Bundle
open scoped Manifold ContDiff

universe u

namespace HolomorphicAnosov.Franks

variable {n r : ℕ} {P : Type u} [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) P] [IsManifold (𝓡 n) ∞ P]
  {ι : Type u} {L : ι → Type u}
  [∀ i, TopologicalSpace (L i)]
  [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin r)) (L i)]
  [∀ i, IsManifold (𝓡 r) 1 (L i)]
  {D : RealTangentDistribution (𝓡 n) P}

/-- The real infimum of the original ambient-metric lengths of all finite-piece
intrinsic C¹ paths joining the specified leaf points. Source: Franks (1970),
p.65, intrinsic metric definition, with the node's finite-piece C¹ convention.
The original carrier, charts, inclusion and tensor are those of the supplied
`LeafFoliation` and `leafPathLength`; no path existence or metric axioms are
hidden in this definition. -/
def intrinsicLeafDistance
    (g : ContMDiffRiemannianMetric (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : P → Type _))
    (F : LeafFoliation (r := r) (L := L) D) {i : ι} (x y : L i) : ℝ :=
  sInf (Set.range (fun γ : PiecewiseC1Path (r := r) x y ↦ leafPathLength g F γ))

end HolomorphicAnosov.Franks
