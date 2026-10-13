import HolomorphicAnosov.Topology.Franks.LeafFoliation

/-!
# Transport on specified intrinsic leaves

Source: John Franks, *Anosov Diffeomorphisms*, Global Analysis Part I (1970),
Proposition 1.1 and the intrinsic leaf metric convention, printed p.65;
Lemma 1.2 and Corollary 1.3, pp.65–66. The intrinsic carriers and native plaque
charts are the already-defined `LeafFoliation`, with the HPS §7, pp.115–116,
foliation-box convention. DAG node: `topo.franks_leaf_transport_g8`.

A transport packages conclusion DATA: an actual permutation of leaf labels and
an actual C¹ diffeomorphism of each given leaf to its image leaf. It asserts no
existence for an arbitrary ambient map and does not assume ambient differentiability.
The intertwining law uses the original leaf inclusions, not ambient subspace atlases.
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

/-- Transport of a specified intrinsic C¹ leaf foliation by the original ambient map.

Source: Franks, Proposition 1.1, p.65, Lemma 1.2 and Corollary 1.3, pp.65–66;
HPS §7, pp.115–116 supplies the explicit intrinsic leaf topology convention.

The label equivalence is a permutation, and each `leafMap` contains both a genuine
bijection and C¹ regularity of that map and its inverse in the given native leaf charts.
The ambient map `a` is an arbitrary function at this definition boundary: its leafwise
restriction is regular as a CONSEQUENCE of the supplied transport data, without adding
an ambient differentiability or invariance premise. The equality is pointwise on every
leaf, including all its returning plaques. No global Euclidean parametrization, leaf
embedding, metric, contraction, covering, or transverse derivative is included.

Empty label types and empty ambient spaces impose only their actual constructor laws;
zero-dimensional leaves use the same C¹ diffeomorphism definition. This definition has
no postponed proofs or asserted existence, and all its building notions are its genuine
`LeafFoliation` and Mathlib `Equiv`/`Diffeomorph` data.
-/
structure LeafTransport {D : RealTangentDistribution (𝓡 n) P}
    (F : LeafFoliation (n := n) (r := r) (L := L) D) (a : P → P) where
  /-- The permutation of the existing leaf labels (Franks p.65). -/
  permutation : ι ≃ ι
  /-- A C¹ diffeomorphism between the specified intrinsic leaf manifolds (Franks pp.65–66). -/
  leafMap : ∀ i : ι, Diffeomorph (𝓡 r) (𝓡 r) (L i) (L (permutation i)) 1
  /-- Inclusion of the transported point is the original ambient action (Franks p.65). -/
  intertwining : ∀ i (x : L i),
    F.inclusion (permutation i) (leafMap i x) = a (F.inclusion i x)

end HolomorphicAnosov.Franks
