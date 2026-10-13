import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Product boxes with intrinsic C¹ plaques

Source: Franks, *Anosov Diffeomorphisms*, Global Analysis Part I (1970),
Proposition 1.1(b), printed p.65 (supplied complete volume PDF p.74), uses
intrinsically C¹ injectively immersed leaves. Hirsch–Pugh–Shub, *Invariant
Manifolds* (1977), §7, pp.115--116, defines continuous foliation boxes and
laminations with differentiable intrinsic leaves. This module packages one box;
it asserts no existence theorem, leaf-distance estimate or dynamical invariance.
-/

open scoped ContDiff Manifold

universe u

namespace HolomorphicAnosov.Franks

variable {n r : ℕ} {P : Type u} [TopologicalSpace P]
variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) P]
variable {ι : Type u} {L : ι → Type u}
variable [∀ i, TopologicalSpace (L i)]
variable [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin r)) (L i)]

/-- A leaf box for specified leaf carriers, intrinsic leaf atlases and inclusion maps.

The transversal has only a topology. The coordinate domain and ambient image
are open sets with their subspace topologies. Each slice is a C¹ diffeomorphism
onto an open set in its labelled leaf's intrinsic topology, and its ambient image
agrees pointwise with the product homeomorphism. These fields impose no
transverse differentiability, global leaf embedding, connected coordinate domain,
or nonemptiness. The inclusion maps and their global leaf properties belong to
the specified leaf data; the box itself does not replace the intrinsic topology
with the topology induced from the ambient manifold.

Source: Franks, Proposition 1.1(b), printed p.65; HPS, §7, pp.115--116,
continuous foliation boxes and C¹ intrinsic laminae. -/
structure LeafBox [IsManifold (𝓡 n) ∞ P]
    [∀ i, IsManifold (𝓡 r) 1 (L i)] (inc : ∀ i, L i → P) where
  /-- The topological transverse parameter space. -/
  transversal : Type u
  /-- No smooth structure is required on the transversal. -/
  [topology : TopologicalSpace transversal]
  /-- An open domain in real Euclidean leaf coordinates; it may be empty. -/
  disc : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin r))
  /-- The open ambient image of the box. -/
  ambient : TopologicalSpace.Opens P
  /-- The product map onto that open ambient subset. -/
  box : (disc × transversal) ≃ₜ ambient
  /-- The leaf containing each slice. -/
  label : transversal → ι
  /-- Each plaque is open in its leaf's intrinsic topology. -/
  plaque : ∀ t, TopologicalSpace.Opens (L (label t))
  /-- The slice parametrization and its inverse are C¹ in native leaf charts. -/
  chart : ∀ t, Diffeomorph (𝓡 r) (𝓡 r) disc (plaque t) 1
  /-- The slice agrees with the given inclusion of the intrinsic leaf. -/
  intertwining : ∀ t z, (box (z, t) : P) = inc (label t) (chart t z)

end HolomorphicAnosov.Franks
