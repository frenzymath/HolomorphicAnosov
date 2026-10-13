import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Instances.AddCircle.Real
import HolomorphicAnosov.Topology.ClosedSmoothRealManifold

namespace HolomorphicAnosov

universe u

/-!
# Higher-dimensional homotopy-torus rigidity interface

This file records the sole permitted explicit rigidity premise.  It is a
proposition-valued schema, not an axiom or a proof of the assertion.  The
topology and Euclidean atlas on `M` are selected once by the typeclass
parameters and are therefore the structures used by both map witnesses.

Source: the higher-dimensional homotopy-torus assertion quoted by Ghys,
*Holomorphic Anosov systems*, proof of Theorem B, printed p. 598, [H-S].
The bound `5 ≤ n` and this closed-smooth packaging are the reviewed precise
interface; Zhang's application uses only dimensions `n = 2 d ≥ 6`.
-/

/--
The proposed Hsiang--Shaneson homotopy-torus rigidity premise.

For every real closed smooth `n`-manifold with `n ≥ 5`, a genuine topological
homotopy equivalence to the canonical real `n`-torus entails a genuine
homeomorphism to that torus.  The `ClosedSmoothRealManifold` argument is an
explicit witness and is not installed as a global axiom or hidden instance.
-/
def HomotopyTorusRigidity : Prop :=
  ∀ (n : ℕ),
    5 ≤ n →
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M],
        ClosedSmoothRealManifold n M →
          Nonempty (ContinuousMap.HomotopyEquiv M (UnitAddTorus (Fin n))) →
            Nonempty (Homeomorph M (UnitAddTorus (Fin n)))

end HolomorphicAnosov
