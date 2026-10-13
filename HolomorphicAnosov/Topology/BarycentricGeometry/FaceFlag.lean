import HolomorphicAnosov.Topology.BarycentricGeometry.OriginalFace
import Mathlib.Order.NonemptyFiniteChains

/-!
# Finite flags of nonempty coordinate faces

Node: `topo.def_face_flag_g2`.
Source: Schultz, UCR Mathematics 246A, §I.2 Proposition 3 and its proof,
printed p.23; Hatcher, Algebraic Topology, pp.119–120. Nonempty nested
families of coordinate faces are represented by Mathlib nonempty finite
chains under inclusion. No ordering choices or maximality data are added.
-/

namespace HolomorphicAnosov.BarycentricGeometry

/-- A strictly nested finite family of nonempty original faces. Mathlib's comparable finite-chain
notion retains all faces without repetitions. -/
abbrev FaceFlag (n : ℕ) := PartialOrder.NonemptyFiniteChains (OriginalFace n)

end HolomorphicAnosov.BarycentricGeometry
