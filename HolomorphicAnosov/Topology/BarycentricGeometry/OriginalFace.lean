import Mathlib.Data.Finset.Empty

/-!
# Nonempty coordinate faces of a standard simplex

Node: `topo.def_original_face_g2`.
Source: Hatcher, Algebraic Topology, Proposition 2.21 proof, pp.119–120,
and Appendix, pp.534–535. A nonempty face is encoded by its finite subset of
the original vertex indices. The full face and every singleton are included.
This is the existing public subtype abbreviation, with no new mathematical data.
-/

namespace HolomorphicAnosov.BarycentricGeometry

/-- Nonempty ORIGINAL coordinate faces, as finite sets of their vertex indices. Hatcher pp.119–120,
Appendix pp.534–535. -/
abbrev OriginalFace (n : ℕ) := {F : Finset (Fin (n + 1)) // F.Nonempty}

end HolomorphicAnosov.BarycentricGeometry
