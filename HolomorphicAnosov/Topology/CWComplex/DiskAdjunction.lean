import Mathlib.Topology.Category.TopCat.Sphere
import Mathlib.Topology.Constructions
import Mathlib.Logic.Relation

/-!
# Finite disk adjunction

Source: Hatcher, *Algebraic Topology*, Appendix p.519: attach finitely many
closed Euclidean disks by identifying each boundary point with its attaching
image. This module supplies the concrete construction of DAG node
`topo.def_finite_disk_adjunction_g2`, with the original quotient projections.
-/

noncomputable section

open scoped TopCat

universe u

namespace HolomorphicAnosov.FiniteCellAdjunction

/-- The finite disk adjunction along the prescribed continuous boundary maps.

Source: Hatcher, *Algebraic Topology*, Appendix p.519. Start with the disjoint
union of `X` and the `k` closed Euclidean `n`-disks. Identify `(i,z)` on a disk
boundary with `a i z` in `X`, taking precisely the equivalence closure of these
generators. The resulting carrier has Mathlib's coinduced quotient topology.
No separation, embedding, compactness or injectivity property is assumed.
For `k = 0` there are no boundary generators; for `n = 0` every boundary is empty.
-/
def adjunction (n : ℕ) (X : TopCat.{u}) (k : ℕ) (a : Fin k → C(∂𝔻 n, X)) :
    TopCat.{u} :=
  TopCat.of (Quotient (Relation.EqvGen.setoid
    (fun p q : X ⊕ (Fin k × 𝔻 n) ↦ ∃ (i : Fin k) (z : ∂𝔻 n),
      p = Sum.inr (i, TopCat.diskBoundaryInclusion n z) ∧ q = Sum.inl (a i z))))

/-- The original old-space projection to the finite disk adjunction.
Source: Hatcher, Appendix p.519. Its embedding property is not assumed. -/
def oldInclusion {n : ℕ} {X : TopCat.{u}} {k : ℕ} {a : Fin k → C(∂𝔻 n, X)} :
    X → adjunction n X k a :=
  fun x ↦ Quotient.mk _ (Sum.inl x)

/-- The original quotient map on the disk with label `i`.
Source: Hatcher, Appendix p.519. Its boundary map may identify different points. -/
def newCharacteristic {n : ℕ} {X : TopCat.{u}} {k : ℕ}
    {a : Fin k → C(∂𝔻 n, X)} (i : Fin k) : 𝔻 n → adjunction n X k a :=
  fun z ↦ Quotient.mk _ (Sum.inr (i, z))

end HolomorphicAnosov.FiniteCellAdjunction
