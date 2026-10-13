import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Successor-degree witnesses for module boundaries

Source: Bredon, *Topology and Geometry*, VI §1 pp.316–320: the boundaries in degree
`n` are the image of the degree `n + 1` differential. The predecessor comparison
identifies Mathlib's native incoming object with that explicit degree.
-/

noncomputable section
open CategoryTheory
namespace HolomorphicAnosov
universe uR vM
variable {R : Type uR} [CommRing R]

/-- Every boundary cycle has a primitive in the successor degree, including degree zero.
Source: Bredon VI §1 pp.316–320, image of the incoming differential.
Proof: write the cycle as the image of an element of the native predecessor object.
Apply `xPrevIso` to this element to obtain an element in degree `n + 1`.
The `dTo_eq` comparison identifies its differential with the original incoming map;
taking values in the cycle subtype gives the desired equality. -/
theorem moduleCatBoundary_exists_successor
    (C : ChainComplex (ModuleCat.{vM} R) ℕ) (n : ℕ)
    (c : LinearMap.ker (C.dFrom n).hom)
    (hc : c ∈ LinearMap.range (C.sc n).moduleCatToCycles) :
    ∃ x : C.X (n + 1), (C.d (n + 1) n).hom x = c.val := by
  obtain ⟨x, hx⟩ := hc
  refine ⟨(C.xPrevIso (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl)).hom.hom x, ?_⟩
  calc
    _ = (C.dTo n).hom x :=
      (ConcreteCategory.congr_hom (C.dTo_eq (show (ComplexShape.down ℕ).Rel
        (n + 1) n from rfl)) x).symm
    _ = c.val := congrArg Subtype.val hx

end HolomorphicAnosov
