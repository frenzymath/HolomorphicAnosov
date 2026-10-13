import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Vanishing of a boundary class in native module homology

Source: Bredon, *Topology and Geometry*, VI §1 pp.316–320.
The native kernel/image quotient and predecessor comparison implement the
statement that a boundary represents the zero homology class.
-/

noncomputable section
open CategoryTheory
namespace HolomorphicAnosov
universe uR vM
variable {R : Type uR} [CommRing R]

set_option backward.isDefEq.respectTransparency false in
/-- An explicit incoming differential has zero class in the native module homology.
Source: Bredon, Topology and Geometry, VI §1 pp.316–320, homology as cycles
modulo boundaries. The successor degree exists also at degree zero. The comparison
with `dTo` puts the witness in the native image submodule, which the quotient kills. -/
theorem moduleCatHomologyClass_eq_zero_of_boundary
    (C : ChainComplex (ModuleCat.{vM} R) ℕ) (m n : ℕ)
    (hmn : (ComplexShape.down ℕ).Rel m n)
    (c : LinearMap.ker (C.dFrom n).hom)
    (hc : ∃ x : C.X m, (C.d m n).hom x = c.val) :
    (C.sc n).moduleCatHomologyIso.inv.hom
      ((C.sc n).moduleCatLeftHomologyData.π.hom c) = 0 := by
  obtain ⟨x, hx⟩ := hc
  have hmem : c ∈ LinearMap.range (C.sc n).moduleCatToCycles := by
    refine ⟨(C.xPrevIso hmn).inv.hom x,
      Subtype.ext ?_⟩
    exact (ConcreteCategory.congr_hom (C.xPrevIso_comp_dTo hmn) x).trans hx
  change (C.sc n).moduleCatHomologyIso.inv.hom
    ((LinearMap.range (C.sc n).moduleCatToCycles).mkQ c) = 0
  have hz : (LinearMap.range (C.sc n).moduleCatToCycles).mkQ c = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hmem
  rw [hz, map_zero]
end HolomorphicAnosov
