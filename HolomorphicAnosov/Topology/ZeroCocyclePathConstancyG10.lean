import HolomorphicAnosov.AlgebraicTopology.SingularCochainCohomologyDefinition
import Mathlib.Topology.Homotopy.TopCat.ZerothHomotopy

/-!
# Path constancy of degree-zero singular cocycles

Source: Hatcher, *Algebraic Topology*, printed pp.197–198. Evaluating the
cocycle equation on a singular edge shows equality of its endpoint values.
The proof below is the agent-written expansion recorded in
`topo.zero_cocycle_path_constancy_g10`.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace HolomorphicAnosov.SingularCochain
noncomputable section

set_option backward.isDefEq.respectTransparency false in
/-- A degree-zero singular cocycle has equal evaluations on vertices joined by
an actual path.  This is the literal alternating-boundary calculation in the
singular complex: the cocycle equation evaluated on the singular edge says
its terminal value minus its initial value is zero.
Source: Hatcher, Algebraic Topology, pp.197-198, with Mathlib's
`TopCat.toSSetObjEdgeEquiv` supplying the singular edge for a path. -/
theorem zero_cocycle_eval_eq_of_path (R : Type) [CommRing R]
    (X : TopCat) [PathConnectedSpace X]
    (a : cycles R (complex R X) 0) (x y : X) :
    (show ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)).X 0 ⟶
      ModuleCat.of R R from a.val)
        ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of R R)
          (TopCat.toSSetObj₀Equiv.symm x) 1) =
      (show ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)).X 0 ⟶
        ModuleCat.of R R from a.val)
        ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of R R)
          (TopCat.toSSetObj₀Equiv.symm y) 1) := by
  let e : SSet.Edge (TopCat.toSSetObj₀Equiv.symm x)
      (TopCat.toSSetObj₀Equiv.symm y) :=
    TopCat.toSSetObjEdgeEquiv.symm
      (TopCat.pathEquiv.symm (PathConnectedSpace.somePath x y))
  have ha := a.property
  change ((complex R X).d 0 ((ComplexShape.up ℕ).next 0)).hom a.val = 0 at ha
  rw [(ComplexShape.up ℕ).next_eq' (ComplexShape.up_mk 0 1 rfl)] at ha
  change ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)).d 1 0 ≫ a.val = 0 at ha
  have h := congrArg
    (fun f ↦ (TopCat.toSSet.obj X).ιChainComplex
      (R := ModuleCat.of R R) e.edge ≫ f) ha
  rw [← Category.assoc, SSet.ιChainComplex_d] at h
  simp [e, Preadditive.add_comp] at h
  have hxy := (eq_of_sub_eq_zero (show
    (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of R R)
      (TopCat.toSSetObj₀Equiv.symm y) ≫ a.val -
    (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of R R)
      (TopCat.toSSetObj₀Equiv.symm x) ≫ a.val = 0 by
    simpa only [sub_eq_add_neg, Preadditive.neg_comp] using h)).symm
  exact congrArg (fun f : ModuleCat.of R R ⟶ ModuleCat.of R R ↦ f 1) hxy

end
end HolomorphicAnosov.SingularCochain

