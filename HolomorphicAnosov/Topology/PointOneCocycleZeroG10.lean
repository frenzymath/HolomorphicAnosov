import HolomorphicAnosov.AlgebraicTopology.SingularCochainCohomologyDefinition

/-!
# Degree-one singular cocycles on a point

Source: Hatcher, Algebraic Topology, Proposition 2.8, p.110; cochain definition,
pp.197–198. DAG node: `topo.point_one_cocycle_zero_g10`.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
noncomputable section
namespace HolomorphicAnosov.SingularCochain

set_option backward.isDefEq.respectTransparency false in
/-- Every degree-one singular cocycle on the actual one-point space is zero.
Source: Hatcher, Algebraic Topology, the Proposition 2.8 point-chain calculation p.110 and
the dual cochain definition pp.197–198. There is one simplex in each degree.
The three faces of the unique two-simplex coincide, so its boundary is the
unique one-simplex with coefficient 1 - 1 + 1 = 1. A cocycle kills this
boundary, hence kills the generator and is zero by coproduct extensionality.
This argument works in every commutative ring, including characteristic two.
-/
theorem point_one_cocycle_eq_zero (R : Type) [CommRing R]
    (a : cycles R (complex R (TopCat.of PUnit)) 1) : a = 0 := by
  let X := TopCat.of PUnit
  let S := TopCat.toSSet.obj X
  have hs (n : ℕ) : Subsingleton (S _⦋n⦌) := by
    apply (TopCat.toSSetObjEquiv X (op ⦋n⦌)).injective.subsingleton
  let (n : ℕ) : Subsingleton (S _⦋n⦌) := hs n
  let σ : S _⦋2⦌ := (TopCat.toSSetObjEquiv X (op ⦋2⦌)).symm
    (ContinuousMap.const _ PUnit.unit)
  have ha := a.property
  change ((complex R X).d 1 ((ComplexShape.up ℕ).next 1)).hom a.val = 0 at ha
  rw [(ComplexShape.up ℕ).next_eq' (ComplexShape.up_mk 1 2 rfl)] at ha
  change (S.chainComplex (ModuleCat.of R R)).d 2 1 ≫ a.val = 0 at ha
  apply Subtype.ext
  apply SSet.chainComplex_hom_ext
  intro τ
  have h := congrArg (fun f ↦ S.ιChainComplex (R := ModuleCat.of R R) σ ≫ f) ha
  rw [← Category.assoc, SSet.ιChainComplex_d] at h
  have hf (i : Fin 3) : S.δ i σ = τ := Subsingleton.elim _ _
  simpa [Fin.sum_univ_succ, hf, Preadditive.add_comp] using h

end HolomorphicAnosov.SingularCochain
