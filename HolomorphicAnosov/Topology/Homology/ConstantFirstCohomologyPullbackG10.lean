import HolomorphicAnosov.AlgebraicTopology.SingularCochainCohomologyDefinition
import HolomorphicAnosov.Topology.Homology.PointFirstCohomologyZeroG10

/-!
Constant maps annihilate first singular cohomology. (Hatcher, Prop. 2.8)
-/

open CategoryTheory Opposite

noncomputable section
namespace HolomorphicAnosov.SingularCochain

set_option backward.isDefEq.respectTransparency false in
/-- Constant maps kill every degree-one singular cohomology class over a commutative ring. (Hatcher, Prop. 2.8) -/
theorem constant_first_cohomology_pullback_eq_zero (R : Type) [CommRing R]
    (X Y : TopCat) (y : Y) (a : cohomology R Y 1) :
    cohomologyPullback R (TopCat.ofHom (ContinuousMap.const X y)) 1 a = 0 := by
  let f : X ⟶ TopCat.of PUnit := TopCat.ofHom (ContinuousMap.const X PUnit.unit)
  let g : TopCat.of PUnit ⟶ Y := TopCat.ofHom (ContinuousMap.const PUnit y)
  have hfactor : TopCat.ofHom (ContinuousMap.const X y) = f ≫ g := rfl
  rw [hfactor]
  calc
    cohomologyPullback R (f ≫ g) 1 a =
        cohomologyPullback R f 1 (cohomologyPullback R g 1 a) := by
      change (cohomologyPullback R (f ≫ g) 1) a =
        (cohomologyPullback R g 1 ≫ cohomologyPullback R f 1) a
      congr 1
      unfold cohomologyPullback quotientMap pullback
      rw [op_comp, Functor.map_comp, HomologicalComplex.homologyMap_comp]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = 0 := by
      let := point_first_cohomology_subsingleton R
      rw [show cohomologyPullback R g 1 a = 0 from Subsingleton.elim _ _, map_zero]

end HolomorphicAnosov.SingularCochain

