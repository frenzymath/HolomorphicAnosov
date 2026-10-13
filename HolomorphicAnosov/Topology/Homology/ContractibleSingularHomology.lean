import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Topology.Homotopy.Contractible

open CategoryTheory CategoryTheory.Limits

namespace HolomorphicAnosov

/-- Positive-degree ordinary singular homology of a contractible space is zero. (Hatcher, Cor. 2.11) -/
theorem singular_homology_isZero_of_contractible {R : Type u} [Ring R]
    (X : TopCat.{u}) [ContractibleSpace X] (M : ModuleCat.{u} R)
    (n : ℕ) (hn : n ≠ 0) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj M).obj X) := by
  obtain ⟨x, ⟨H⟩⟩ := id_nullhomotopic X
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj M
  let P : TopCat.{u} := TopCat.of PUnit.{u+1}
  let f : X ⟶ P := TopCat.ofHom (ContinuousMap.const X PUnit.unit)
  let g : P ⟶ X := TopCat.ofHom (ContinuousMap.const P x)
  have hp : IsZero (F.obj P) :=
    AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat.{u} R) n M P hn
  have hH : F.map (𝟙 X) = F.map (f ≫ g) :=
    TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
      (f := 𝟙 X) (g := f ≫ g) H M n
  rw [F.map_id, F.map_comp, hp.eq_zero_of_tgt (F.map f), zero_comp] at hH
  exact (IsZero.iff_id_eq_zero _).mpr hH

end HolomorphicAnosov
