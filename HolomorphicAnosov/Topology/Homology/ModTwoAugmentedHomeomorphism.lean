import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
import Mathlib.Algebra.Homology.Augment
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.ULift

/-!
# Homeomorphism comparison on the fixed modulus-two augmented singular complexes

Source: Hatcher, Algebraic Topology, reduced augmentation p.110, induced chain
maps pp.111–113, and the explicit coefficient extension p.153. The coefficient
object is literally `ModuleCat.of (ZMod 2) (ULift.{0} (ZMod 2))` throughout.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace HolomorphicAnosov
noncomputable section

/-- A homeomorphism induces an isomorphism of the actual augmented complexes,
with coefficient identity in degree zero and its singular chain map in each
successor degree. Both augmentation boundary witnesses are constructed.

Source: Hatcher pp.110–113,153. The two endpoint coefficients cancel, so the
coefficient-sum augmentation kills the first boundary. Postcomposition preserves
coefficient sum. Insert identity in degree zero and the ordinary chain map in
successor degrees; the augmentation square and ordinary chain-map squares prove
this is a chain map. Do the same for the inverse homeomorphism. The two composites
are identity componentwise by the singular-chain functor laws. No connectedness,
nonemptiness or sphere homology assertion is used.

For empty spaces the ordinary chain objects vanish but the added coefficient
object remains; its comparison is still the identity. Hatcher's p.110
nonemptiness convention avoids nonzero homology in degree minus one, which is
not asserted to vanish here. -/
theorem modTwoAugmentedHomeomorphism (X Y : TopCat.{0}) (e : X ≃ₜ Y) :
    let R0 : ModuleCat.{0} (ZMod 2) := ModuleCat.of (ZMod 2) (ULift.{0} (ZMod 2))
    let LX := TopCat.toSSet.obj X
    let LY := TopCat.toSSet.obj Y
    let KX := LX.chainComplex R0
    let KY := LY.chainComplex R0
    let εX : KX.X 0 ⟶ R0 := Sigma.desc (fun _ : LX _⦋0⦌ ↦ 𝟙 R0)
    let εY : KY.X 0 ⟶ R0 := Sigma.desc (fun _ : LY _⦋0⦌ ↦ 𝟙 R0)
    ∃ (wX : KX.d 1 0 ≫ εX = 0) (wY : KY.d 1 0 ≫ εY = 0),
      ∃ a : ChainComplex.augment KX εX wX ≅ ChainComplex.augment KY εY wY,
        a.hom.f 0 = 𝟙 R0 ∧ ∀ q : ℕ, a.hom.f (q + 1) =
          (SSet.chainComplexMap (TopCat.toSSet.map
            (TopCat.ofHom ⟨e, e.continuous_toFun⟩)) R0).f q := by
  dsimp only
  let R0 : ModuleCat.{0} (ZMod 2) := ModuleCat.of (ZMod 2) (ULift.{0} (ZMod 2))
  let K (Z : TopCat.{0}) := (TopCat.toSSet.obj Z).chainComplex R0
  let ε (Z : TopCat.{0}) : (K Z).X 0 ⟶ R0 := Sigma.desc (fun _ ↦ 𝟙 R0)
  have w (Z : TopCat.{0}) : (K Z).d 1 0 ≫ ε Z = 0 := by
    apply SSet.chainComplex_hom_ext
    intro σ
    rw [← Category.assoc, SSet.ιChainComplex_d]
    simp [ε, SSet.ιChainComplex, Fin.sum_univ_two]
  let A (Z : TopCat.{0}) := ChainComplex.augment (K Z) (ε Z) (w Z)
  let F {Z W : TopCat.{0}} (f : Z ⟶ W) : A Z ⟶ A W :=
    ChainComplex.ofHom
      (fun n ↦ match n with
        | 0 => 𝟙 R0
        | n + 1 => (SSet.chainComplexMap (TopCat.toSSet.map f) R0).f n)
      (fun n ↦ by
        cases n with
        | zero =>
          change (SSet.chainComplexMap (TopCat.toSSet.map f) R0).f 0 ≫ ε W = ε Z ≫ 𝟙 _
          apply SSet.chainComplex_hom_ext
          intro σ
          rw [← Category.assoc, SSet.ι_chainComplexMap_f]
          simp [ε, SSet.ιChainComplex]
        | succ n =>
          exact (SSet.chainComplexMap (TopCat.toSSet.map f) R0).comm (n + 1) n)
  let f : X ⟶ Y := TopCat.ofHom ⟨e, e.continuous_toFun⟩
  let g : Y ⟶ X := TopCat.ofHom ⟨e.symm, e.continuous_invFun⟩
  have hfg : f ≫ g = 𝟙 X := by ext x; exact e.symm_apply_apply x
  have hgf : g ≫ f = 𝟙 Y := by ext y; exact e.apply_symm_apply y
  have comp {Z W V : TopCat.{0}} (f' : Z ⟶ W) (g' : W ⟶ V) :
      F f' ≫ F g' = F (f' ≫ g') := by
    apply HomologicalComplex.hom_ext
    intro n
    cases n <;> simp [F, SSet.chainComplexMap] <;> rfl
  have ident (Z : TopCat.{0}) : F (𝟙 Z) = 𝟙 (A Z) := by
    apply HomologicalComplex.hom_ext
    intro n
    cases n <;> simp [F, SSet.chainComplexMap] <;> rfl
  refine ⟨w X, w Y, ⟨F f, F g, ?_, ?_⟩, rfl, fun q ↦ rfl⟩
  · rw [comp, hfg, ident]
  · rw [comp, hgf, ident]

end
end HolomorphicAnosov
