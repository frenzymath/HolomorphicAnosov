import HolomorphicAnosov.Topology.Homology.ModTwoAugmentedHomeomorphIso
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Convex.Contractible

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HolomorphicAnosov.Topology.Homology

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe u
abbrev modTwoCoefficients : ModuleCat.{u} (ZMod 2) := ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))

def modTwoSingularAugmentation (X : TopCat.{u}) :
    ((TopCat.toSSet.obj X).chainComplex modTwoCoefficients).X 0 ⟶ modTwoCoefficients :=
  Sigma.desc (fun _ ↦ 𝟙 modTwoCoefficients)

def modTwoAugmentedSingularChains (X : TopCat.{u}) :
    ChainComplex (ModuleCat.{u} (ZMod 2)) ℕ :=
  ChainComplex.augment
    ((TopCat.toSSet.obj X).chainComplex modTwoCoefficients)
    (modTwoSingularAugmentation X) (by
      apply SSet.chainComplex_hom_ext
      intro σ
      rw [← Category.assoc, SSet.ιChainComplex_d]
      simp [modTwoSingularAugmentation, SSet.ιChainComplex, Fin.sum_univ_two])

def modTwoAugmentedSingularChainsMap {X Y : TopCat.{u}} (f : X ⟶ Y) :
    modTwoAugmentedSingularChains X ⟶ modTwoAugmentedSingularChains Y :=
  ChainComplex.ofHom
    (fun n ↦ match n with
      | 0 => 𝟙 modTwoCoefficients
      | n + 1 =>
        (SSet.chainComplexMap (TopCat.toSSet.map f) modTwoCoefficients).f n)
    (fun n ↦ by
      cases n with
      | zero =>
        change (SSet.chainComplexMap (TopCat.toSSet.map f) modTwoCoefficients).f 0 ≫
          modTwoSingularAugmentation Y = modTwoSingularAugmentation X ≫ 𝟙 _
        apply SSet.chainComplex_hom_ext
        intro σ
        rw [← Category.assoc, SSet.ι_chainComplexMap_f]
        simp [modTwoSingularAugmentation, SSet.ιChainComplex]
      | succ n =>
        exact (SSet.chainComplexMap (TopCat.toSSet.map f) modTwoCoefficients).comm (n + 1) n)

set_option backward.isDefEq.respectTransparency false in
/-- The actual singular prism homotopy extends over coefficient augmentation:
the added-degree homotopy components are zero, and successor components are
Mathlib's original prism. Its degree-one equation is the original degree-zero
equation, with the additional augmentation term zero. Source: Hatcher pp.110–113. -/
def modTwoAugmentedSingularChainsHomotopy {X Y : TopCat.{u}}
    {f g : X ⟶ Y} (H : TopCat.Homotopy f g) :
    _root_.Homotopy (modTwoAugmentedSingularChainsMap f)
      (modTwoAugmentedSingularChainsMap g) where
  hom i j := match i, j with
    | i + 1, j + 1 => (H.toSSet.chainComplexMap modTwoCoefficients).hom i j
    | _, _ => 0
  zero i j hij := by
    cases i with
    | zero => rfl
    | succ i =>
      cases j with
      | zero => rfl
      | succ j =>
        exact (H.toSSet.chainComplexMap modTwoCoefficients).zero i j
          (by simpa using hij)
  comm i := by
    cases i with
    | zero =>
      rw [dNext_eq_zero _ _ (by simp),
        prevD_eq _ (show (ComplexShape.down ℕ).Rel 1 0 from rfl)]
      simp [modTwoAugmentedSingularChainsMap, ChainComplex.ofHom, zero_add]
    | succ i =>
      rw [dNext_eq _ (show (ComplexShape.down ℕ).Rel (i + 1) i from rfl),
        prevD_eq _ (show (ComplexShape.down ℕ).Rel (i + 2) (i + 1) from rfl)]
      cases i with
      | zero =>
        simpa [dNext_eq_zero _ _ (show ¬ (ComplexShape.down ℕ).Rel 0
            ((ComplexShape.down ℕ).next 0) from by simp), CategoryTheory.Limits.comp_zero, zero_add,
          prevD_eq _ (show (ComplexShape.down ℕ).Rel 1 0 from rfl),
          modTwoAugmentedSingularChainsMap, modTwoAugmentedSingularChains,
          ChainComplex.ofHom, ChainComplex.augment] using
          (H.toSSet.chainComplexMap modTwoCoefficients).comm 0
      | succ i =>
        simpa [dNext_eq _ (show (ComplexShape.down ℕ).Rel (i + 1) i from rfl),
          prevD_eq _ (show (ComplexShape.down ℕ).Rel (i + 2) (i + 1) from rfl),
          modTwoAugmentedSingularChainsMap, modTwoAugmentedSingularChains,
          ChainComplex.ofHom, ChainComplex.augment] using
          (H.toSSet.chainComplexMap modTwoCoefficients).comm (i + 1)

def modTwoAugmentedSingularChainsFunctor : TopCat.{u} ⥤ ChainComplex (ModuleCat.{u} (ZMod 2)) ℕ where
  obj := modTwoAugmentedSingularChains
  map := modTwoAugmentedSingularChainsMap
  map_id X := by
    apply HomologicalComplex.Hom.ext
    funext n
    cases n <;> simp [modTwoAugmentedSingularChainsMap, SSet.chainComplexMap] <;> rfl
  map_comp f g := by
    apply HomologicalComplex.Hom.ext
    funext n
    cases n <;> simp [modTwoAugmentedSingularChainsMap, SSet.chainComplexMap] <;> rfl

end HolomorphicAnosov.Topology.Homology
namespace HolomorphicAnosov.Topology.Homology

theorem modTwoAugmentedHomologyIso
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (q : ℕ) :
    Nonempty ((modTwoAugmentedSingularChains (TopCat.of X)).homology q ≅
      (modTwoAugmentedSingularChains (TopCat.of Y)).homology q) := by
  let f : TopCat.of X ⟶ TopCat.of Y := TopCat.ofHom e.toFun
  let g : TopCat.of Y ⟶ TopCat.of X := TopCat.ofHom e.invFun
  let F := modTwoAugmentedSingularChainsFunctor.map f
  let G := modTwoAugmentedSingularChainsFunctor.map g
  have hfg : F ≫ G = modTwoAugmentedSingularChainsFunctor.map (f ≫ g) := by
    exact (modTwoAugmentedSingularChainsFunctor.map_comp f g).symm
  have hgf : G ≫ F = modTwoAugmentedSingularChainsFunctor.map (g ≫ f) := by
    exact (modTwoAugmentedSingularChainsFunctor.map_comp g f).symm
  have hfg' : TopCat.Homotopy (f ≫ g) (𝟙 _) := e.left_inv.some
  have hgf' : TopCat.Homotopy (g ≫ f) (𝟙 _) := e.right_inv.some
  have hF : HomologicalComplex.homologyMap
      (modTwoAugmentedSingularChainsFunctor.map (f ≫ g)) q =
      HomologicalComplex.homologyMap
        (modTwoAugmentedSingularChainsFunctor.map (𝟙 _)) q := by
    have hh := (modTwoAugmentedSingularChainsHomotopy hfg').homologyMap_eq q
    change HomologicalComplex.homologyMap (modTwoAugmentedSingularChainsMap (f ≫ g)) q =
      HomologicalComplex.homologyMap (modTwoAugmentedSingularChainsMap (𝟙 _)) q
    exact hh
  have hG : HomologicalComplex.homologyMap
      (modTwoAugmentedSingularChainsFunctor.map (g ≫ f)) q =
      HomologicalComplex.homologyMap
        (modTwoAugmentedSingularChainsFunctor.map (𝟙 _)) q := by
    have hh := (modTwoAugmentedSingularChainsHomotopy hgf').homologyMap_eq q
    change HomologicalComplex.homologyMap (modTwoAugmentedSingularChainsMap (g ≫ f)) q =
      HomologicalComplex.homologyMap (modTwoAugmentedSingularChainsMap (𝟙 _)) q
    exact hh
  change Nonempty ((modTwoAugmentedSingularChainsFunctor.obj (TopCat.of X)).homology q ≅
    (modTwoAugmentedSingularChainsFunctor.obj (TopCat.of Y)).homology q)
  refine ⟨⟨HomologicalComplex.homologyMap F q,
    HomologicalComplex.homologyMap G q, ?_, ?_⟩⟩
  · rw [← HomologicalComplex.homologyMap_comp, hfg]
    simpa only [modTwoAugmentedSingularChainsFunctor.map_id, HomologicalComplex.homologyMap_id] using hF
  · rw [← HomologicalComplex.homologyMap_comp, hgf]
    simpa only [modTwoAugmentedSingularChainsFunctor.map_id, HomologicalComplex.homologyMap_id] using hG

end HolomorphicAnosov.Topology.Homology
open scoped Simplicial
namespace HolomorphicAnosov

/-- A continuous homotopy equivalence preserves the literal augmented mod-two
singular homology complexes, including arbitrary boundary-zero witnesses.
Source: Hatcher, Algebraic Topology, pp.110--113 and p.153. -/
theorem modTwoAugmentedHomotopyEquivIso
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) :
    let R0 : ModuleCat.{u} (ZMod 2) :=
      ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))
    let LX := TopCat.toSSet.obj (TopCat.of X)
    let LY := TopCat.toSSet.obj (TopCat.of Y)
    let KX := LX.chainComplex R0
    let KY := LY.chainComplex R0
    let εX : KX.X 0 ⟶ R0 := Sigma.desc (fun _ : LX _⦋0⦌ ↦ 𝟙 R0)
    let εY : KY.X 0 ⟶ R0 := Sigma.desc (fun _ : LY _⦋0⦌ ↦ 𝟙 R0)
    ∀ (wX : KX.d 1 0 ≫ εX = 0) (wY : KY.d 1 0 ≫ εY = 0) (q : ℕ),
      Nonempty ((ChainComplex.augment KX εX wX).homology q ≅
        (ChainComplex.augment KY εY wY).homology q) := by
  dsimp only
  intro wX wY q
  let wX₀ :
      ((TopCat.toSSet.obj (TopCat.of X)).chainComplex
        Topology.Homology.modTwoCoefficients).d 1 0 ≫
          Topology.Homology.modTwoSingularAugmentation (TopCat.of X) = 0 := by
    apply SSet.chainComplex_hom_ext
    intro σ
    rw [← Category.assoc, SSet.ιChainComplex_d]
    simp [Topology.Homology.modTwoSingularAugmentation, SSet.ιChainComplex,
      Fin.sum_univ_two]
  let wY₀ :
      ((TopCat.toSSet.obj (TopCat.of Y)).chainComplex
        Topology.Homology.modTwoCoefficients).d 1 0 ≫
          Topology.Homology.modTwoSingularAugmentation (TopCat.of Y) = 0 := by
    apply SSet.chainComplex_hom_ext
    intro σ
    rw [← Category.assoc, SSet.ιChainComplex_d]
    simp [Topology.Homology.modTwoSingularAugmentation, SSet.ιChainComplex,
      Fin.sum_univ_two]
  have hwX : wX = wX₀ := Subsingleton.elim _ _
  have hwY : wY = wY₀ := Subsingleton.elim _ _
  cases hwX
  cases hwY
  simpa [Topology.Homology.modTwoAugmentedSingularChains, Topology.Homology.modTwoSingularAugmentation] using
    Topology.Homology.modTwoAugmentedHomologyIso e q


end HolomorphicAnosov
