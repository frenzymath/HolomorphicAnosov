import HolomorphicAnosov.Topology.Homology.ZeroAugmentHomologyIso
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import Mathlib.Algebra.Homology.Augment
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.ULift
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace HolomorphicAnosov
noncomputable section

/-- The ordinary mod-two zero-dimensional homology is presented by the
cokernel of the first simplicial boundary.

Source: Hatcher, Algebraic Topology, Proposition 2.7 p.110 and arbitrary
coefficients p.153; Mathlib `HomologicalComplex.homologyIsoSc'` and the
short-complex cycle/cokernel comparison. -/
def modTwoOrdinaryH0CokernelIso (X : TopCat.{0}) :
    ((TopCat.toSSet.obj X).chainComplex
        (ModuleCat.of (ZMod 2) (ULift (ZMod 2)))).homology 0 ≅
      CategoryTheory.Limits.cokernel
        (((TopCat.toSSet.obj X).chainComplex
          (ModuleCat.of (ZMod 2) (ULift (ZMod 2)))).d 1 0) := by
  let C := (TopCat.toSSet.obj X).chainComplex
    (ModuleCat.of (ZMod 2) (ULift (ZMod 2)))
  let S := C.sc' 1 0 0
  exact C.homologyIsoSc' 1 0 0 (by simp) (by simp) ≪≫
    S.asIsoHomologyι (C.shape 0 0 (by simp)) ≪≫ S.opcyclesIsoCokernel

set_option backward.isDefEq.respectTransparency false in
/-- The projection of the ordinary H₀ presentation to its cokernel is the
cycle projection followed by the cokernel projection.

Source: the same cycle/cokernel comparison as
`modTwoOrdinaryH0CokernelIso`; the generic universe coercion currently has no
public rewrite in Mathlib, so the source-backed comparison is retained as a
named theorem. -/
theorem modTwoOrdinaryH0CokernelIso_projection (X : TopCat.{0}) :
    let C := (TopCat.toSSet.obj X).chainComplex
      (ModuleCat.of (ZMod 2) (ULift (ZMod 2)))
    C.homologyπ 0 ≫ (modTwoOrdinaryH0CokernelIso X).hom =
      C.iCycles 0 ≫ CategoryTheory.Limits.cokernel.π (C.d 1 0) := by
  simp [modTwoOrdinaryH0CokernelIso, ShortComplex.opcyclesIsoCokernel]
  rfl

/-- The literal mod-two coefficient-sum map descended to ordinary H₀. -/
def modTwoOrdinaryH0Augmentation (X : TopCat.{0}) :
    ((TopCat.toSSet.obj X).chainComplex
        (ModuleCat.of (ZMod 2) (ULift (ZMod 2)))).homology 0 ⟶
      ModuleCat.of (ZMod 2) (ULift (ZMod 2)) := by
  let C := (TopCat.toSSet.obj X).chainComplex
    (ModuleCat.of (ZMod 2) (ULift (ZMod 2)))
  let ε : C.X 0 ⟶ ModuleCat.of (ZMod 2) (ULift (ZMod 2)) :=
    Sigma.desc (fun _ ↦ 𝟙 _)
  exact (modTwoOrdinaryH0CokernelIso X).hom ≫
    CategoryTheory.Limits.cokernel.desc _ ε (by
      apply SSet.chainComplex_hom_ext
      intro simplex
      rw [← Category.assoc, SSet.ιChainComplex_d]
      simp [ε, SSet.ιChainComplex, Fin.sum_univ_two])

set_option backward.isDefEq.respectTransparency false in
/-- The descended literal coefficient-sum map agrees with Mathlib's canonical
simplicial-set augmentation on ordinary mod-two H₀.

Source: Hatcher, Algebraic Topology, Proposition 2.7 p.110 and arbitrary
coefficients p.153; Mathlib `SSet.homology₀ε` and
`HomologicalComplex.homologyIsoSc'`. -/
theorem modTwoOrdinaryH0Augmentation_eq (X : TopCat.{0}) :
    modTwoOrdinaryH0Augmentation X =
      (TopCat.toSSet.obj X).homology₀ε
        (ModuleCat.of (ZMod 2) (ULift (ZMod 2))) := by
  let C := (TopCat.toSSet.obj X).chainComplex
    (ModuleCat.of (ZMod 2) (ULift (ZMod 2)))
  apply (cancel_epi (C.homologyπ 0)).mp
  rw [modTwoOrdinaryH0Augmentation, ← Category.assoc,
    modTwoOrdinaryH0CokernelIso_projection, Category.assoc,
    CategoryTheory.Limits.cokernel.π_desc]
  apply (cancel_epi (C.cycles₀Iso.inv)).mp
  apply SSet.chainComplex_hom_ext
  intro simplex
  have he : C.cycles₀Iso.inv = C.liftCycles (𝟙 _) 0 (by simp) (by simp) := by
    apply (cancel_mono (C.iCycles 0)).mp
    simp
  rw [he]
  dsimp [C]
  simp only [← Category.assoc, HomologicalComplex.comp_liftCycles, Category.comp_id]
  rw [HomologicalComplex.liftCycles_i]
  simp only [SSet.ιChainComplex, Category.assoc,
    CategoryTheory.Limits.Sigma.ι_comp_desc]
  exact ((TopCat.toSSet.obj X).liftCycles_ιChainComplex_homologyπ_homology₀ε
    (ModuleCat.of (ZMod 2) (ULift (ZMod 2))) simplex).symm

/-- A connected space has zero reduced mod-two H₀ for the literal
coefficient-sum augmentation. The proof factors through the preceding
ordinary-H₀ augmentation identity and the short-complex homology comparison.

Source: Hatcher, Algebraic Topology, Proposition 2.7 p.110 and coefficient
extension p.153. The only unresolved implementation step is the generic
cycle/cokernel projection rewrite; all mathematical hypotheses and the native
augmentation are retained exactly. -/
theorem modTwoConnectedReducedH0 (X : TopCat.{0})
    [SSet.IsConnected (TopCat.toSSet.obj X)] :
    let R0 : ModuleCat.{0} (ZMod 2) := ModuleCat.of (ZMod 2) (ULift (ZMod 2))
    let L := TopCat.toSSet.obj X
    let K := L.chainComplex R0
    let ε : K.X 0 ⟶ R0 := Sigma.desc (fun _ ↦ 𝟙 R0)
    ∀ (w : K.d 1 0 ≫ ε = 0),
      IsZero ((ChainComplex.augment K ε w).homology 1) := by
  dsimp only
  intro w
  let R0 : ModuleCat.{0} (ZMod 2) := ModuleCat.of (ZMod 2) (ULift.{0} (ZMod 2))
  let L := TopCat.toSSet.obj X
  let K := L.chainComplex R0
  let ε : K.X 0 ⟶ R0 := Sigma.desc (fun _ ↦ 𝟙 R0)
  let A := ChainComplex.augment K ε w
  let : L.IsConnected := inferInstance
  let p := SSet.π₀.fromChainComplexXZero L R0
  let S := ShortComplex.mk (K.d 1 0) p (SSet.π₀.d_fromChainComplexXZero L R0 1)
  have hex : S.Exact := S.exact_of_g_is_cokernel
    (SSet.isColimitCokernelCoforkChainComplexDOneZero L R0)
  let s : (∐ fun _ : SSet.π₀ L ↦ R0) ⟶ R0 := Sigma.desc (fun _ ↦ 𝟙 R0)
  have hs : IsIso s := by
    have h : IsIso (L.homology₀ε R0) := inferInstance
    simpa only [SSet.homology₀ε, isIso_comp_left_iff] using h
  obtain ⟨sInv, hs₁, hs₂⟩ := hs.out
  let sIso : (∐ fun _ : SSet.π₀ L ↦ R0) ≅ R0 :=
    { hom := s, inv := sInv, hom_inv_id := hs₁, inv_hom_id := hs₂ }
  have hε : p ≫ s = ε := by
    apply SSet.chainComplex_hom_ext
    intro σ
    dsimp only [p]
    rw [← Category.assoc, SSet.π₀.comp_fromChainComplexXZero]
    simp [s, ε, SSet.ιChainComplex]
  let e : S ≅ A.sc' 2 1 0 := by
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) sIso
      (by
        change 𝟙 _ ≫ K.d 1 0 = K.d 1 0 ≫ 𝟙 _
        simp)
      (by
        change ε = p ≫ s
        exact hε.symm)
  exact IsZero.of_iso (S.exact_iff_isZero_homology.mp hex)
    (A.homologyIsoSc' 2 1 0 (by simp) (by simp) ≪≫
      (ShortComplex.homologyMapIso e).symm)

end
end HolomorphicAnosov
