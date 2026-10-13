import HolomorphicAnosov.Algebra.Homology.FieldChainKroneckerEvaluation
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.BifunctorHomotopy
import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-!
# Homology models for chain complexes over a field

Choose linear representatives for every cycle quotient. They form a chain map
from the zero-differential homology complex, inducing the identity on homology.
Mathlib's projective-complex theorem turns it into a homotopy equivalence.
The additive-bifunctor homotopy constructors show that tensoring two such
homotopy equivalences again gives a homotopy equivalence.

This is an independent algebraic implementation of the field-splitting
principle behind Bredon, *Topology and Geometry*, VI §1, pp.318–320.
-/

open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
noncomputable section

namespace HolomorphicAnosov.FieldComplexHomologyModel
open FieldChainKronecker
variable {K : Type u} [Field K]

/-- The zero-differential complex of the homology vector spaces. Source:
Bredon, Topology and Geometry, VI §1, pp.318–320; split cycles over a field. -/
def model (C : ChainComplex (ModuleCat.{u} K) ℕ) : ChainComplex (ModuleCat.{u} K) ℕ where
  X n := ModuleCat.of K (degreeHomology.{u,u} C n)
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := by simp

/-- Choose a linear cycle representative for each homology class by projectivity.
Source: Bredon VI §1, p.318, split cycle/boundary vector spaces. -/
def sectionToCycles (C : ChainComplex (ModuleCat.{u} K) ℕ) (n : ℕ) :
    (model C).X n ⟶ (C.sc n).moduleCatLeftHomologyData.K := by
  letI : Epi (C.sc n).moduleCatLeftHomologyData.π :=
    ⟨fun _ _ ↦ Limits.Cofork.IsColimit.hom_ext (C.sc n).moduleCatLeftHomologyData.hπ⟩
  exact Projective.factorThru (𝟙 _) (C.sc n).moduleCatLeftHomologyData.π

/-- The chosen representatives define a chain map since they are cycles.
Source: Bredon VI §1 pp.318–320. -/
def inclusion (C : ChainComplex (ModuleCat.{u} K) ℕ) : model C ⟶ C where
  f n := sectionToCycles C n ≫ (C.sc n).moduleCatLeftHomologyData.i
  comm' p r hpr := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    simp only [model, Limits.zero_comp, ModuleCat.hom_zero, LinearMap.zero_apply]
    change (C.d p r).hom ((sectionToCycles C p).hom z).val = 0
    rw [← (ComplexShape.down ℕ).next_eq' hpr]
    exact ((sectionToCycles C p).hom z).property

/-- The homology-model inclusion is a quasi-isomorphism: its map on homology
is the identity, because the cycle section is a right inverse to the quotient.
This implements the field splitting used in Bredon VI §1 pp.318–320. -/
theorem inclusion_quasiIso (C : ChainComplex (ModuleCat.{u} K) ℕ) :
    QuasiIso (inclusion C) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff]
  let S := (model C).sc n
  let T := C.sc n
  let φ := (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} K)
    (ComplexShape.down ℕ) n).map (inclusion C)
  let hS : S.LeftHomologyData := ShortComplex.LeftHomologyData.ofZeros S rfl rfl
  let hT : T.LeftHomologyData := T.moduleCatLeftHomologyData
  let γ : ShortComplex.LeftHomologyMapData φ hS hT :=
    { φK := sectionToCycles C n
      φH := 𝟙 _
      commi := by
        change sectionToCycles C n ≫ _ = 𝟙 _ ≫ (sectionToCycles C n ≫ _)
        rw [Category.id_comp]
      commf' := by
        apply (cancel_mono hT.i).mp
        simp only [Category.assoc, ShortComplex.LeftHomologyData.f'_i]
        rw [show hS.f' = 0 from ShortComplex.LeftHomologyData.ofZeros_f' _ _ _]
        simp only [Limits.zero_comp]
        change 0 = ((inclusion C).f ((ComplexShape.down ℕ).prev n) ≫ C.dTo n)
        rw [(inclusion C).comm_to n]
        change 0 = (0 : (model C).X _ ⟶ (model C).X n) ≫ _
        simp
      commπ := by
        change 𝟙 _ ≫ 𝟙 _ = sectionToCycles C n ≫ T.moduleCatLeftHomologyData.π
        simp [sectionToCycles, T, Projective.factorThru_comp] }
  exact γ.quasiIso_iff.mpr (show IsIso (𝟙 ((model C).X n)) from inferInstance)

/-- Over a field the inclusion of chosen homology representatives is a chain
homotopy equivalence. Every vector space is projective, so Mathlib's theorem
that a quasi-isomorphism of bounded-below projective complexes is a homotopy
equivalence applies to the preceding quasi-isomorphism. Source: Bredon VI §1,
pp.318–320, splitting argument; Mathlib ChainComplex.quasiIso_iff_of_projective. -/
theorem inclusion_homotopyEquivalence (C : ChainComplex (ModuleCat.{u} K) ℕ) :
    ∃ e : HomotopyEquiv (model C) C, e.hom = inclusion C :=
  (ChainComplex.quasiIso_iff_of_projective (inclusion C)).mp (inclusion_quasiIso C)

/-- A quasi-isomorphism acts bijectively on the explicit kernel/image quotient.
The concrete module homology data compute the abstract homology map, so the
quasi-isomorphism criterion is exactly bijectivity of this linear map. -/
theorem degreeHomologyMap_bijective {C D : ChainComplex (ModuleCat.{u} K) ℕ}
    (f : C ⟶ D) [QuasiIso f] (n : ℕ) :
    Function.Bijective (degreeHomologyMap.{u,u} f n) := by
  let φ := (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} K)
    (ComplexShape.down ℕ) n).map f
  let γ : ShortComplex.LeftHomologyMapData φ (C.sc n).moduleCatLeftHomologyData
      (D.sc n).moduleCatLeftHomologyData :=
    { φK := ModuleCat.ofHom (cycleMap f n)
      φH := ModuleCat.ofHom (degreeHomologyMap f n)
      commi := by ext z; rfl
      commf' := by
        ext z
        apply Subtype.ext
        exact (ConcreteCategory.congr_hom (f.comm_to n) z).symm
      commπ := by ext z; rfl }
  have hg : ShortComplex.QuasiIso φ := (quasiIsoAt_iff f n).mp inferInstance
  have hi : IsIso γ.φH := γ.quasiIso_iff.mp hg
  exact (ConcreteCategory.isIso_iff_bijective γ.φH).mp hi

@[simp] theorem tensorHom_comp {C C' C'' D D' D'' : ChainComplex (ModuleCat.{u} K) ℕ}
    (a : C ⟶ C') (b : C' ⟶ C'') (c : D ⟶ D') (d : D' ⟶ D'') :
    HomologicalComplex.tensorHom (a ≫ b) (c ≫ d) =
      HomologicalComplex.tensorHom a c ≫ HomologicalComplex.tensorHom b d := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  simp [HomologicalComplex.tensorHom, Category.assoc, MonoidalCategory.whisker_exchange_assoc]

@[simp] theorem tensorHom_id (C D : ChainComplex (ModuleCat.{u} K) ℕ) :
    HomologicalComplex.tensorHom (𝟙 C) (𝟙 D) = 𝟙 (HomologicalComplex.tensorObj C D) := by
  simp [HomologicalComplex.tensorHom, HomologicalComplex.mapBifunctorMap]

/-- Tensoring two chain homotopy equivalences gives a chain homotopy
 equivalence. Apply the additive-bifunctor homotopy construction in each
factor successively; the composition and identity laws are functoriality. -/
def tensorHomotopyEquiv {C C' D D' : ChainComplex (ModuleCat.{u} K) ℕ}
    (e : HomotopyEquiv C C') (f : HomotopyEquiv D D') :
    HomotopyEquiv (HomologicalComplex.tensorObj C D) (HomologicalComplex.tensorObj C' D') where
  hom := HomologicalComplex.tensorHom e.hom f.hom
  inv := HomologicalComplex.tensorHom e.inv f.inv
  homotopyHomInvId := by
    have h₁ := HomologicalComplex.mapBifunctorMapHomotopy₁ e.homotopyHomInvId
      (f.hom ≫ f.inv) (MonoidalCategory.curriedTensor (ModuleCat.{u} K)) (ComplexShape.down ℕ)
    have h₂ := HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 C) f.homotopyHomInvId
      (MonoidalCategory.curriedTensor (ModuleCat.{u} K)) (ComplexShape.down ℕ)
    change Homotopy (HomologicalComplex.tensorHom _ _ ≫ HomologicalComplex.tensorHom _ _) _
    simpa only [← tensorHom_comp, tensorHom_id] using h₁.trans h₂
  homotopyInvHomId := by
    have h₁ := HomologicalComplex.mapBifunctorMapHomotopy₁ e.homotopyInvHomId
      (f.inv ≫ f.hom) (MonoidalCategory.curriedTensor (ModuleCat.{u} K)) (ComplexShape.down ℕ)
    have h₂ := HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 C') f.homotopyInvHomId
      (MonoidalCategory.curriedTensor (ModuleCat.{u} K)) (ComplexShape.down ℕ)
    change Homotopy (HomologicalComplex.tensorHom _ _ ≫ HomologicalComplex.tensorHom _ _) _
    simpa only [← tensorHom_comp, tensorHom_id] using h₁.trans h₂

end HolomorphicAnosov.FieldComplexHomologyModel

