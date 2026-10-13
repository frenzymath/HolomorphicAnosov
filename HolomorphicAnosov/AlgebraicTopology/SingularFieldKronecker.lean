import HolomorphicAnosov.Algebra.Homology.FieldChainKroneckerEvaluation
import HolomorphicAnosov.AlgebraicTopology.SingularCochainCupProductDefinition

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
noncomputable section
namespace HolomorphicAnosov.SingularFieldKronecker
variable {K : Type} [Field K]


/-- The functorial singular dual and the field-evaluation dual have the same genuine degreewise
linear functionals; this comparison uses no cohomology equivalence supplied as a hypothesis. -/
def singularDualIso (X : TopCat) :
    SingularCochain.complex K X ≅
      FieldChainKronecker.dualComplex ((SingularCochain.chainFunctor K).obj X) :=
  HomologicalComplex.Hom.isoOfComponents (fun k ↦
    { hom := ModuleCat.ofHom
        { toFun := fun a ↦ a.hom
          map_add' := by intros; rfl
          map_smul' := by intros; rfl }
      inv := ModuleCat.ofHom
        { toFun := fun a ↦ ModuleCat.ofHom a
          map_add' := by intros; rfl
          map_smul' := by intros; rfl } }) (by intros; ext a; rfl)




set_option backward.isDefEq.respectTransparency false in
/-- Canonical transport between the two literal kernel/image quotient presentations of singular
cohomology, induced by the degreewise functional identification. -/
def singularFieldCohomologyEquiv (X : TopCat) (k : ℕ) :
    SingularCochain.cohomology K X k ≃ₗ[K]
      FieldChainKronecker.cohomology ((SingularCochain.chainFunctor K).obj X) k :=
  (((SingularCochain.complex K X).sc k).moduleCatHomologyIso.symm ≪≫
    HomologicalComplex.homologyMapIso (singularDualIso X) k ≪≫
    ((FieldChainKronecker.dualComplex ((SingularCochain.chainFunctor K).obj X)).sc k).moduleCatHomologyIso ).toLinearEquiv



set_option backward.isDefEq.respectTransparency false in
/-- The module-homology comparison sends a literal cocycle class to the class of its actual
component image. This is homology projection naturality, evaluated at the original cocycle. -/
theorem quotient_map_representative
    {ι : Type*} {c : ComplexShape ι}
    {Q Q' : HomologicalComplex (ModuleCat K) c} (F : Q ⟶ Q') (k : ι)
    (a : LinearMap.ker (Q.sc k).g.hom) (b : LinearMap.ker (Q'.sc k).g.hom)
    (hab : (F.f k) a.val = b.val) :
    ((Q.sc k).moduleCatHomologyIso.inv ≫ HomologicalComplex.homologyMap F k ≫
      (Q'.sc k).moduleCatHomologyIso.hom) ((Q.sc k).moduleCatLeftHomologyData.π a) =
        (Q'.sc k).moduleCatLeftHomologyData.π b := by
  let ac := (Q.sc k).moduleCatCyclesIso.inv a
  have hb : (Q'.sc k).moduleCatCyclesIso.hom
      (HomologicalComplex.cyclesMap F k ac) = b := by
    apply Subtype.ext
    change (Q'.sc k).moduleCatLeftHomologyData.i
      ((Q'.sc k).moduleCatCyclesIso.hom (HomologicalComplex.cyclesMap F k ac)) = _
    have hi := congrArg (fun t ↦ t ((HomologicalComplex.cyclesMap F k) ac))
      (Q'.sc k).moduleCatCyclesIso_hom_i
    simp only [ConcreteCategory.comp_apply] at hi
    have hn := congrArg (fun t ↦ t ac) (HomologicalComplex.cyclesMap_i F k)
    simp only [ConcreteCategory.comp_apply] at hn
    have ha := congrArg (fun t ↦ t a) (Q.sc k).moduleCatCyclesIso_inv_iCycles
    simp only [ConcreteCategory.comp_apply] at ha
    exact hi.trans (hn.trans ((congrArg (fun z ↦ (F.f k) z) ha).trans hab))
  have he := congrArg (fun t ↦ t ac) (HomologicalComplex.homologyπ_naturality F k)
  have ha := congrArg (fun t ↦ t a) (Q.sc k).moduleCatCyclesIso_inv_π
  have hbπ := congrArg (fun t ↦ t ((HomologicalComplex.cyclesMap F k) ac))
    (Q'.sc k).π_moduleCatCyclesIso_hom
  change (Q'.sc k).moduleCatHomologyIso.hom
    (HomologicalComplex.homologyMap F k ((Q.sc k).moduleCatHomologyIso.inv
      ((Q.sc k).moduleCatLeftHomologyData.π a))) = _
  simp only [ConcreteCategory.comp_apply] at ha he hbπ
  exact (congrArg (fun z ↦ (Q'.sc k).moduleCatHomologyIso.hom
    (HomologicalComplex.homologyMap F k z)) ha.symm).trans
      ((congrArg (fun z ↦ (Q'.sc k).moduleCatHomologyIso.hom z) he).trans
        (hbπ.trans (congrArg (fun z ↦ (Q'.sc k).moduleCatLeftHomologyData.π z) hb)))


/-- The actual field Kronecker map for the original singular cochain quotient. Its comparison
with the field-chain provider is fixed by the degreewise functionals, not assumed. -/
def singularKronecker (X : TopCat) (k : ℕ) :
    SingularCochain.cohomology K X k ≃ₗ[K]
      Module.Dual K (((SingularCochain.chainFunctor K).obj X).sc k).moduleCatLeftHomologyData.H :=
  (singularFieldCohomologyEquiv X k).trans
    (FieldChainKronecker.evaluationEquiv ((SingularCochain.chainFunctor K).obj X) k)




set_option backward.isDefEq.respectTransparency false in
/-- The singular Kronecker equivalence evaluates every original cocycle/cycle pair literally. -/
theorem singularKronecker_representative (X : TopCat) (k : ℕ)
    (a : SingularCochain.cycles K (SingularCochain.complex K X) k)
    (z : LinearMap.ker (((SingularCochain.chainFunctor K).obj X).sc k).g.hom) :
    singularKronecker X k
        (SingularCochain.cocycleClass K (SingularCochain.complex K X) k a)
        ((((SingularCochain.chainFunctor K).obj X).sc k).moduleCatLeftHomologyData.π z) =
      (show ((SingularCochain.chainFunctor K).obj X).X k ⟶ ModuleCat.of K K from a.val)
        z.val := by
  let b : SingularCochain.cycles K
      (FieldChainKronecker.dualComplex ((SingularCochain.chainFunctor K).obj X)) k :=
    ⟨a.val.hom, FieldChainKronecker.map_cycle_mem (singularDualIso X).hom k a⟩
  have he := quotient_map_representative (singularDualIso X).hom k a b rfl
  change FieldChainKronecker.evaluationEquiv ((SingularCochain.chainFunctor K).obj X) k
    ((SingularCochain.quotientMap K (singularDualIso X).hom k)
      (SingularCochain.cocycleClass K (SingularCochain.complex K X) k a)) _ = _
  have he' : (SingularCochain.quotientMap K (singularDualIso X).hom k)
      (SingularCochain.cocycleClass K (SingularCochain.complex K X) k a) =
        FieldChainKronecker.cycleClass
          (FieldChainKronecker.dualComplex ((SingularCochain.chainFunctor K).obj X)) k b := he
  rw [he']
  exact FieldChainKronecker.evaluation_representative _ k b z



end HolomorphicAnosov.SingularFieldKronecker
