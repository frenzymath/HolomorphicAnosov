import HolomorphicAnosov.Topology.Homology.SSetPairRestrictScalarsChainIso

open CategoryTheory CategoryTheory.Limits
open HolomorphicAnosov.Topology.Homology
universe u
noncomputable section
namespace HolomorphicAnosov.Topology.Homology
/-- Naturality of the relative chain restriction-of-scalars comparison in the pair variable.
Source: Hatcher, Algebraic Topology, relative quotient chains p.115 and coefficient groups p.153;
the proof is the naturality of the absolute coefficient comparison followed by the cokernel
universal property from Mathlib's `Relative` API. DAG node: `topo.sset_pair_restrict_scalars_chain_naturality_g18`. -/
theorem ssetPairRestrictScalarsChainIso_naturality {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) {P Q : SSetPair.{u}} (g : P ⟶ Q) (V : ModuleCat.{u} S) :
    ((ModuleCat.restrictScalars f).mapHomologicalComplex (.down ℕ)).map (P.chainComplexMap g V) ≫
      (ssetPairRestrictScalarsChainIso f Q V).hom =
    (ssetPairRestrictScalarsChainIso f P V).hom ≫
      P.chainComplexMap g ((ModuleCat.restrictScalars f).obj V) := by
  let F := ModuleCat.restrictScalars.{u} f
  let G := F.mapHomologicalComplex (.down ℕ)
  let e := SSet.chainComplexFunctorObjCompMapIso F V
  apply Cofork.IsColimit.hom_ext
    (CokernelCofork.mapIsColimit _ (P.isColimitCokernelCoforkChainComplex V) G)
  change G.map (P.chainComplexπ V) ≫ G.map (SSetPair.chainComplexMap g V) ≫ _ =
    G.map (P.chainComplexπ V) ≫ _ ≫ _
  have hp := ((SSetPair.chainComplexFunctorπ (ModuleCat.{u} S)).app V).naturality g
  change SSet.chainComplexMap g.hom.right V ≫ Q.chainComplexπ V =
    P.chainComplexπ V ≫ SSetPair.chainComplexMap g V at hp
  rw [← Category.assoc, ← G.map_comp, ← hp, G.map_comp, Category.assoc]
  have hQ := CokernelCofork.π_mapOfIsColimit
    ((Q.cokernelCoforkChainComplex V).mapIsColimit
      (Q.isColimitCokernelCoforkChainComplex V) G)
    (Q.cokernelCoforkChainComplex (F.obj V))
    (Arrow.isoMk (e.app Q.left) (e.app Q.right)
      (e.hom.naturality Q.hom).symm).hom
  have hP := CokernelCofork.π_mapOfIsColimit
    ((P.cokernelCoforkChainComplex V).mapIsColimit
      (P.isColimitCokernelCoforkChainComplex V) G)
    (P.cokernelCoforkChainComplex (F.obj V))
    (Arrow.isoMk (e.app P.left) (e.app P.right)
      (e.hom.naturality P.hom).symm).hom
  have hQ' : G.map (Q.chainComplexπ V) ≫
      (ssetPairRestrictScalarsChainIso f Q V).hom =
      (e.app Q.right).hom ≫ Q.chainComplexπ (F.obj V) := by
    dsimp [ssetPairRestrictScalarsChainIso]
    change G.map (Cofork.π (Q.cokernelCoforkChainComplex V)) ≫ _ = _
    rw [← CokernelCofork.map_π]
    exact hQ
  have hP' : G.map (P.chainComplexπ V) ≫
      (ssetPairRestrictScalarsChainIso f P V).hom =
      (e.app P.right).hom ≫ P.chainComplexπ (F.obj V) := by
    dsimp [ssetPairRestrictScalarsChainIso]
    change G.map (Cofork.π (P.cokernelCoforkChainComplex V)) ≫ _ = _
    rw [← CokernelCofork.map_π]
    exact hP
  rw [hQ']
  rw [← Category.assoc (G.map (P.chainComplexπ V)), hP']
  simp only [Category.assoc]
  change G.map (SSet.chainComplexMap g.hom.right V) ≫ (e.app Q.right).hom ≫
    Q.chainComplexπ (F.obj V) = (e.app P.right).hom ≫
    P.chainComplexπ (F.obj V) ≫ SSetPair.chainComplexMap g (F.obj V)
  have he := e.hom.naturality g.hom.right
  change G.map (SSet.chainComplexMap g.hom.right V) ≫ (e.app Q.right).hom =
    (e.app P.right).hom ≫ SSet.chainComplexMap g.hom.right (F.obj V) at he
  rw [← Category.assoc, he]
  rw [← Category.assoc]
  exact congrArg ((e.app P.right).hom ≫ ·)
    (((SSetPair.chainComplexFunctorπ (ModuleCat.{u} R)).app (F.obj V)).naturality g)
end HolomorphicAnosov.Topology.Homology

