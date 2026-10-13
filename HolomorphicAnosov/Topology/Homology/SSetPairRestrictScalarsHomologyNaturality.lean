import HolomorphicAnosov.Topology.Homology.SSetPairRestrictScalarsHomologyIso
import HolomorphicAnosov.Topology.Homology.SSetPairRestrictScalarsChainNaturality
open CategoryTheory CategoryTheory.Limits
open HolomorphicAnosov.Topology.Homology
universe u
noncomputable section
namespace HolomorphicAnosov.Topology.Homology

/-- Restriction of scalars commutes naturally with relative simplicial homology in the pair.
Source: Hatcher, Algebraic Topology, relative quotient chains p.115 and coefficient groups p.153.
Apply homology to the public natural chain comparison. The exact-functor homology comparison
and the natural identification of complex homology with short-complex homology provide the other
commutative squares; composing them proves the equation.
DAG node: `topo.sset_pair_restrict_scalars_homology_naturality_g18`. -/
theorem ssetPairRestrictScalarsHomologyIso_naturality {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) {P Q : SSetPair.{u}} (g : P ⟶ Q) (V : ModuleCat.{u} S) (n : ℕ)
    :
    (ModuleCat.restrictScalars f).map (SSetPair.homologyMap g V n) ≫
        (ssetPairRestrictScalarsHomologyIso f Q V n).hom =
      (ssetPairRestrictScalarsHomologyIso f P V n).hom ≫
        SSetPair.homologyMap g ((ModuleCat.restrictScalars f).obj V) n := by
  have hnat := ssetPairRestrictScalarsChainIso_naturality f g V
  let F := ModuleCat.restrictScalars.{u} f
  let G := F.mapHomologicalComplex (.down ℕ)
  let φ := SSetPair.chainComplexMap g V
  let ψ := SSetPair.chainComplexMap g (F.obj V)
  let eP := ssetPairRestrictScalarsChainIso f P V
  let eQ := ssetPairRestrictScalarsChainIso f Q V
  let t := HomologicalComplex.homologyFunctorIso (ModuleCat.{u} R) (.down ℕ) n
  change F.map (HomologicalComplex.homologyMap φ n) ≫
      (ssetPairRestrictScalarsHomologyIso f Q V n).hom =
    (ssetPairRestrictScalarsHomologyIso f P V n).hom ≫
      HomologicalComplex.homologyMap ψ n
  have ha := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} S) (.down ℕ) n).map φ) F
  have hb := t.inv.naturality (G.map φ)
  have hc := congrArg (fun k ↦ HomologicalComplex.homologyMap k n) hnat
  simp only [HomologicalComplex.homologyMap_comp] at hc
  change G.map φ ≫ eQ.hom = eP.hom ≫ ψ at hnat
  have hc' : HomologicalComplex.homologyMap (G.map φ) n ≫
      HomologicalComplex.homologyMap eQ.hom n =
      HomologicalComplex.homologyMap eP.hom n ≫ HomologicalComplex.homologyMap ψ n := by
    simpa only [← HomologicalComplex.homologyMap_comp] using hc
  change F.map (HomologicalComplex.homologyMap φ n) ≫
      (((Q.chainComplex V).sc n).mapHomologyIso F).inv ≫
      (t.app (G.obj (Q.chainComplex V))).inv ≫
      HomologicalComplex.homologyMap eQ.hom n =
    (((P.chainComplex V).sc n).mapHomologyIso F).inv ≫
      (t.app (G.obj (P.chainComplex V))).inv ≫
      HomologicalComplex.homologyMap eP.hom n ≫ HomologicalComplex.homologyMap ψ n
  have ha' : F.map (HomologicalComplex.homologyMap φ n) ≫
      (((Q.chainComplex V).sc n).mapHomologyIso F).inv =
    (((P.chainComplex V).sc n).mapHomologyIso F).inv ≫
      ShortComplex.homologyMap
        (F.mapShortComplex.map
          ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} S) (.down ℕ) n).map φ)) := ha
  erw [← Category.assoc, ha']
  have hb' : ShortComplex.homologyMap
      (F.mapShortComplex.map
        ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} S) (.down ℕ) n).map φ)) ≫
      (t.app (G.obj (Q.chainComplex V))).inv =
      (t.app (G.obj (P.chainComplex V))).inv ≫
        HomologicalComplex.homologyMap (G.map φ) n := hb
  erw [Category.assoc]
  erw [← Category.assoc (ShortComplex.homologyMap _), hb']
  erw [Category.assoc, Category.assoc, hc']
  rfl

end HolomorphicAnosov.Topology.Homology
