import HolomorphicAnosov.Topology.Homology.SSetPairRestrictScalarsChainIso
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace HolomorphicAnosov.Topology.Homology

/-- Restriction of scalars commutes with relative simplicial homology.
Source: Hatcher, coefficient groups p.153; the chain comparison is the
public relative chain isomorphism and Mathlib's exact-functor homology
comparison. DAG node: `topo.sset_pair_restrict_scalars_homology_iso_g18`. -/
noncomputable def ssetPairRestrictScalarsHomologyIso
    {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (P : SSetPair.{u}) (V : ModuleCat.{u} S) (n : ℕ) :
    (ModuleCat.restrictScalars f).obj (P.homology V n) ≅
      P.homology ((ModuleCat.restrictScalars f).obj V) n := by
  let F := ModuleCat.restrictScalars.{u} f
  let G := F.mapHomologicalComplex (.down ℕ)
  let h := ssetPairRestrictScalarsChainIso f P V
  let S₀ := (P.chainComplex V).sc n
  let hi : (G.obj (P.chainComplex V)).homology n ≅
      (P.chainComplex (F.obj V)).homology n :=
    HomologicalComplex.homologyMapIso h n
  change F.obj ((P.chainComplex V).homology n) ≅
    (P.chainComplex (F.obj V)).homology n
  exact (S₀.mapHomologyIso F).symm ≪≫
    ((HomologicalComplex.homologyFunctorIso (ModuleCat R) (.down ℕ) n).app
      (G.obj (P.chainComplex V))).symm ≪≫ hi

end HolomorphicAnosov.Topology.Homology
