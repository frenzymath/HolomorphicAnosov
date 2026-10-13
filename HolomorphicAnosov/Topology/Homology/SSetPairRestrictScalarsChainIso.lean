import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.MapHomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Homology.HomologicalComplexLimits

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace HolomorphicAnosov.Topology.Homology

/-- Restriction of scalars commutes with relative simplicial chain complexes.
Source: Hatcher, Algebraic Topology, relative quotient chains p.115 and
coefficient groups p.153. The absolute comparison identifies the two maps
whose cokernels define the relative complexes; restriction of scalars preserves
these cokernels, so their universal properties give the displayed isomorphism.
DAG node: `topo.sset_pair_restrict_scalars_chain_iso_g18`. -/
def ssetPairRestrictScalarsChainIso {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (P : SSetPair.{u}) (V : ModuleCat.{u} S) :
    ((ModuleCat.restrictScalars f).mapHomologicalComplex (.down ℕ)).obj
        (P.chainComplex V) ≅
      P.chainComplex ((ModuleCat.restrictScalars f).obj V) := by
  let F := ModuleCat.restrictScalars.{u} f
  let G := F.mapHomologicalComplex (.down ℕ)
  let e := SSet.chainComplexFunctorObjCompMapIso F V
  exact CokernelCofork.mapIsoOfIsColimit
    (CokernelCofork.mapIsColimit _ (P.isColimitCokernelCoforkChainComplex V) G)
    (P.isColimitCokernelCoforkChainComplex (F.obj V))
    (Arrow.isoMk (e.app P.left) (e.app P.right) (e.hom.naturality P.hom).symm)
end HolomorphicAnosov.Topology.Homology
