import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

open CategoryTheory
universe u v
namespace HolomorphicAnosov.Topology

/-- Every native module homology element is the class of a concrete cycle.
Source: Hatcher, Algebraic Topology, pp.108–109, homology as cycles modulo
boundaries. Surjectivity of the native homology projection gives a native cycle;
apply the concrete cycles isomorphism and then its inverse identity. -/
theorem moduleCat_homology_cycle_representative {R : Type u} [Ring R]
    (S : ShortComplex (ModuleCat.{v} R)) (z : S.homology) :
    ∃ a : LinearMap.ker S.g.hom,
      S.homologyπ (S.moduleCatCyclesIso.inv a) = z := by
  obtain ⟨a, ha⟩ := (ModuleCat.epi_iff_surjective S.homologyπ).1 inferInstance z
  refine ⟨S.moduleCatCyclesIso.hom a, ?_⟩
  have hi := congrArg (fun f ↦ f a) S.moduleCatCyclesIso.hom_inv_id
  change S.moduleCatCyclesIso.inv (S.moduleCatCyclesIso.hom a) = a at hi
  exact (congrArg S.homologyπ hi).trans ha
end HolomorphicAnosov.Topology
