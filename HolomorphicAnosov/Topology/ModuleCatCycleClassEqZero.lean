import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

open CategoryTheory
universe u v
namespace HolomorphicAnosov.Topology

/-- A native cycle class vanishes exactly when the cycle is a boundary.
Source: Hatcher, Algebraic Topology, pp.108–109. Include homology into opcycles;
the cycle-class image is the cokernel projection of the original cycle.
Injectivity of this inclusion and the cokernel zero criterion give the result. -/
theorem moduleCat_cycleClass_eq_zero_iff {R : Type u} [Ring R]
    (S : ShortComplex (ModuleCat.{v} R)) (a : LinearMap.ker S.g.hom) :
    S.homologyπ (S.moduleCatCyclesIso.inv a) = 0 ↔
      ∃ c : S.X₁, S.f c = a.val := by
  have hi := congrArg (fun f ↦ f a) S.moduleCatCyclesIso_inv_iCycles
  change S.iCycles (S.moduleCatCyclesIso.inv a) = a.val at hi
  have hp := congrArg (fun f ↦ f (S.moduleCatCyclesIso.inv a)) S.homology_π_ι
  simp only [ModuleCat.comp_apply] at hp
  rw [hi] at hp
  constructor
  · intro h
    apply (S.moduleCat_pOpcycles_eq_zero_iff _).1
    rw [← hp, h, map_zero]
  · intro h
    apply (ModuleCat.mono_iff_injective S.homologyι).1 inferInstance
    rw [hp, map_zero]
    exact (S.moduleCat_pOpcycles_eq_zero_iff _).2 h
end HolomorphicAnosov.Topology
