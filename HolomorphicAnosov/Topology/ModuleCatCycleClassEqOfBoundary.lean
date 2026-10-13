import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

open CategoryTheory
universe u v
namespace HolomorphicAnosov.Topology

/-- Cycles differing by a boundary have the same class in native module homology.
Source: Hatcher, Algebraic Topology, pp.108–109, definition of homology.
Proof: include homology into opcycles, identify both images with the opcycle
projections of the given cycles, then use the quotient equality criterion. -/
theorem moduleCat_cycleClass_eq_of_boundary {R : Type u} [Ring R]
    (S : ShortComplex (ModuleCat.{v} R)) (a b : LinearMap.ker S.g.hom)
    (c : S.X₁) (hc : S.f c = a.val - b.val) :
    S.homologyπ (S.moduleCatCyclesIso.inv a) =
      S.homologyπ (S.moduleCatCyclesIso.inv b) := by
  apply (ModuleCat.mono_iff_injective S.homologyι).1 inferInstance
  have ha := congrArg (fun f ↦ f (S.moduleCatCyclesIso.inv a)) S.homology_π_ι
  have hb := congrArg (fun f ↦ f (S.moduleCatCyclesIso.inv b)) S.homology_π_ι
  simp only [ModuleCat.comp_apply] at ha hb
  rw [ha, hb]
  apply (S.moduleCat_pOpcycles_eq_iff _ _).2
  have hai := congrArg (fun f ↦ f a) S.moduleCatCyclesIso_inv_iCycles
  have hbi := congrArg (fun f ↦ f b) S.moduleCatCyclesIso_inv_iCycles
  change S.iCycles (S.moduleCatCyclesIso.inv a) = a.val at hai
  change S.iCycles (S.moduleCatCyclesIso.inv b) = b.val at hbi
  rw [hai, hbi]
  exact ⟨c, hc⟩

end HolomorphicAnosov.Topology
