import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

open CategoryTheory
universe u v
namespace HolomorphicAnosov.Topology

/-- A short-complex map sends the native class of a cycle to the class of its
middle-component image.
Source: Hatcher, Algebraic Topology, p.111, induced homology map; Mathlib's cycle
and homology projection naturality. Apply injectivity of the target cycle
inclusion to identify the mapped cycle, then use naturality of homology projection. -/
theorem moduleCat_cycleClass_naturality {R : Type u} [Ring R]
    {S T : ShortComplex (ModuleCat.{v} R)} (f : S ⟶ T)
    (a : LinearMap.ker S.g.hom) (b : LinearMap.ker T.g.hom)
    (hb : f.τ₂ a.val = b.val) :
    ShortComplex.homologyMap f (S.homologyπ (S.moduleCatCyclesIso.inv a)) =
      T.homologyπ (T.moduleCatCyclesIso.inv b) := by
  have hiS := congrArg (fun k ↦ k a) S.moduleCatCyclesIso_inv_iCycles
  have hiT := congrArg (fun k ↦ k b) T.moduleCatCyclesIso_inv_iCycles
  change S.iCycles (S.moduleCatCyclesIso.inv a) = a.val at hiS
  change T.iCycles (T.moduleCatCyclesIso.inv b) = b.val at hiT
  have hc : ShortComplex.cyclesMap f (S.moduleCatCyclesIso.inv a) =
      T.moduleCatCyclesIso.inv b := by
    apply (ModuleCat.mono_iff_injective T.iCycles).1 inferInstance
    have hn := congrArg (fun k ↦ k (S.moduleCatCyclesIso.inv a))
      (ShortComplex.cyclesMap_i f)
    change T.iCycles (ShortComplex.cyclesMap f (S.moduleCatCyclesIso.inv a)) =
      f.τ₂ (S.iCycles (S.moduleCatCyclesIso.inv a)) at hn
    exact hn.trans ((congrArg f.τ₂ hiS).trans (hb.trans hiT.symm))
  have hn := congrArg (fun k ↦ k (S.moduleCatCyclesIso.inv a))
    (ShortComplex.homologyπ_naturality f)
  change ShortComplex.homologyMap f (S.homologyπ (S.moduleCatCyclesIso.inv a)) =
    T.homologyπ (ShortComplex.cyclesMap f (S.moduleCatCyclesIso.inv a)) at hn
  exact hn.trans (congrArg T.homologyπ hc)

end HolomorphicAnosov.Topology
