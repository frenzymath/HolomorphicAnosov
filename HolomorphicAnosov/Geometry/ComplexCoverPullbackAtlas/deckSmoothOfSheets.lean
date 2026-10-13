import HolomorphicAnosov.Geometry.ComplexModel
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

namespace HolomorphicAnosov

universe u v

open scoped ContDiff

variable {d : ℕ} {X : Type u} {Y : Type v}
  [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
  [TopologicalSpace Y]

/-- A continuous map preserving a covering projection is smooth when local covering sheets and their inverses are smooth. (Lee, Prop. 1.15, p. 9). -/
theorem deckSmoothOfSheets [ChartedSpace (ComplexModel d) Y]
    (p : Y → X) (hprojection : ContMDiff (complexModel d) (complexModel d) ∞ p)
    (hlocal : ∀ y : Y, ∃ e : OpenPartialHomeomorph Y X,
      y ∈ e.source ∧ Set.EqOn e p e.source ∧
      ContMDiffOn (complexModel d) (complexModel d) ∞ e e.source ∧
        ContMDiffOn (complexModel d) (complexModel d) ∞ e.symm e.target)
    (f : Y → Y) (hf : Continuous f) (hpf : ∀ y, p (f y) = p y) :
    ContMDiff (complexModel d) (complexModel d) ∞ f := by
  intro y
  obtain ⟨e, hey, he, _, hes⟩ := hlocal (f y)
  have hey' : e (f y) = p y := (he hey).trans (hpf y)
  have hs : ContMDiffAt (complexModel d) (complexModel d) ∞ e.symm (p y) := by
    rw [← hey']
    exact hes.contMDiffAt (e.open_target.mem_nhds (e.map_source hey))
  apply (hs.comp y (hprojection y)).congr_of_eventuallyEq
  filter_upwards [hf.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds hey)] with t ht
  change f t = e.symm (p t)
  rw [← hpf t, ← he ht]
  exact (e.left_inv ht).symm


end HolomorphicAnosov
