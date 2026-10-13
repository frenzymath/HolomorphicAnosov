import HolomorphicAnosov.Topology.CWComplex.NativeDiskIntervalHomeomorph
import Mathlib.Topology.CWComplex.Classical.Basic

/-!
# Closed-disk characteristic maps for interval prisms

Source: Fritsch–Piccinini, *Cellular Structures in Topology*, Theorem 2.2.2,
p.58: product characteristic maps have the products of the original closed
cells as their images. The native coordinate parametrization is supplied by
`native_disk_interval_homeomorph`; no regularity of the original cell is used.
-/

open Set _root_.Topology
namespace HolomorphicAnosov.Topology

/-- The product of an original characteristic map with the interval identity,
parametrized on the native next-dimensional closed disk.

Source: Fritsch–Piccinini, Theorem 2.2.2(ii) and its product attaching-map proof,
p.58. Proof: use the native disk–interval homeomorphism and compose its first
projection with the original characteristic map. Both components are continuous.
The homeomorphism is onto, and the original closed cell is precisely the image
of its closed disk, so the image is the product closed cell. The coordinate
identities are those of the native disk homeomorphism. This includes d=0 and
noninjective characteristic maps on the boundary.
-/
theorem prism_closed_disk_characteristic
    {X : Type*} [TopologicalSpace X] [CWComplex (univ : Set X)]
    (d : ℕ) (i : RelCWComplex.cell (univ : Set X) d) :
    ∃ f : ↥(Metric.closedBall (0 : Fin (d + 1) → ℝ) 1) → X × unitInterval,
      Continuous f ∧
      range f = (CWComplex.closedCell (C := univ) d i).prod univ ∧
      (∀ w, (f w).1 = RelCWComplex.map (C := univ) d i
        (fun j ↦ w.1 j.castSucc)) ∧
      (∀ w, ((f w).2 : ℝ) = (w.1 (Fin.last d) + 1) / 2) := by
  obtain ⟨e, hhead, htime, _⟩ := native_disk_interval_homeomorph d
  let f : ↥(Metric.closedBall (0 : Fin (d + 1) → ℝ) 1) → X × unitInterval :=
    fun w ↦ (RelCWComplex.map (C := univ) d i (e w).1.1, (e w).2)
  refine ⟨f, ?_, ?_, ?_, htime⟩
  · exact ((RelCWComplex.continuousOn d i).domRestrict.comp
      (continuous_fst.comp e.continuous)).prodMk (continuous_snd.comp e.continuous)
  · ext xt
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨⟨(e w).1.1, (e w).1.2, rfl⟩, mem_univ _⟩
    · rintro ⟨⟨z, hz, hzx⟩, _⟩
      refine ⟨e.symm (⟨z, hz⟩, xt.2), ?_⟩
      simp only [f, e.apply_symm_apply]
      exact Prod.ext hzx rfl
  · intro w
    exact congrArg (RelCWComplex.map (C := univ) d i) (funext (hhead w))

end HolomorphicAnosov.Topology

