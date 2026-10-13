import HolomorphicAnosov.Geometry.Manifold.OrientedRealTopForm
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
A compact oriented smooth manifold has a finite cover by charts of its oriented atlas and a
subordinate smooth partition of unity. (Demailly, I §1.C, p. 11)
-/

open scoped Manifold ContDiff

namespace HolomorphicAnosov.VolumePrototype

/-- Every compact Hausdorff oriented smooth manifold has a finite cover by charts of its supplied
oriented atlas and a smooth partition of unity whose closed supports lie in the chart sources.
(Demailly, I §1.C, p. 11) -/
theorem finiteVolumePresentation_exists
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (CoordinateSpace n) M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]
    (o : OrientedAtlas (n := n) (M := M)) :
    ∃ k : ℕ, ∃ charts : Fin k → OpenPartialHomeomorph M (CoordinateSpace n),
      (∀ i, charts i ∈ o.charts) ∧
      (∀ x : M, ∃ i : Fin k, x ∈ (charts i).source) ∧
      ∃ χ : SmoothPartitionOfUnity (Fin k) 𝓘(ℝ, CoordinateSpace n) M,
        χ.IsSubordinate (fun i ↦ (charts i).source) := by
  classical
  let U : o.charts → Set M := fun e ↦ e.1.source
  have ho : ∀ e : o.charts, IsOpen (U e) := fun e ↦ e.1.open_source
  have hcover : Set.univ ⊆ ⋃ e : o.charts, U e := by
    intro x _
    obtain ⟨e, he, hx⟩ := o.covers x
    exact Set.mem_iUnion.mpr ⟨⟨e, he⟩, hx⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U ho hcover
  let index := (Fintype.equivFin s).symm
  let charts : Fin (Fintype.card s) → OpenPartialHomeomorph M (CoordinateSpace n) :=
    fun i ↦ (index i).1.1
  have hcharts : ∀ i, charts i ∈ o.charts := fun i ↦ (index i).1.2
  have hc : ∀ x : M, ∃ i, x ∈ (charts i).source := by
    intro x
    obtain ⟨e, he, hx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    refine ⟨(Fintype.equivFin s) ⟨e, he⟩, ?_⟩
    simpa only [charts, index, Equiv.symm_apply_apply] using hx
  obtain ⟨χ, hχ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    𝓘(ℝ, CoordinateSpace n) isClosed_univ (fun i ↦ (charts i).source)
    (fun i ↦ (charts i).open_source) (fun x _ ↦ Set.mem_iUnion.mpr (hc x))
  exact ⟨Fintype.card s, charts, hcharts, hc, χ, hχ⟩


end HolomorphicAnosov.VolumePrototype
