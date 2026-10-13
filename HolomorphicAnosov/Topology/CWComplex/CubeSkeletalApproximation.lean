import HolomorphicAnosov.Topology.AttachedCellPolyhedralData
import HolomorphicAnosov.Topology.CWComplex.SubcomplexSkeleton
import Mathlib.Topology.CWComplex.Classical.Basic
import HolomorphicAnosov.Topology.CWComplex.FiniteCubeSkeletalApproximation
import HolomorphicAnosov.Topology.CompactCWFiniteSubcomplex

namespace HolomorphicAnosov

open HatcherAttachedCell

/-- A cube map into an arbitrary Hausdorff CW complex can be deformed into
its dimension skeleton, relative to any source subset already mapping there.
Source: Hatcher Theorem 4.8, p.349, compact characteristic-image reduction.
The cube is compact, so its continuous image lies in a finite subcomplex.
The fixed-subset image belongs to that subcomplex's skeleton by the skeleton
intersection identity. Apply finite-target approximation there, and use the
same identity to include the endpoint in the ambient skeleton. -/
theorem cw_cube_skeletal_approximation
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set Y)]
    (n : ℕ) (A : Set (Cube n)) (f : C(Cube n, Y))
    (hA : Set.MapsTo f A
      (Topology.CWComplex.skeleton (Set.univ : Set Y) (n : ℕ∞) : Set Y)) :
    ∃ g : C(Cube n, Y),
      Set.range g ⊆
        (Topology.CWComplex.skeleton (Set.univ : Set Y) (n : ℕ∞) : Set Y) ∧
      Nonempty (ContinuousMap.HomotopyRel f g A) := by
  obtain ⟨W, hfinite, hW⟩ :=
    (Topology.compact_cw_subset_finite_subcomplex (Set.range f)
      (isCompact_range f.continuous)).2.1
  let := hfinite
  have hWA : Set.MapsTo f A
      (Topology.CWComplex.skeleton (W : Set Y) (n : ℕ∞) : Set Y) := by
    intro x hx
    rw [cw_subcomplex_skeleton]
    exact ⟨hW ⟨x, rfl⟩, hA hx⟩
  obtain ⟨g, hg, H⟩ := finite_cw_cube_skeletal_approximation (W : Set Y) n A f hW hWA
  refine ⟨g, ?_, H⟩
  rw [cw_subcomplex_skeleton] at hg
  exact fun x hx ↦ (hg hx).2

end HolomorphicAnosov
