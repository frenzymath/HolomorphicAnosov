import Mathlib.Topology.CWComplex.Classical.Basic
import HolomorphicAnosov.Topology.CWComplex.CubeSkeletalApproximation
import HolomorphicAnosov.Topology.CWComplex.EuclideanSupRadialHomeomorph
import HolomorphicAnosov.Topology.EuclideanDiskUnitCube

namespace HolomorphicAnosov

/-- A map from a native sup-norm characteristic disk into a Hausdorff CW
complex can be deformed into the skeleton of the disk dimension, relative
to any source subset already mapping there. Source: Hatcher Theorem 4.8,
pp.349–351, with Bredon I.16, pp.56–57, for disk/cube coordinates.
Compose the norm-preserving radial disk comparison with the Euclidean
closed-disk/cube homeomorphism. Pull the map and its prescribed fixed set
to the cube, apply cube skeletal approximation, then pull the homotopy back.
The inverse identities preserve both endpoints and every fixed point. -/
theorem cw_characteristic_disk_skeletal_approximation
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set Y)]
    (n : ℕ) (A : Set (Metric.closedBall (0 : Fin n → ℝ) 1))
    (f : C(Metric.closedBall (0 : Fin n → ℝ) 1, Y))
    (hA : Set.MapsTo f A
      (Topology.CWComplex.skeleton (Set.univ : Set Y) (n : ℕ∞) : Set Y)) :
    ∃ g : C(Metric.closedBall (0 : Fin n → ℝ) 1, Y),
      Set.range g ⊆
        (Topology.CWComplex.skeleton (Set.univ : Set Y) (n : ℕ∞) : Set Y) ∧
      Nonempty (ContinuousMap.HomotopyRel f g A) := by
  obtain ⟨e, he⟩ := euclidean_sup_radial_homeomorph n
  let ed : HatcherAttachedCell.CellDisk n ≃ₜ Metric.closedBall (0 : Fin n → ℝ) 1 :=
    e.subtype (fun x ↦ by simp only [Metric.mem_closedBall, dist_zero_right, he])
  obtain ⟨ec, _⟩ := euclidean_closed_disk_unit_cube_homeomorphism n
  let c := ed.symm.trans ec
  let q : C(HatcherAttachedCell.Cube n, Y) := f.comp ⟨c.symm, c.symm.continuous⟩
  obtain ⟨r, hr, ⟨H⟩⟩ := cw_cube_skeletal_approximation n (c.symm ⁻¹' A) q
    (fun x hx ↦ hA hx)
  let g : C(Metric.closedBall (0 : Fin n → ℝ) 1, Y) := r.comp ⟨c, c.continuous⟩
  refine ⟨g, fun y hy ↦ ?_, ?_⟩
  · obtain ⟨x, rfl⟩ := hy
    exact hr ⟨c x, rfl⟩
  · refine ⟨{
      toContinuousMap := ⟨fun z ↦ H (z.1, c z.2),
        H.continuous.comp (continuous_fst.prodMk (c.continuous.comp continuous_snd))⟩
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }⟩
    · intro x
      simp [q]
    · intro x
      exact H.map_one_left (c x)
    · intro t x hx
      have hcx : c x ∈ c.symm ⁻¹' A := by simpa using hx
      simpa [q] using H.eq_fst t hcx

end HolomorphicAnosov
