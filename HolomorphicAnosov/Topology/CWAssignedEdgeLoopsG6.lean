import HolomorphicAnosov.Topology.BasedHomotopyUniqueness
import HolomorphicAnosov.Topology.CWComplex.OneCellLoopDiskRealization
import HolomorphicAnosov.Topology.RootedEdgeLoopCollapse

namespace HolomorphicAnosov
universe u v

/-- Prescribed based loops glue to a continuous map on an original one-dimensional CW carrier.
Source: Hatcher, Algebraic Topology, Proposition 1B.9 pp.90–91. Apply the native one-disk
adapter to every assigned loop, send every vertex to the common basepoint, and use weak-CW
characteristic-prism gluing with constant time coordinate. Its compatibility condition is exactly
the common boundary value; no regularity or local finiteness of the CW structure is required. -/
theorem cw_assigned_edge_loops_g6
    {K : Type u} {Y : Type v} [TopologicalSpace K] [TopologicalSpace Y] [T2Space K]
    (C : Set K) [Topology.CWComplex C]
    (hhigh : ∀ n, IsEmpty (Topology.RelCWComplex.cell C (n + 2))) (y₀ : Y)
    (ell : Topology.RelCWComplex.cell C 1 → Path y₀ y₀)
    (rev : Topology.RelCWComplex.cell C 1 → Bool) :
    ∃ f : C(C, Y),
      (∀ v : Topology.RelCWComplex.cell C 0,
        f ⟨Topology.RelCWComplex.map 0 v 0,
          Topology.RelCWComplex.closedCell_subset_complex 0 v ⟨0, by simp, rfl⟩⟩ = y₀) ∧
      (∀ e (t : unitInterval) (z : Metric.closedBall (0 : Fin 1 → ℝ) 1),
        z.val 0 = (if rev e then 1 - 2 * (t : ℝ) else 2 * (t : ℝ) - 1) →
        f ⟨Topology.RelCWComplex.map 1 e z.val,
          Topology.RelCWComplex.closedCell_subset_complex 1 e ⟨z.val, z.property, rfl⟩⟩ =
            ell e t) := by
  classical
  have hdisks := fun e ↦ cw_one_cell_loop_disk_realization (ell e) (rev e)
  choose b hb hboundary using hdisks
  let Cv : Topology.RelCWComplex.cell C 0 → C(unitInterval, Y) :=
    fun _ ↦ ContinuousMap.const unitInterval y₀
  let Pe : Topology.RelCWComplex.cell C 1 →
      C(unitInterval × Metric.closedBall (0 : Fin 1 → ℝ) 1, Y) :=
    fun e ↦ (b e).comp ContinuousMap.snd
  obtain ⟨H, hHv, hHe⟩ := cw_one_dimensional_glue_edge_tracks C hhigh Cv Pe
    (fun e z _ _ hz _ ↦ hboundary e z hz)
  let f : C(C, Y) := H.comp ((ContinuousMap.const C (0 : unitInterval)).prodMk
    (ContinuousMap.id C))
  refine ⟨f, ?_, ?_⟩
  · intro v
    exact hHv v 0
  · intro e t z hz
    change H (0, ⟨Topology.RelCWComplex.map 1 e z.val,
      Topology.RelCWComplex.closedCell_subset_complex 1 e ⟨z.val, z.property, rfl⟩⟩) = ell e t
    rw [hHe]
    exact hb e t z hz

end HolomorphicAnosov
