import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.UnitInterval

open Set _root_.Topology
namespace HolomorphicAnosov.Topology

/-- The endpoint product map is a CW partial equivalence, with the exact restricted
continuity interfaces supplied by `RelCWComplex`. This is the endpoint slice used
in the interval-product open-cell construction. -/
theorem endpoint_partial_equiv_data {X : Type*} [TopologicalSpace X] [CWComplex (univ : Set X)]
    (d : ℕ) (i : RelCWComplex.cell (univ : Set X) d) (a : Bool) :
    ∃ e : PartialEquiv (Fin d → ℝ) (X × unitInterval),
      e.source = Metric.ball 0 1 ∧
      e.target = (RelCWComplex.map (C := univ) d i '' Metric.ball 0 1) ×ˢ {if a then 1 else 0} ∧
      (∀ z, e z = (RelCWComplex.map (C := univ) d i z, if a then 1 else 0)) ∧
      ContinuousOn e (Metric.closedBall 0 1) ∧ ContinuousOn e.symm e.target := by
  let t : unitInterval := if a then 1 else 0
  let m := RelCWComplex.map (C := univ) d i
  let e : PartialEquiv (Fin d → ℝ) (X × unitInterval) := {
    toFun := fun z ↦ (m z, t)
    invFun := fun y ↦ m.symm y.1
    source := Metric.ball 0 1
    target := (m '' Metric.ball 0 1) ×ˢ {t}
    map_source' := by
      intro z hz
      have hzt : z ∈ m.source := by
        rw [RelCWComplex.source_eq]
        exact hz
      exact ⟨⟨z, hz, rfl⟩, mem_singleton t⟩
    map_target' := by
      rintro y ⟨⟨z, hz, hzy⟩, hs⟩
      have hzt : z ∈ m.source := by
        rw [RelCWComplex.source_eq]
        exact hz
      have hmt : y.1 ∈ m.target := by
        rw [← hzy]
        exact m.map_source hzt
      have hm := m.map_target hmt
      rw [RelCWComplex.source_eq] at hm
      exact hm
    left_inv' := by
      intro z hz
      have hzt : z ∈ m.source := by
        rw [RelCWComplex.source_eq]
        exact hz
      exact m.left_inv hzt
    right_inv' := by
      rintro y ⟨⟨z, hz, hzy⟩, hs⟩
      have hzt : z ∈ m.source := by
        rw [RelCWComplex.source_eq]
        exact hz
      have hmt : y.1 ∈ m.target := by
        rw [← hzy]
        exact m.map_source hzt
      have hsecond : t = y.2 := Eq.symm (mem_singleton_iff.mp hs)
      exact Prod.ext (m.right_inv hmt) hsecond }
  refine ⟨e, rfl, rfl, ?_, ?_, ?_⟩
  · intro z
    rfl
  · change ContinuousOn (fun z ↦ (m z, t)) (Metric.closedBall 0 1)
    exact (RelCWComplex.continuousOn d i).prodMk continuousOn_const
  · change ContinuousOn (fun y ↦ m.symm y.1) e.target
    have hmaps : Set.MapsTo Prod.fst e.target m.target := by
      intro y hy
      rcases hy with ⟨⟨z, hz, hzy⟩, hs⟩
      have hzt : z ∈ m.source := by
        rw [RelCWComplex.source_eq]
        exact hz
      rw [← hzy]
      exact m.map_source hzt
    have hc := (RelCWComplex.continuousOn_symm d i).comp continuousOn_fst hmaps
    simpa [e, Function.comp_def] using hc

end HolomorphicAnosov.Topology
