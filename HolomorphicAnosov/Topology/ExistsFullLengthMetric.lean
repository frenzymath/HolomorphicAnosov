import Mathlib.Topology.MetricSpace.Gluing

namespace HolomorphicAnosov

open Set

/-- Every extended metric has a compatible finite metric preserving all finite
extended distances. Split into finite-distance equivalence classes, metrize each
class by its original distance, use Mathlib's Sigma metric, and pull it back
through the native fibre equivalence. -/
theorem exists_full_length_metric (X : Type*) [em : EMetricSpace X] :
    ∃ d : MetricSpace X,
      d.toUniformSpace.toTopologicalSpace = em.toUniformSpace.toTopologicalSpace ∧
      ∀ x y : X, em.edist x y < ⊤ → ENNReal.ofReal (d.dist x y) = em.edist x y := by
  classical
  let s : Setoid X := Metric.edistLtTopSetoid
  let q : X → Quotient s := Quotient.mk s
  let F : Quotient s → Type _ := fun c ↦ {x : X // q x = c}
  have hFopen (c : Quotient s) : IsOpen {x : X | q x = c} := by
    obtain ⟨z, rfl⟩ := Quotient.exists_rep c
    have heq : {x : X | q x = Quotient.mk s z} = Metric.eball z ⊤ := by
      ext x
      simp only [Set.mem_ofPred_eq, Metric.mem_eball]
      apply (Quotient.eq (r := s)).trans
      exact Iff.rfl
    rw [heq]
    exact Metric.isOpen_eball
  let fiberMetric : ∀ c : Quotient s, MetricSpace (F c) := fun c ↦
    EMetricSpace.toMetricSpace (fun x y ↦ ne_of_lt
      (show edist x y < ⊤ from Quotient.exact (x.property.trans y.property.symm)))
  let : ∀ c : Quotient s, MetricSpace (F c) := fiberMetric
  let : MetricSpace (Σ c, F c) := Metric.Sigma.metricSpace
  let e : (Σ c, F c) ≃ X := Equiv.sigmaFiberEquiv q
  let h : (Σ c, F c) ≃ₜ X := e.toHomeomorphOfContinuousOpen
    (continuous_sigma fun _ ↦ continuous_subtype_val)
    (isOpenMap_sigma.mpr fun c ↦ (hFopen c).isOpenMap_subtype_val)
  let d : MetricSpace X := h.symm.isEmbedding.comapMetricSpace h.symm
  refine ⟨d, rfl, ?_⟩
  intro x y hxy
  have hq : q x = q y := Quotient.sound hxy
  let xx : F (q x) := ⟨x, rfl⟩
  let yy : F (q x) := ⟨y, hq.symm⟩
  have hy : h.symm y = Sigma.mk (q x) yy := by
    apply h.injective
    rfl
  change ENNReal.ofReal (dist (h.symm x) (h.symm y)) = edist x y
  rw [hy]
  change ENNReal.ofReal (dist (Sigma.mk (q x) xx) (Sigma.mk (q x) yy)) = edist x y
  rw [Metric.Sigma.dist_same]
  exact ENNReal.ofReal_toReal hxy.ne

end HolomorphicAnosov
