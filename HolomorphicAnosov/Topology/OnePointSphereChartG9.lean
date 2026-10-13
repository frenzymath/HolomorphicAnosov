import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# A sphere chart sending a prescribed point to infinity

This file constructs a self-homeomorphism of the one-point compactification sending any chosen point to infinity. (Conway, Lemma 2.2)
-/

open Set
open scoped Topology _root_.Topology

namespace HolomorphicAnosov

/-- Every point of the native one-point compactification admits a self-homeomorphism sending it to infinity. (Conway, Lemma 2.2) -/
theorem onePoint_homeomorph_send_to_infty (p : OnePoint ℂ) :
    ∃ e : OnePoint ℂ ≃ₜ OnePoint ℂ, e p = OnePoint.infty := by
  let S := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
  let e : OnePoint ℂ ≃ₜ S := onePointEquivSphereOfFinrankEq (by simp)
  let v : EuclideanSpace ℝ (Fin 3) := e p
  have hv : ‖v‖ = 1 := by simp [v]
  have hv0 : v ≠ 0 := by intro h; simp [h] at hv
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  have hd : Module.finrank ℝ ℂ = Module.finrank ℝ (ℝ ∙ v)ᗮ := by
    rw [Submodule.finrank_orthogonal_span_singleton (𝕜 := ℝ) (n := 2) hv0]
    simp
  let f : ℂ ≃ₜ (ℝ ∙ v)ᗮ :=
    (FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq hd).some.toHomeomorph
  let q : OnePoint ℂ ≃ₜ S := f.onePointCongr.trans (onePointHyperplaneHomeoUnitSphere hv)
  have hq : q OnePoint.infty = e p := by
    apply Subtype.ext
    rfl
  refine ⟨e.trans q.symm, ?_⟩
  change q.symm (e p) = OnePoint.infty
  rw [← hq, q.symm_apply_apply]

end HolomorphicAnosov
