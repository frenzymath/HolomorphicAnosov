import HolomorphicAnosov.Analysis.Measure.LocalRegularZeroSetNull

open Filter Set MeasureTheory
open scoped Topology _root_.Topology

namespace HolomorphicAnosov

/-- Mityagin, Claim 1, pp. 1–2, extended to a normed target by a separating
continuous linear functional. At a zero whose derivative is nonzero, choose
an input vector with nonzero derivative value and a linear functional nonzero
on that value. The scalar composition has a regular zero, so its local zero
set, and hence the original local zero set, is null. The Lindelöf property of
Euclidean space extracts countably many such null neighborhoods. -/
theorem volume_regular_zero_set_eq_zero {N : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : EuclideanSpace ℝ (Fin N) → F) (U : Set (EuclideanSpace ℝ (Fin N)))
    (hf : ∀ x ∈ U, ContDiffAt ℝ 1 f x) :
    volume {x | x ∈ U ∧ f x = 0 ∧ fderiv ℝ f x ≠ 0} = 0 := by
  let s := {x | x ∈ U ∧ f x = 0 ∧ fderiv ℝ f x ≠ 0}
  change volume s = 0
  rw [← compl_mem_ae_iff]
  apply (HereditarilyLindelofSpace.isLindelof s).compl_mem_sets_of_nhdsWithin
  intro x hx
  have hex : ∃ v, fderiv ℝ f x v ≠ 0 := by
    by_contra! h
    exact hx.2.2 (ContinuousLinearMap.ext h)
  obtain ⟨v, hv⟩ := hex
  obtain ⟨l, hl⟩ := SeparatingDual.exists_ne_zero (R := ℝ) hv
  have hscalar : ContDiffAt ℝ 1 (fun y ↦ l (f y)) x :=
    l.contDiff.contDiffAt.comp x (hf x hx.1)
  have hderiv : fderiv ℝ (fun y ↦ l (f y)) x ≠ 0 := by
    change fderiv ℝ (l ∘ f) x ≠ 0
    rw [(l.hasFDerivAt.comp x ((hf x hx.1).differentiableAt one_ne_zero).hasFDerivAt).fderiv]
    intro hzero
    apply hl
    have heval := congrArg (fun L : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ ↦ L v) hzero
    exact heval
  obtain ⟨V, hV, hnull⟩ := exists_nhds_volume_zero_set_eq_zero hscalar
    (by simp [hx.2.1]) hderiv
  refine ⟨s ∩ V, inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hV), ?_⟩
  rw [compl_mem_ae_iff]
  apply measure_mono_null (t := {y | y ∈ V ∧ l (f y) = 0}) _ hnull
  intro y hy
  exact ⟨hy.2, by simp [hy.1.2.1]⟩

end HolomorphicAnosov
