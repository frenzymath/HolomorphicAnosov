import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Complex.Basic

open Set

namespace HolomorphicAnosov

/-- A chart point whose coordinate lies in a preconnected subset of the target containing the
center's coordinate belongs to the center's connected component of the source.
(Zhang, Lemma 2.7, p. 9) -/
theorem partialChart_component_entry
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) {x p : X} (hx : x ∈ e.source)
    (hp : p ∈ e.source) {C : Set Y} (hC : IsPreconnected C)
    (hCT : C ⊆ e.target) (hxC : e x ∈ C) (hpC : e p ∈ C) :
    p ∈ connectedComponentIn e.source x := by
  have hi : IsPreconnected (e.symm '' C) :=
    hC.image _ (e.continuousOn_symm.mono hCT)
  have hxi : x ∈ e.symm '' C := ⟨e x, hxC, e.left_inv hx⟩
  have hsub : e.symm '' C ⊆ e.source := by
    rintro _ ⟨y, hy, rfl⟩
    exact e.map_target (hCT hy)
  exact hi.subset_connectedComponentIn hxi hsub ⟨e p, hpC, e.left_inv hp⟩

set_option backward.isDefEq.respectTransparency false in
/-- Balls of a positive Hermitian form are convex in the underlying real vector space. (Zhang,
Lemmas 2.5 and 2.7, pp. 8–9) -/
theorem hermitian_core_ball_convex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (h : InnerProductSpace.Core ℂ E) (r : ℝ) :
    Convex ℝ {v : E | Real.sqrt (h.inner v v).re < r} := by
  let : Module ℂ E := inferInstance
  let : InnerProductSpace.Core ℂ E := h
  let : NormedAddCommGroup E := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  let : NormedSpace ℂ E := InnerProductSpace.Core.toNormedSpace (𝕜 := ℂ)
  simpa only [Metric.ball, dist_zero_right] using! (convex_ball (0 : E) r)

/-- A point whose chart coordinate lies in a Hermitian ball in a tangent submodule belongs to the
center's connected component of the chart source. -/
theorem partialChart_hermitian_component_entry
    {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℂ E]
    (S : Submodule ℂ E) (h : InnerProductSpace.Core ℂ E)
    (e : OpenPartialHomeomorph X S) {x p : X}
    (hx : x ∈ e.source) (hp : p ∈ e.source) (he : e x = 0)
    {r : ℝ} (hr : 0 < r)
    (hball : ∀ v : S, Real.sqrt (h.inner v.val v.val).re < r → v ∈ e.target)
    (hpball : Real.sqrt (h.inner (e p).val (e p).val).re < r) :
    p ∈ connectedComponentIn e.source x := by
  have hconvex : Convex ℝ {v : S | Real.sqrt (h.inner v.val v.val).re < r} :=
    (hermitian_core_ball_convex h r).linear_preimage (S.subtype.restrictScalars ℝ)
  apply partialChart_component_entry e hx hp hconvex.isPreconnected hball _ hpball
  rw [he]
  simpa only [Set.mem_ofPred_eq, Submodule.coe_zero, InnerProductSpace.Core.inner_zero_left,
    Complex.zero_re, Real.sqrt_zero] using hr

end HolomorphicAnosov
