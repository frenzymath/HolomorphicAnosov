import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Analysis.Complex.Basic

/-!
Continuity of finite linear combinations of tangent sections. (Hatcher, Vector Bundles and
K-Theory, §1.1, p.8)
-/

noncomputable section
open Set Bundle Filter Topology _root_.Topology
open scoped ContDiff
namespace HolomorphicAnosov

/-- Finite complex linear combinations of continuous tangent sections along a continuous base map,
with continuous coefficients, are continuous on their common domain. (Hatcher, Vector Bundles
and K-Theory, p.8) -/
theorem continuousOn_tangent_linear_combination
    {E H M X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [TopologicalSpace X] [Fintype ι]
    (p : X → M) (v : ∀ x : X, ι → TangentSpace I (p x))
    (a : X → ι → ℂ) {U : Set X}
    (hp : ContinuousOn p U)
    (hv : ∀ i, ContinuousOn (fun x ↦ (⟨p x, v x i⟩ : TangentBundle I M)) U)
    (ha : ∀ i, ContinuousOn (fun x ↦ a x i) U) :
    ContinuousOn (fun x ↦ (⟨p x, ∑ i, a x i • v x i⟩ : TangentBundle I M)) U := by
  classical
  intro x hx
  let e := trivializationAt E (TangentSpace I) (p x)
  have hbase : ∀ᶠ y in 𝓝[U] x, p y ∈ e.baseSet :=
    (hp x hx).eventually (e.open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (p x)))
  apply (FiberBundle.continuousWithinAt_totalSpace E _).mpr
  refine ⟨hp x hx, ?_⟩
  have hc (i : ι) : ContinuousWithinAt
      (fun y ↦ (e (⟨p y, v y i⟩ : TangentBundle I M)).2) U x :=
    ((FiberBundle.continuousWithinAt_totalSpace E _).mp (hv i x hx)).2
  have hsum : ContinuousWithinAt
      (fun y ↦ ∑ i, a y i • (e (⟨p y, v y i⟩ : TangentBundle I M)).2) U x :=
    tendsto_finsetSum _ (fun i _ ↦ (ha i x hx).smul (hc i))
  apply hsum.congr_of_eventuallyEq_of_mem _ hx
  filter_upwards [hbase] with y hy
  change (e (⟨p y, ∑ i, a y i • v y i⟩ : TangentBundle I M)).2 = _
  have he : (e (⟨p y, ∑ i, a y i • v y i⟩ : TangentBundle I M)).2 =
      (e.linearMapAt ℂ (p y)) (∑ i, a y i • v y i) := by
    rw [e.linearMapAt_def_of_mem hy]
    rfl
  rw [he, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul, e.linearMapAt_def_of_mem hy]
  rfl

end HolomorphicAnosov
