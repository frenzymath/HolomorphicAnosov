import HolomorphicAnosov.Geometry.Riemannian.PositiveBilinearCoercivity
import Mathlib.Analysis.Normed.Operator.NormedSpace
import HolomorphicAnosov.Geometry.SmoothMetricPullbackCore

open Set Bundle Filter
open scoped Topology Manifold ContDiff

namespace HolomorphicAnosov

/-- Bilinear forms with strictly positive diagonal on nonzero vectors form an open set in finite
dimension. -/
theorem isOpen_positive_bilinear_forms
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    IsOpen {B : V →L[ℝ] V →L[ℝ] ℝ | ∀ v : V, v ≠ 0 → 0 < B v v} := by
  apply (Metric.isOpen_iff (α := V →L[ℝ] V →L[ℝ] ℝ)).mpr
  intro B hB
  obtain ⟨c, hc, hbound⟩ := exists_pos_quadratic_lower_bound B hB
  refine ⟨c, hc, ?_⟩
  intro A hA v hv
  have hdist : ‖A - B‖ < c := by
    change dist A B < c at hA
    simpa only [dist_eq_norm A B] using hA
  have hnorm : ‖(A - B) v v‖ ≤ ‖A - B‖ * ‖v‖ ^ 2 := by
    calc
      ‖(A - B) v v‖ ≤ ‖(A - B) v‖ * ‖v‖ := ((A - B) v).le_opNorm v
      _ ≤ (‖A - B‖ * ‖v‖) * ‖v‖ :=
        mul_le_mul_of_nonneg_right ((A - B).le_opNorm v) (norm_nonneg v)
      _ = ‖A - B‖ * ‖v‖ ^ 2 := by ring
  have herr : |A v v - B v v| ≤ ‖A - B‖ * ‖v‖ ^ 2 := hnorm
  have hn : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  have hstrict := mul_lt_mul_of_pos_right hdist hn
  have hlow := (abs_le.mp herr).1
  have hb := hbound v
  linarith

/-- Subtraction and constant scalar multiplication of continuous maps into matching fibres are
continuous in the total-space topology. -/
theorem continuous_bundle_linear_combination
    {B X F : Type*} [TopologicalSpace B] [TopologicalSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (V : B → Type*) [∀ b, AddCommGroup (V b)] [∀ b, TopologicalSpace (V b)]
    [∀ b, Module ℝ (V b)] [TopologicalSpace (TotalSpace F V)]
    [FiberBundle F V] [VectorBundle ℝ F V]
    (b : X → B) (s t : ∀ x, V (b x))
    (hs : Continuous (fun x ↦ (⟨b x, s x⟩ : TotalSpace F V)))
    (ht : Continuous (fun x ↦ (⟨b x, t x⟩ : TotalSpace F V))) (a c : ℝ) :
    Continuous (fun x ↦ (⟨b x, a • s x - c • t x⟩ : TotalSpace F V)) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [FiberBundle.continuousAt_totalSpace F]
  have hb : Continuous b := (FiberBundle.continuous_proj (F := F) (E := V)).comp hs
  refine ⟨hb.continuousAt, ?_⟩
  let e := trivializationAt F V (b x₀)
  have hs' := (FiberBundle.continuousAt_totalSpace F _ (x₀ := x₀)).mp hs.continuousAt
  have ht' := (FiberBundle.continuousAt_totalSpace F _ (x₀ := x₀)).mp ht.continuousAt
  apply ((hs'.2.const_smul a).sub (ht'.2.const_smul c)).congr_of_eventuallyEq
  have he : ∀ᶠ x in 𝓝 x₀, b x ∈ e.baseSet := hb.continuousAt.preimage_mem_nhds
    (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' (b x₀)))
  filter_upwards [he] with x hx
  change (e ⟨b x, a • s x - c • t x⟩).2 =
    a • (e ⟨b x, s x⟩).2 - c • (e ⟨b x, t x⟩).2
  have h := (e.linearMapAt ℝ (b x)).map_sub (a • s x) (c • t x)
  simp only [map_smul] at h
  simpa only [e.coe_linearMapAt_of_mem (R := ℝ) hx] using h

/-- An open condition on a closed subspace defines an open implication on the ambient space. -/
theorem isOpen_constraint_on_closed {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsClosed K) {U : Set K} (hU : IsOpen U) :
    IsOpen {x : X | ∀ hx : x ∈ K, (⟨x, hx⟩ : K) ∈ U} := by
  have heq : {x : X | ∀ hx : x ∈ K, (⟨x, hx⟩ : K) ∈ U} =
      (Subtype.val '' Uᶜ)ᶜ := by
    ext x
    constructor
    · intro hx hbad
      obtain ⟨y, hy, rfl⟩ := hbad
      exact hy (hx y.property)
    · intro hx hmem
      by_contra hbad
      exact hx ⟨⟨x, hmem⟩, hbad, rfl⟩
  rw [heq]
  exact (hK.isClosedMap_subtype_val _ hU.isClosed_compl).isOpen_compl

section Bundle
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Positivity can be tested in any tangent trivialization containing the base point. -/
theorem positive_bilinear_coordinates_iff (x₀ x : M)
    (q : TangentSpace 𝓘(ℝ, E) x →L[ℝ] TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ)
    (hx : x ∈ (trivializationAt E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) x₀).baseSet) :
    (∀ v : E, v ≠ 0 → 0 < bilinearCoordinates x₀ x q v v) ↔
      ∀ v : TangentSpace 𝓘(ℝ, E) x, v ≠ 0 → 0 < q v v := by
  let e := (trivializationAt E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) x₀)
  let L := e.continuousLinearEquivAt ℝ x hx
  have hcoord (v w : E) : bilinearCoordinates x₀ x q v w = q (L.symm v) (L.symm w) := by
    rw [bilinearCoordinates_apply _ _ _ hx]
    change q (e.symmL ℝ x v) (e.symmL ℝ x w) = _
    rw [← e.symm_continuousLinearEquivAt_eq (R := ℝ) hx]
  constructor
  · intro h v hv
    have hn : L v ≠ 0 := (map_ne_zero_iff L L.injective).mpr hv
    simpa only [hcoord, L.symm_apply_apply] using h (L v) hn
  · intro h v hv
    rw [hcoord]
    exact h _ ((map_ne_zero_iff L.symm L.symm.injective).mpr hv)

/-- Positive bilinear tensors form an open subset of the total tensor bundle. -/
theorem isOpen_positive_bilinear_tensors [FiniteDimensional ℝ E] :
    IsOpen {z : Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x →L[ℝ]
        TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ) |
      ∀ v, v ≠ 0 → 0 < z.snd v v} := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  let e := trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
    (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x →L[ℝ]
      TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ) z.proj
  have he : ContinuousAt (fun w ↦ (e w).2) z :=
    (e.continuousAt (FiberBundle.mem_trivializationAt_proj_source)).snd
  have hbase : ∀ᶠ w in 𝓝 z, w.proj ∈
      (trivializationAt E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) z.proj).baseSet :=
    (FiberBundle.continuous_proj (F := E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun x : M ↦ TangentSpace 𝓘(ℝ, E) x →L[ℝ]
        TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ)).continuousAt.preimage_mem_nhds
      ((trivializationAt E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) z.proj).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt' z.proj))
  have hpos : ∀ v : E, v ≠ 0 → 0 < (e z).2 v v :=
    (positive_bilinear_coordinates_iff z.proj z.proj z.snd
      (FiberBundle.mem_baseSet_trivializationAt' z.proj)).mpr hz
  have hp := he.preimage_mem_nhds (isOpen_positive_bilinear_forms.mem_nhds hpos)
  filter_upwards [hbase, hp] with w hw hpw
  exact (positive_bilinear_coordinates_iff z.proj w.proj w.snd hw).mp hpw
end Bundle

end HolomorphicAnosov
