import HolomorphicAnosov.Geometry.Manifold.VectorBundle.QuotientLineConnectionC0
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.CompleteCodomain

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology Bundle
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
noncomputable section
universe u
namespace HolomorphicAnosov
open QuotientLineConnection

/-- A sequence of connections with geometrically bounded successive differences has a limiting
connection satisfying the corresponding geometric tail bound in every frame. (Zhang, Lemma 2.2,
eq. (6), p. 5) -/
theorem connection_limit_of_geometric_bound
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    {U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    (g : Bundle.ContMDiffRiemannianMetric (realModel d) ∞ (ComplexModel d)
      (fun x : X ↦ TangentSpace (realModel d) x))
    (Ds : ℕ → Connection U) {C τ : ℝ} (hC : 0 ≤ C) (hτ : 0 ≤ τ) (hτ1 : τ < 1)
    (hstep : ∀ n (V : Opens X) (e : HolomorphicFrame U V) x, x ∈ V →
      ∀ v : TangentSpace (realModel d) x,
        ‖(Ds n).form V e x v - (Ds (n + 1)).form V e x v‖ ≤
          C * τ ^ n * Real.sqrt (g.inner x v v)) :
    ∃ D : Connection U,
      (∀ (V : Opens X) (e : HolomorphicFrame U V) x, x ∈ V →
        ∀ v : TangentSpace (realModel d) x,
          Tendsto (fun n ↦ (Ds n).form V e x v) atTop (𝓝 (D.form V e x v))) ∧
      (∀ n (V : Opens X) (e : HolomorphicFrame U V) x, x ∈ V →
        ∀ v : TangentSpace (realModel d) x,
          ‖(Ds n).form V e x v - D.form V e x v‖ ≤
            (C * Real.sqrt (g.inner x v v)) * τ ^ n / (1 - τ)) ∧
      (∀ n, BddAbove (differenceValues g (Ds n) D)) ∧
      Tendsto (fun n ↦ c0Distance g (Ds n) D) atTop (𝓝 0) := by
  classical
  let : Bundle.RiemannianBundle (fun x : X ↦ TangentSpace (realModel d) x) :=
    ⟨g.toRiemannianMetric⟩
  have hb (n : ℕ) (V : Opens X) (e : HolomorphicFrame U V) (x : X) (hx : x ∈ V)
      (v : TangentSpace (realModel d) x) :
      dist ((Ds n).form V e x v) ((Ds (n + 1)).form V e x v) ≤
        (C * Real.sqrt (g.inner x v v)) * τ ^ n := by
    rw [dist_eq_norm]
    convert hstep n V e x hx v using 1
    ring
  have hex (V : Opens X) (e : HolomorphicFrame U V) (x : X) (hx : x ∈ V)
      (v : TangentSpace (realModel d) x) :
      ∃ z : ℂ, Tendsto (fun n ↦ (Ds n).form V e x v) atTop (𝓝 z) :=
    cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric τ
      (C * Real.sqrt (g.inner x v v)) hτ1 (fun n ↦ hb n V e x hx v))
  choose L hL using hex
  let F (V : Opens X) (e : HolomorphicFrame U V) (x : X)
      (v : TangentSpace (realModel d) x) := if hx : x ∈ V then L V e x hx v else 0
  have hf (V : Opens X) (e : HolomorphicFrame U V) (x : X) (hx : x ∈ V)
      (v : TangentSpace (realModel d) x) :
      Tendsto (fun n ↦ (Ds n).form V e x v) atTop (𝓝 (F V e x v)) := by
    simpa only [F, dite_eq_left hx] using hL V e x hx v
  let A (V : Opens X) (e : HolomorphicFrame U V) (x : X) :
      TangentSpace (realModel d) x →ₗ[ℝ] ℂ :=
    { toFun := F V e x
      map_add' := by
        intro v w
        by_cases hx : x ∈ V
        · apply tendsto_nhds_unique (hf V e x hx (v + w))
          simpa only [map_add] using (hf V e x hx v).add (hf V e x hx w)
        · simp [F, hx]
      map_smul' := by
        intro c v
        by_cases hx : x ∈ V
        · apply tendsto_nhds_unique (hf V e x hx (c • v))
          simpa only [map_smul, RingHom.id_apply] using (hf V e x hx v).const_smul c
        · simp [F, hx] }
  let G (V : Opens X) (e : HolomorphicFrame U V) (x : X) :=
    (A V e x).toContinuousLinearMap
  let D : Connection U :=
    { form := G
      gauge := by
        intro V W e e' x hx hx'
        ext v
        apply tendsto_nhds_unique (hf W e' x hx' v)
        apply ((hf V e x hx v).add_const _).congr'
        exact Eventually.of_forall fun n ↦
          (congrArg (fun B ↦ B v) ((Ds n).gauge V W e e' x hx hx')).symm }
  have htail (n : ℕ) (V : Opens X) (e : HolomorphicFrame U V) (x : X)
      (hx : x ∈ V) (v : TangentSpace (realModel d) x) :
      ‖(Ds n).form V e x v - D.form V e x v‖ ≤
        (C * Real.sqrt (g.inner x v v)) * τ ^ n / (1 - τ) := by
    change ‖(Ds n).form V e x v - F V e x v‖ ≤ _
    simpa only [dist_eq_norm] using dist_le_of_le_geometric_of_tendsto τ
      (C * Real.sqrt (g.inner x v v)) hτ1
      (fun k ↦ hb k V e x hx v) (hf V e x hx v) n
  have hden : 0 < 1 - τ := sub_pos.mpr hτ1
  have hub (n : ℕ) : ∀ t ∈ differenceValues g (Ds n) D,
      t ≤ C * τ ^ n / (1 - τ) := by
    rintro t ⟨V, e, x, hx, v, hv, rfl⟩
    apply (htail n V e x hx v).trans
    apply div_le_div_of_nonneg_right _ hden.le
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hτ n)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (show Real.sqrt (g.inner x v v) ≤ 1 by
        simpa using Real.sqrt_le_sqrt hv) hC
  have hbounded (n : ℕ) : BddAbove (differenceValues g (Ds n) D) :=
    ⟨C * τ ^ n / (1 - τ), hub n⟩
  have hrange (n : ℕ) : 0 ≤ c0Distance g (Ds n) D ∧
      c0Distance g (Ds n) D ≤ C * τ ^ n / (1 - τ) := by
    rcases (differenceValues g (Ds n) D).eq_empty_or_nonempty with he | hne
    · simp only [c0Distance, he, Real.sSup_empty]
      exact ⟨le_rfl, div_nonneg (mul_nonneg hC (pow_nonneg hτ n)) hden.le⟩
    · refine ⟨?_, csSup_le hne (hub n)⟩
      obtain ⟨t, ht⟩ := hne
      rcases ht with ⟨V, e, x, hx, v, hv, rfl⟩
      exact (norm_nonneg _).trans (le_csSup (hbounded n) ⟨V, e, x, hx, v, hv, rfl⟩)
  refine ⟨D, hf, htail, hbounded, ?_⟩
  apply squeeze_zero (fun n ↦ (hrange n).1) (fun n ↦ (hrange n).2)
  simpa only [mul_zero, zero_div] using
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hτ hτ1).const_mul C).div_const (1 - τ)

end HolomorphicAnosov
