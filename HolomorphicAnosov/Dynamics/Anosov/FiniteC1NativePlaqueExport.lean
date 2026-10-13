import HolomorphicAnosov.Dynamics.Anosov.FiniteC1NativePlaqueFamily
import HolomorphicAnosov.Geometry.OpenDiffeomorphMaximalChart
import HolomorphicAnosov.Geometry.ComplexToRealManifold
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.LinearAlgebra.Dimension.Finrank

open scoped ContDiff Manifold Topology _root_.Topology
open Set TopologicalSpace Topology _root_.Topology
noncomputable section
namespace HolomorphicAnosov.HPS
universe u
attribute [local instance] complex_isManifold_real

/-- Export the original finite-C¹ native family in a fixed complex ambient chart,
with the constant real rank of its supplied native leaves.

Source: HPS (1977), continuous embedding sections (5.5), pp.61--63, and native
continuation pp.111--114. Differentiate the supplied open-plaque diffeomorphism
to identify its finite coordinate dimension with the constant leaf rank. Extend
the family off its center domain arbitrarily. Its common receiving chart is an
original ambient chart, hence a complex maximal chart. Centering gives containment
of the center domain in this chart. The supplied smoothness, embedding and joint
first-derivative continuity give the asserted finite-C¹ properties. Convert each
supplied open-plaque diffeomorphism to a maximal native chart and use its exact
inverse formula for factorization. No transverse differentiability is claimed.
DAG node: `dynamics.finite_c1_native_plaque_export_g18`.
-/
theorem FiniteC1NativePlaqueFamily.coordinate_export
    {d r k : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    {D : RealTangentDistribution (realModel d) M}
    {ι : Type u} {L : ι → Type u}
    [∀ i, TopologicalSpace (L i)]
    [∀ i, ChartedSpace (Fin r → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ (L i)]
    {F : LeafPartition D ι L (fun _ ↦ r)} {p : M}
    (Φ : FiniteC1NativePlaqueFamily F p k) :
    ∃ (V : Set M) (a : OpenPartialHomeomorph M (ComplexModel d))
        (ρ : ℝ) (q : M → (Fin r → ℝ) → M),
        IsOpen V ∧ p ∈ V ∧ V ⊆ a.source ∧
        a ∈ IsManifold.maximalAtlas (complexModel d) ∞ M ∧ 0 < ρ ∧
        (∀ x ∈ V, q x 0 = x) ∧
        (∀ x ∈ V, ∀ v ∈ Metric.ball (0 : Fin r → ℝ) ρ, q x v ∈ a.source) ∧
        (∀ x ∈ V, ContMDiffOn 𝓘(ℝ, Fin r → ℝ) (realModel d) ∞
          (q x) (Metric.ball 0 ρ)) ∧
        (∀ x ∈ V, IsEmbedding (fun v : ↥(Metric.ball (0 : Fin r → ℝ) ρ) ↦ q x v)) ∧
        (∀ x ∈ V, ∃ (i : ι) (c : OpenPartialHomeomorph (L i) (Fin r → ℝ)),
          c ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin r → ℝ) ∞ (L i) ∧
          Metric.ball (0 : Fin r → ℝ) ρ ⊆ c.target ∧
          ∀ v ∈ Metric.ball (0 : Fin r → ℝ) ρ,
            q x v = (F.leaf i).inclusion (c.symm v)) ∧
        (∀ x ∈ V, ∀ v ∈ Metric.ball (0 : Fin r → ℝ) ρ,
          HasFDerivAt (fun w ↦ a (q x w))
            (fderiv ℝ (fun w ↦ a (q x w)) v) v) ∧
        ContinuousOn (fun xv : M × (Fin r → ℝ) ↦ a (q xv.1 xv.2))
          (V ×ˢ Metric.ball 0 ρ) ∧
        ContinuousOn (fun xv : M × (Fin r → ℝ) ↦
          fderiv ℝ (fun v ↦ a (q xv.1 v)) xv.2) (V ×ˢ Metric.ball 0 ρ) := by
  classical
  let p₀ : Φ.family.centerDomain := ⟨p, Φ.family.center_mem⟩
  let v₀ : Metric.ball (0 : Fin k → ℝ) Φ.family.radius :=
    ⟨0, Metric.mem_ball_self Φ.family.radius_pos⟩
  have hkr : k = r := by
    have he := ((Φ.chart p₀).mfderivToContinuousLinearEquiv (by simp) v₀).toLinearEquiv.finrank_eq
    change Module.finrank ℝ (Fin k → ℝ) = Module.finrank ℝ (Fin r → ℝ) at he
    simpa only [Module.finrank_fin_fun] using he
  subst k
  let V := Φ.family.centerDomain
  let a := chartAt (ComplexModel d) Φ.family.receivingAnchor
  let q : M → (Fin r → ℝ) → M := fun x v ↦
    if hx : x ∈ V then (Φ.family.plaque ⟨x, hx⟩).param v else x
  have hq (x : M) (hx : x ∈ V) : q x = (Φ.family.plaque ⟨x, hx⟩).param := by
    funext v
    simp [q, hx]
  have ha : (extChartAt (realModel d) Φ.family.receivingAnchor : M → ComplexModel d) = a := by
    rfl
  have hasource : (extChartAt (realModel d) Φ.family.receivingAnchor).source = a.source := by
    simp [a]
  have hrecv (x : M) (hx : x ∈ V) (v : Fin r → ℝ)
      (hv : v ∈ Metric.ball 0 Φ.family.radius) : q x v ∈ a.source := by
    rw [hq x hx]
    rw [← hasource]
    exact Φ.family.receiving_domain ⟨x, hx⟩ v hv
  refine ⟨V, a, Φ.family.radius, q, Φ.family.centerDomain_open, Φ.family.center_mem,
    ?_, IsManifold.chart_mem_maximalAtlas _, Φ.family.radius_pos, ?_, hrecv, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro x hx
    have he := hrecv x hx 0 (Metric.mem_ball_self Φ.family.radius_pos)
    simpa [hq x hx, (Φ.family.plaque ⟨x, hx⟩).centered] using he
  · intro x hx
    rw [hq x hx]
    exact (Φ.family.plaque ⟨x, hx⟩).centered
  · intro x hx
    rw [hq x hx, ← Φ.family.domain_eq ⟨x, hx⟩]
    exact (Φ.family.plaque ⟨x, hx⟩).smooth
  · intro x hx
    rw [hq x hx, ← Φ.family.domain_eq ⟨x, hx⟩]
    exact (Φ.family.plaque ⟨x, hx⟩).embedded
  · intro x hx
    obtain ⟨c, hc, htarget, hformula⟩ := open_diffeomorph_maximal_chart
      (⟨Metric.ball (0 : Fin r → ℝ) Φ.family.radius, Metric.isOpen_ball⟩ : Opens _)
      (Φ.receivingPlaque ⟨x, hx⟩) ⟨0, Metric.mem_ball_self Φ.family.radius_pos⟩
      (Φ.chart ⟨x, hx⟩)
    refine ⟨Φ.label ⟨x, hx⟩, c, hc, ?_, ?_⟩
    · rw [htarget]
      exact subset_rfl
    · intro v hv
      rw [hq x hx, hformula ⟨v, hv⟩]
      exact Φ.factorization ⟨x, hx⟩ ⟨v, hv⟩
  · intro x hx v hv
    rw [hq x hx, ← ha]
    exact ((Φ.family.coordinate_smooth ⟨x, hx⟩).contDiffAt
      (Metric.isOpen_ball.mem_nhds hv)).differentiableAt (by simp) |>.hasFDerivAt
  · apply continuousOn_iff_continuous_domRestrict.mpr
    let f : (V ×ˢ Metric.ball (0 : Fin r → ℝ) Φ.family.radius) →
      V × Metric.ball (0 : Fin r → ℝ) Φ.family.radius := fun z ↦
      (⟨z.val.1, z.property.1⟩, ⟨z.val.2, z.property.2⟩)
    have hf : Continuous f :=
      ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
    have hg := (a.continuousOn.comp_continuous Φ.family.jointly_continuous
      (fun z ↦ by rw [← hasource]; exact Φ.family.receiving_domain z.1 z.2 z.2.property)).comp hf
    convert hg using 1
    funext z
    simp [Set.domRestrict, f, q, z.property.1]
  · apply continuousOn_iff_continuous_domRestrict.mpr
    have hf : Continuous (fun z : V ×ˢ Metric.ball (0 : Fin r → ℝ) Φ.family.radius ↦
        ((⟨z.val.1, z.property.1⟩, ⟨z.val.2, z.property.2⟩) :
          V × Metric.ball (0 : Fin r → ℝ) Φ.family.radius)) :=
      ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
    have hg := Φ.family.jointly_continuous_derivative.comp hf
    convert hg using 1
    funext z
    simp [Set.domRestrict, q, z.property.1, a]

end HolomorphicAnosov.HPS
