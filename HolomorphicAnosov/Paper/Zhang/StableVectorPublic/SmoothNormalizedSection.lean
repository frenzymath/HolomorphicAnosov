import HolomorphicAnosov.Geometry.HolomorphicComplexOneForm
import HolomorphicAnosov.Paper.Zhang.NormalizedVectorDolbeaultPullback
import Mathlib.Geometry.Manifold.PartitionOfUnity
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.RealVectorBundle

open Bundle Set Filter
open scoped Manifold ContDiff Topology _root_.Topology
namespace HolomorphicAnosov
attribute [local instance] complex_isManifold_real
noncomputable section

/-- A nowhere-zero holomorphic one-form on a compact complex manifold admits a smooth tangent
section `e₀` with `θ(e₀) = 1`. (Zhang, Lemma 4.3, p. 15) -/
theorem exists_smooth_normalized_tangent_section
    {d : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X] [T2Space X] [CompactSpace X]
    (θ : ComplexOneForm d X) (hθ : IsHolomorphicComplexOneForm θ)
    (hne : ∀ x, θ x ≠ 0) :
    ∃ e₀ : (x : X) → TangentSpace (complexModel d) x,
      ContMDiff (realModel d) ((realModel d).prod 𝓘(ℝ, ComplexModel d)) ∞
        (fun x ↦ TotalSpace.mk' (ComplexModel d) x (e₀ x)) ∧
      ∀ x, θ x (e₀ x) = 1 := by
  classical
  let V := fun x : X ↦ TangentSpace (complexModel d) x
  let : VectorBundle ℝ (ComplexModel d) V := OneFormBundle.real_vector_bundle
  let t := fun x : X ↦ {v : V x | θ x v = 1}
  have ht (x : X) : Convex ℝ (t x) :=
    (convex_singleton (1 : ℂ)).linear_preimage ((θ x).restrictScalars ℝ).toLinearMap
  have hlocal : ∀ a : X, ∃ W ∈ 𝓝 a, ∃ s : (x : X) → V x,
      ContMDiffOn (realModel d) ((realModel d).prod 𝓘(ℝ, ComplexModel d)) ∞
        (fun x ↦ TotalSpace.mk' (ComplexModel d) x (s x)) W ∧
      ∀ x ∈ W, s x ∈ t x := by
    intro a
    let c := chartAt (ComplexModel d) a
    let fr := trivializationAt (ComplexModel d) V a
    have ha : a ∈ fr.baseSet := FiberBundle.mem_baseSet_trivializationAt _ _ a
    obtain ⟨w, hw⟩ : ∃ w, θ a w ≠ 0 := by
      by_contra h
      apply hne a
      ext w
      simpa using not_exists.mp h w
    let v : ComplexModel d := fr.continuousLinearEquivAt ℂ a ha w
    let g : ComplexModel d → ℂ := fun z ↦ preferredCotangentCoefficients θ a z v
    have hg : ContDiffOn ℂ ∞ g c.target :=
      (preferredCotangentCoefficients_holomorphic θ hθ a).clm_apply contDiffOn_const
    have hga : g (c a) ≠ 0 := by
      have he := preferredCotangentCoefficients_apply θ a (c a)
        (mem_chart_target _ a) v
      have hc : c.symm (c a) = a := c.left_inv (mem_chart_source _ a)
      dsimp only [g]
      rw [he, hc, ← fr.symm_continuousLinearEquivAt_eq ha]
      simpa only [v, ContinuousLinearEquiv.symm_apply_apply] using hw
    let W := c.source ∩ c ⁻¹' {z | g z ≠ 0}
    have hW : IsOpen W :=
      (hg.continuousOn.comp c.continuousOn (fun x hx ↦ c.map_source hx)).isOpen_inter_preimage
        c.open_source isOpen_ne
    have haW : a ∈ W := ⟨mem_chart_source _ a, hga⟩
    let s : (x : X) → V x := fun x ↦ fr.symmL ℂ x ((g (c x))⁻¹ • v)
    have hsC : ContMDiffOn (complexModel d) (complexModel d).tangent ∞
        (fun x ↦ TotalSpace.mk' (ComplexModel d) x (s x)) W := by
      apply (fr.contMDiffOn_section_iff hW (fun x hx ↦ hx.1)).mpr
      have hgc : ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞ (fun x ↦ g (c x)) W :=
        hg.contMDiffOn.comp ((contMDiffOn_of_mem_maximalAtlas (I := complexModel d)
          (IsManifold.chart_mem_maximalAtlas a)).mono inter_subset_left)
          (fun x hx ↦ c.map_source hx.1)
      have hh := (hgc.inv₀ (fun x hx ↦ hx.2)).smul
        (contMDiffOn_const : ContMDiffOn (complexModel d) 𝓘(ℂ, ComplexModel d) ∞
          (fun _ : X ↦ v) W)
      apply hh.congr
      intro x hx
      dsimp only [s]
      rw [fr.symmL_apply hx.1, fr.apply_mk_symm hx.1]
      rfl
    refine ⟨W, hW.mem_nhds haW, s, ?_, ?_⟩
    · intro x hx
      obtain ⟨hc, hd⟩ := contMDiffWithinAt_iff.mp (hsC x hx)
      exact contMDiffWithinAt_iff.mpr ⟨hc, hd.restrict_scalars ℝ⟩
    · intro x hx
      change θ x (fr.symmL ℂ x ((g (c x))⁻¹ • v)) = 1
      rw [map_smul, map_smul, smul_eq_mul]
      have he := preferredCotangentCoefficients_apply θ a (c x) (c.map_source hx.1) v
      rw [c.left_inv hx.1] at he
      change g (c x) = _ at he
      rw [← he, inv_mul_cancel₀ hx.2]
  obtain ⟨s, hs⟩ := exists_contMDiffSection_forall_mem_convex_of_local
    (I := realModel d) V t ht hlocal
  exact ⟨s, s.contMDiff, hs⟩

end
end HolomorphicAnosov
