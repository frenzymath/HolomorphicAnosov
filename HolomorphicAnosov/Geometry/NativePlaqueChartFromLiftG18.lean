import HolomorphicAnosov.Geometry.OpenDiffeomorphMaximalChartField
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.LinearAlgebra.Dimension.Constructions

noncomputable section
open Set TopologicalSpace Manifold _root_.Topology
open scoped ContDiff _root_.Topology
namespace HolomorphicAnosov

/-- An injective smooth local diffeomorphism on an open native parameter domain defines an intrinsic
maximal chart on its full image. (Lee, 2003, Chs. 1–2, pp.13–15, 36; Ghys, 1995, pp.589–590) -/
theorem native_plaque_chart_from_lift_g18
    {r s : ℕ} {L : Type*} [TopologicalSpace L]
    [ChartedSpace (Fin s → ℝ) L] [IsManifold 𝓘(ℝ,Fin s → ℝ) ∞ L]
    (B : Opens (Fin r → ℝ)) (b : B) (l : B → L)
    (hl : IsLocalDiffeomorph 𝓘(ℝ,Fin r → ℝ) 𝓘(ℝ,Fin s → ℝ) ∞ l)
    (ho : IsOpenEmbedding l) :
    ∃ J : (Fin s → ℝ) ≃ₗᵢ[ℝ] (Fin r → ℝ),
      ∃ c : OpenPartialHomeomorph L (Fin s → ℝ),
        c ∈ IsManifold.maximalAtlas 𝓘(ℝ,Fin s → ℝ) ∞ L ∧
        c.source = Set.range l ∧ c.target = J ⁻¹' (B : Set (Fin r → ℝ)) ∧
        (∀ v : Fin s → ℝ, ∀ hv : J v ∈ B, c.symm v = l ⟨J v,hv⟩) ∧
        ∀ v : B, c (l v) = J.symm v.val := by
  have hrs : r = s := by
    let e := (hl b).mfderivToContinuousLinearEquiv (by simp)
    have h := e.toLinearEquiv.finrank_eq
    change Module.finrank ℝ (Fin r → ℝ) = Module.finrank ℝ (Fin s → ℝ) at h
    simpa only [Module.finrank_fin_fun] using h
  subst s
  let U : Opens L := ⟨Set.range l,ho.isOpen_range⟩
  let e : B ≃ₜ U := ho.isEmbedding.toHomeomorph
  have hei (v : U) : l (e.symm v) = v.val :=
    congrArg Subtype.val (e.apply_symm_apply v)
  have hf : ContMDiff 𝓘(ℝ,Fin r → ℝ) 𝓘(ℝ,Fin r → ℝ) ∞ e := by
    apply (ContMDiff.subtypeVal_comp_iff U e).mp
    exact hl.contMDiff
  have hi : ContMDiff 𝓘(ℝ,Fin r → ℝ) 𝓘(ℝ,Fin r → ℝ) ∞ e.symm := by
    intro y
    let h := hl (e.symm y)
    have hp : y.val ∈ h.localInverse.source := by
      rw [← hei y]
      exact h.localInverse_mem_source
    have hs : ContMDiffAt 𝓘(ℝ,Fin r → ℝ) 𝓘(ℝ,Fin r → ℝ) ∞ h.localInverse y.val :=
      h.localInverse_contMDiffOn.contMDiffAt (h.localInverse.open_source.mem_nhds hp)
    have heq : e.symm =ᶠ[𝓝 y] (h.localInverse ∘ (Subtype.val : U → L)) := by
      filter_upwards [continuous_subtype_val.continuousAt
        (h.localInverse.open_source.mem_nhds hp)] with z hz
      apply ho.injective
      exact (hei z).trans (h.localInverse_right_inv hz).symm
    exact (hs.comp y contMDiff_subtype_val.contMDiffAt).congr_of_eventuallyEq heq
  let d : Diffeomorph 𝓘(ℝ,Fin r → ℝ) 𝓘(ℝ,Fin r → ℝ) B U ∞ :=
    ⟨e.toEquiv,hf,hi⟩
  obtain ⟨c,hc,hsource,htarget,hinv,hfor⟩ := open_diffeomorph_maximal_chart_field B U b d
  refine ⟨LinearIsometryEquiv.refl ℝ (Fin r → ℝ),c,hc,hsource,htarget,?_,?_⟩
  · intro v hv
    exact hinv ⟨v,hv⟩
  · intro v
    change c (l v) = v.val
    have hh := hfor (d v)
    change c (l v) = ((d.symm (d v)) : B).val at hh
    simpa only [Diffeomorph.symm_apply_apply] using hh

end HolomorphicAnosov
