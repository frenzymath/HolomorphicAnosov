import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientLineConnection

open Bundle Set _root_.Topology TopologicalSpace
open scoped Manifold ContDiff
attribute [local instance] HolomorphicAnosov.complex_isManifold_real

noncomputable section
namespace HolomorphicAnosov
namespace ConnectionCalculus

universe u
variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]

/-- Every point has an open neighborhood with a normalized holomorphic frame of the quotient tangent
line. (Zhang, §2.1, (3); Demailly, V (14.1), p.273) -/
theorem holomorphic_frame_cover
    (P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)) {r : ℕ}
    (hP : IsHolomorphicTangentSubbundle r P) (hline : IsQuotientTangentLine P) :
    ∀ x : X, ∃ V : Opens X, x ∈ V ∧
      Nonempty (QuotientLineConnection.HolomorphicFrame P V) := by
  classical
  obtain ⟨fb, vb, hv, hproj⟩ := holomorphic_quotient_tangent_line_atlas P hP hline
  let := fb
  let := vb
  let := hv
  intro x
  let e := trivializationAt ℂ (HolomorphicQuotientTangentLine P) x
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  let q := (e.linearEquivAt ℂ x hx).symm 1
  obtain ⟨v, hvq⟩ := (P x).mkQ_surjective q
  let t := trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) x
  have hxt : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  let a := (t.linearEquivAt ℂ x hxt) v
  let T : (y : X) → TangentSpace (complexModel d) y := fun y ↦ t.symm y a
  have hT : ContMDiffOn (complexModel d) (complexModel d).tangent ∞
      (fun y ↦ (⟨y, T y⟩ : TangentBundle (complexModel d) X)) t.baseSet := by
    apply t.contMDiffOn_section_baseSet_iff.mpr
    apply (contMDiffOn_const (c := a)).congr
    intro y hy
    simp [T, hy]
  have hTx : T x = v := by
    exact (t.linearEquivAt ℂ x hxt).symm_apply_apply v
  let g : X → ℂ := fun y ↦ (e (quotientTangentProjection P ⟨y, T y⟩)).2
  have hqx : quotientTangentProjection P ⟨x, T x⟩ =
      (⟨x, q⟩ : TotalSpace ℂ (HolomorphicQuotientTangentLine P)) := by
    simp only [quotientTangentProjection, hTx, hvq]
  have hgx : g x = 1 := by
    change (e (quotientTangentProjection P ⟨x, T x⟩)).2 = 1
    rw [hqx]
    exact (e.linearEquivAt ℂ x hx).apply_symm_apply 1
  have hg : ContinuousAt g x := by
    have hsec := hT.continuousOn.continuousAt (t.open_baseSet.mem_nhds hxt)
    exact (e.continuousOn.continuousAt
      (e.open_source.mem_nhds (e.mem_source.mpr hx))).snd.comp
      (hproj.continuous.continuousAt.comp hsec)
  have hn : ∀ᶠ y in nhds x, g y ≠ 0 :=
    hg.eventually_ne (by rw [hgx]; exact one_ne_zero)
  obtain ⟨W, hW, hWo, hxW⟩ := mem_nhds_iff.mp
    (Filter.inter_mem (t.open_baseSet.mem_nhds hxt)
      (Filter.inter_mem (e.open_baseSet.mem_nhds hx) hn))
  let V : Opens X := ⟨W, hWo⟩
  let s : (y : X) → QuotientLineConnection.Fibre P y := fun y ↦ (P y).mkQ (T y)
  have hs : ∀ y ∈ V, s y ≠ 0 := by
    intro y hy hz
    have hgy := (hW hy).2.2
    apply hgy
    change (e (⟨y, s y⟩ : TotalSpace ℂ (HolomorphicQuotientTangentLine P))).2 = 0
    rw [hz]
    exact (e.linearEquivAt ℂ y (hW hy).2.1).map_zero
  let L : ∀ y, y ∈ V → ℂ ≃ₗ[ℂ] QuotientLineConnection.Fibre P y := fun y hy ↦
    (LinearMap.toSpanSingleton ℂ _ (s y)).linearEquivOfInjective
      (smul_left_injective ℂ (hs y hy)) (by simpa using (hline y).symm)
  refine ⟨V, hxW, ⟨⟨s, ?_, fun y hy ↦ (L y hy).symm, ?_⟩⟩⟩
  · intro y hy
    exact ⟨W, T, hWo, hy, Set.Subset.rfl,
      hT.mono (fun z hz ↦ (hW hz).1), fun _ _ ↦ rfl⟩
  · intro y hy
    have hs' : (LinearMap.toSpanSingleton ℂ _ (s y)) 1 = s y := by
      simp
    rw [← hs']
    exact (L y hy).symm_apply_apply 1


end ConnectionCalculus
end HolomorphicAnosov
