import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicTangentSubbundle
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine.Basic
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine.ExistsLocalData
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine.FibreInducing
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine.TrivializationLinear
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine.TransitionSmooth
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine.TransitionEq

/-! The tangent quotient by a holomorphic subbundle with one-dimensional quotient fibres carries a
holomorphic line-bundle atlas. The quotient projection is holomorphic for this atlas and the
coinduced total-space topology (Demailly, V §1, pp.253–254, §11, p.267, (14.1), p.273; Zhang,
§2.1, pp.4–5). -/

open Bundle Set
open scoped Manifold ContDiff Topology _root_.Topology Classical

noncomputable section

namespace HolomorphicAnosov

universe u

variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]

/-- The tangent quotient by a holomorphic subbundle with one-dimensional quotient fibres admits a
holomorphic vector-bundle atlas making the quotient projection holomorphic (Demailly, V §1,
pp.253–254, §11, p.267, (14.1), p.273; Zhang, §2.1, p.4). -/
theorem holomorphic_quotient_tangent_line_atlas
    (P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)) {r : ℕ}
    (hP : IsHolomorphicTangentSubbundle r P) (hline : IsQuotientTangentLine P) :
    ∃ fb : FiberBundle ℂ (HolomorphicQuotientTangentLine P),
      letI := fb
      ∃ vb : VectorBundle ℂ ℂ (HolomorphicQuotientTangentLine P),
        letI := vb
        ∃ hv : ContMDiffVectorBundle ∞ ℂ (HolomorphicQuotientTangentLine P)
            (complexModel d),
          letI := hv
          ContMDiff (complexModel d).tangent ((complexModel d).prod 𝓘(ℂ, ℂ)) ∞
            (quotientTangentProjection P) := by
  classical
  choose D hD using (fun x : X ↦ exists_quotient_local_data P hP hline x)
  let fb : FiberBundle ℂ (HolomorphicQuotientTangentLine P) := {
    totalSpaceMk_isInducing' := fun x ↦ (D x).fibre_inducing x (hD x)
    trivializationAtlas' := Set.range (fun A : QuotientLocalData P ↦ A.trivialization)
    trivializationAt' := fun x ↦ (D x).trivialization
    mem_baseSet_trivializationAt' := hD
    trivialization_mem_atlas' := fun x ↦ ⟨D x, rfl⟩ }
  refine ⟨fb, ?_⟩
  let _ := fb
  let vb : VectorBundle ℂ ℂ (HolomorphicQuotientTangentLine P) := {
    trivialization_linear' := by
      intro e he
      have h := he.out
      change e ∈ Set.range (fun A : QuotientLocalData P ↦ A.trivialization) at h
      obtain ⟨A, rfl⟩ := h
      infer_instance
    continuousOn_coordChange' := by
      intro e e' he he'
      have h := he.out
      have h' := he'.out
      change e ∈ Set.range (fun A : QuotientLocalData P ↦ A.trivialization) at h
      change e' ∈ Set.range (fun A : QuotientLocalData P ↦ A.trivialization) at h'
      obtain ⟨A, rfl⟩ := h
      obtain ⟨A', rfl⟩ := h'
      exact (A.transition_smooth A').continuousOn.congr
        (fun x hx ↦ A.transition_eq A' x hx) }
  refine ⟨vb, ?_⟩
  let _ := vb
  let hv : ContMDiffVectorBundle ∞ ℂ (HolomorphicQuotientTangentLine P) (complexModel d) := {
    contMDiffOn_coordChangeL := by
      intro e e' he he'
      have h := he.out
      have h' := he'.out
      change e ∈ Set.range (fun A : QuotientLocalData P ↦ A.trivialization) at h
      change e' ∈ Set.range (fun A : QuotientLocalData P ↦ A.trivialization) at h'
      obtain ⟨A, rfl⟩ := h
      obtain ⟨A', rfl⟩ := h'
      exact (A.transition_smooth A').congr (fun x hx ↦ A.transition_eq A' x hx) }
  refine ⟨hv, ?_⟩
  let _ := hv
  change ContMDiff (complexModel d).tangent ((complexModel d).prod 𝓘(ℂ, ℂ)) ∞
    (quotientTangentProjection P)
  intro p
  apply Bundle.contMDiffAt_totalSpace.mpr
  refine ⟨?_, ?_⟩
  · exact contMDiffAt_proj (TangentSpace (complexModel d))
  · change ContMDiffAt (complexModel d).tangent 𝓘(ℂ, ℂ) ∞
      (fun q : TangentBundle (complexModel d) X ↦
        ((D p.proj).trivialization (quotientTangentProjection P q)).2) p
    apply ((D p.proj).hscalar p (hD p.proj)).congr_of_eventuallyEq
    filter_upwards [(FiberBundle.continuous_proj (ComplexModel d)
      (TangentSpace (complexModel d))).continuousAt.preimage_mem_nhds
        ((D p.proj).V.isOpen.mem_nhds (hD p.proj))] with q hq
    change (if h : q.proj ∈ (D p.proj).V then
      (D p.proj).L q.proj h ((P q.proj).mkQ q.snd) else 0) =
        (D p.proj).θ q.proj q.snd
    have hx : q.proj ∈ (D p.proj).V := hq
    rw [dite_eq_left hx, (D p.proj).apply_mk]

/-- A fibre-bundle atlas on the tangent quotient by a holomorphic subbundle with one-dimensional
quotient fibres (Demailly, V (14.1), p.273). -/
@[instance_reducible]
def quotientTangentLineFiberBundle
    (P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)) {r : ℕ}
    (hP : IsHolomorphicTangentSubbundle r P) (hline : IsQuotientTangentLine P) :
    FiberBundle ℂ (HolomorphicQuotientTangentLine P) :=
  (holomorphic_quotient_tangent_line_atlas P hP hline).choose

/-- The chosen tangent quotient atlas has a complex vector-bundle structure (Demailly, V §1,
pp.253–254, (14.1), p.273). -/
theorem quotientTangentLineVectorBundle
    (P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)) {r : ℕ}
    (hP : IsHolomorphicTangentSubbundle r P) (hline : IsQuotientTangentLine P) :
    letI := quotientTangentLineFiberBundle P hP hline
    VectorBundle ℂ ℂ (HolomorphicQuotientTangentLine P) :=
  (holomorphic_quotient_tangent_line_atlas P hP hline).choose_spec.choose

/-- The chosen tangent quotient atlas has holomorphic transition maps (Demailly, V §11, p.267,
(14.1), p.273). -/
theorem quotientTangentLineContMDiffVectorBundle
    (P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)) {r : ℕ}
    (hP : IsHolomorphicTangentSubbundle r P) (hline : IsQuotientTangentLine P) :
    letI := quotientTangentLineFiberBundle P hP hline
    letI := quotientTangentLineVectorBundle P hP hline
    ContMDiffVectorBundle ∞ ℂ (HolomorphicQuotientTangentLine P) (complexModel d) :=
  (holomorphic_quotient_tangent_line_atlas P hP hline).choose_spec.choose_spec.choose


end HolomorphicAnosov
