import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientLineConnection
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.SmoothTangentFieldOfHolomorphic

open Bundle Set _root_.Topology TopologicalSpace
open scoped Manifold ContDiff
attribute [local instance] HolomorphicAnosov.complex_isManifold_real

noncomputable section
namespace HolomorphicAnosov.ConnectionCalculus

universe u
variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]

/-- Smooth quotient sections admit smooth local tangent lifts on neighborhoods within their domains.
(Zhang, §2.1, (2), p.4; Demailly, V (14.1), p.273) -/
theorem local_smooth_lift
    {P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    (hcover : ∀ x : X, ∃ V : Opens X, x ∈ V ∧
      Nonempty (QuotientLineConnection.HolomorphicFrame P V))
    (U : Opens X) (s : (x : X) → QuotientLineConnection.Fibre P x)
    (hs : ∀ (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
      (c : OpenPartialHomeomorph X (ComplexModel d)),
      c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
      ContDiffOn ℝ ∞ (fun z ↦ e.coefficient s (c.symm z))
        (c.target ∩ c.symm ⁻¹' ((V : Set X) ∩ U))) :
    ∀ x ∈ U, ∃ W : Opens X, x ∈ W ∧ W ≤ U ∧
      ∃ T : (y : X) → TangentSpace (complexModel d) y,
        QuotientLineConnection.IsSmoothTangentField W T ∧
        ∀ y ∈ W, QuotientLineConnection.projection P y (T y) = s y := by
  intro x hx
  obtain ⟨V, hxV, ⟨e⟩⟩ := hcover x
  obtain ⟨O, t, hO, hxO, hOV, ht, hte⟩ := e.holomorphic x hxV
  let W : Opens X := ⟨O ∩ U, hO.inter U.isOpen⟩
  refine ⟨W, ⟨hxO, hx⟩, inter_subset_right, fun y ↦ e.coefficient s y • t y, ?_, ?_⟩
  · intro y hy
    have hyO : y ∈ O := hy.1
    have hyV : y ∈ V := hOV hyO
    have hyU : y ∈ U := hy.2
    have hg : ContMDiffAt (realModel d) 𝓘(ℝ, ℂ) ∞ (e.coefficient s) y := by
      apply contMDiffAt_iff_source.mpr
      have hh := hs V e (chartAt (ComplexModel d) y) (IsManifold.chart_mem_maximalAtlas y)
      have hyc : chartAt (ComplexModel d) y y ∈
          (chartAt (ComplexModel d) y).target ∩
            (chartAt (ComplexModel d) y).symm ⁻¹' ((V : Set X) ∩ U) := by
        refine ⟨mem_chart_target (ComplexModel d) y, ?_⟩
        change (chartAt (ComplexModel d) y).symm (chartAt (ComplexModel d) y y) ∈
          (V : Set X) ∩ U
        rw [(chartAt (ComplexModel d) y).left_inv (mem_chart_source (ComplexModel d) y)]
        exact ⟨hyV, hyU⟩
      have hn := ((chartAt (ComplexModel d) y).isOpen_inter_preimage_symm
        (V.isOpen.inter U.isOpen)).mem_nhds hyc
      exact (hh.contDiffAt hn).contMDiffAt.contMDiffWithinAt
    let ec := trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) y
    let er := trivializationAt (ComplexModel d) (TangentSpace (realModel d)) y
    have htr := (smoothTangentField_of_holomorphic hO ht).contMDiffAt (hO.mem_nhds hyO)
    have htc := (er.contMDiffAt_section_iff
      (FiberBundle.mem_baseSet_trivializationAt' y)).mp htr
    apply ContMDiffAt.contMDiffWithinAt
    apply (er.contMDiffAt_section_iff
      (FiberBundle.mem_baseSet_trivializationAt' y)).mpr
    have hm : ContDiff ℝ ∞ (fun p : ℂ × ComplexModel d ↦ p.1 • p.2) :=
      contDiff_fst.smul contDiff_snd
    apply (hm.comp_contMDiffAt (hg.prodMk_space htc)).congr_of_eventuallyEq
    filter_upwards [(chartAt (ComplexModel d) y).open_source.mem_nhds
      (mem_chart_source (ComplexModel d) y)] with z hz
    dsimp only [Function.comp_def, er]
    rw [complexTangentToReal_coordinates y ⟨z, e.coefficient s z • t z⟩ hz,
      complexTangentToReal_coordinates y ⟨z, t z⟩ hz]
    exact (ec.linear ℂ hz).2 _ _
  · intro y hy
    apply (e.coordinate y (hOV hy.1)).injective
    simp only [map_smul, hte y hy.1, e.normalized, smul_eq_mul, mul_one]
    exact dite_eq_left (hOV hy.1)

end HolomorphicAnosov.ConnectionCalculus
