import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.FrameTotalCoefficientHolomorphic
import HolomorphicAnosov.Analysis.Complex.HolomorphicFiberLinearDolbeault
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.CompatibleDolbeaultInFrame
import HolomorphicAnosov.Analysis.Complex.AntiholomorphicValue
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable

open Bundle Set Filter _root_.Topology TopologicalSpace
open scoped Manifold ContDiff Classical
attribute [local instance] HolomorphicAnosov.complex_isManifold_real

noncomputable section
namespace HolomorphicAnosov.ConnectionCalculus

/-- The antiholomorphic part of a compatible quotient connection is the projection of the native tangent Dolbeault derivative (Zhang, Definition 2.1, pp.4–5; Demailly, V §11, p.267). -/
theorem compatible_dolbeault_representation
    {d r : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    [T2Space X] [SecondCountableTopology X] [CompactSpace X]
    {P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    (hP : IsHolomorphicTangentSubbundle r P) (hline : IsQuotientTangentLine P)
    (D : QuotientLineConnection.Connection P) (hD : QuotientLineConnection.IsCompatible D)
    (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
    (T : (x : X) → TangentSpace (complexModel d) x)
    (hT : QuotientLineConnection.IsSmoothTangentField V T)
    (x : X) (hx : x ∈ V) (v : TangentSpace (complexModel d) x) :
    (1 / 2 : ℂ) •
      (QuotientLineConnection.covariantDerivative D e
        (fun y ↦ QuotientLineConnection.projection P y (T y)) x hx
        (complexTangentToReal d x v) +
      Complex.I • QuotientLineConnection.covariantDerivative D e
        (fun y ↦ QuotientLineConnection.projection P y (T y)) x hx
        (complexTangentToReal d x (Complex.I • v))) =
      QuotientLineConnection.projection P x (vectorDolbeault T x v) := by
  let p : TangentBundle (complexModel d) X := ⟨x, T x⟩
  let k := chartAt (ComplexModel d) x
  let t := trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) x
  let a := preferredVectorCoefficients T x
  let z := k x
  let c := extChartAt (complexModel d).tangent p
  let H : TangentBundle (complexModel d) X → ℂ := fun q ↦
    if hq : q.proj ∈ V then
      e.coordinate q.proj hq (QuotientLineConnection.projection P q.proj q.snd)
    else 0
  let F : ComplexModel d × ComplexModel d → ℂ := H ∘ c.symm
  have hc : c p = (z, a z) := by
    apply Prod.ext
    · rfl
    · change (t ⟨x, T x⟩).2 = (t ⟨k.symm (k x), T (k.symm (k x))⟩).2
      rw [k.left_inv (mem_chart_source _ x)]
  have hH : ContMDiffAt (complexModel d).tangent 𝓘(ℂ, ℂ) ∞ H p :=
    frame_total_coefficient_holomorphic hP hline V e p hx
  have hF : DifferentiableAt ℂ F (z, a z) := by
    rw [← hc]
    have hh := (hH.mdifferentiableAt (by simp)).differentiableWithinAt_writtenInExtChartAt
    simpa [writtenInExtChartAt, F, c, chartAt_self_eq, differentiableWithinAt_univ] using hh
  have ha : DifferentiableAt ℝ a z := by
    let tr := trivializationAt (ComplexModel d) (TangentSpace (realModel d)) x
    have htr := (hT x hx).contMDiffAt (V.isOpen.mem_nhds hx)
    have hcoeff := ((tr.contMDiffAt_section_iff
      (FiberBundle.mem_baseSet_trivializationAt' x)).mp htr).mdifferentiableAt (by simp)
    have hh : MDifferentiableAt (realModel d) (realModel d)
        (fun y ↦ (tr ⟨y, complexTangentToReal d y (T y)⟩).2) (k.symm z) := by
      rw [show k.symm z = x from k.left_inv (mem_chart_source _ x)]
      exact hcoeff
    have hcomp := (hh.comp z (mdifferentiableAt_atlas_symm (I := realModel d)
      (chart_mem_atlas _ x) (mem_chart_target _ x))).differentiableAt
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [k.open_target.mem_nhds (mem_chart_target _ x)] with y hy
    exact (complexTangentToReal_coordinates x ⟨k.symm y, T (k.symm y)⟩
      (k.map_target hy)).symm
  let C := tangentSpaceCastModel (complexModel d) x
  have htid : t.continuousLinearMapAt ℂ x = C.toContinuousLinearMap := by
    rw [TangentBundle.continuousLinearMapAt_trivializationAt (mem_chart_source _ x),
      mfderiv_extChartAt_self]
    rfl
  have htsi : t.symmL ℂ x = C.symm.toContinuousLinearMap := by
    rw [TangentBundle.symmL_trivializationAt (mem_chart_source _ x),
      mfderivWithin_range_extChartAt_symm]
    rfl
  have hcInv (w : ComplexModel d) : c.symm (z, w) = ⟨x, C.symm w⟩ := by
    have hh : c ⟨x, C.symm w⟩ = (z, w) := by
      change (k x, (t ⟨x, C.symm w⟩).2) = (z, w)
      rw [← t.continuousLinearMapAt_apply_of_mem ℂ (mem_chart_source _ x), htid]
      simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
      rfl
    rw [← hh, c.left_inv]
    simpa only [c, extChartAt_source, TangentBundle.mem_chart_source_iff] using
      mem_chart_source (ComplexModel d) x
  let L : ComplexModel d →L[ℂ] ℂ :=
    (((e.coordinate x hx).toLinearMap.comp (P x).mkQ).comp
      C.symm.toLinearEquiv.toLinearMap).toContinuousLinearMap
  have hL : ∀ w, F (z, w) = L w := by
    intro w
    change H (c.symm (z, w)) = L w
    rw [hcInv]
    simp only [H, hx, dite_true]
    rfl
  let g := e.coefficient (fun y ↦ QuotientLineConnection.projection P y (T y))
  have hpair : (fun y ↦ F (y, a y)) =ᶠ[𝓝 z] (g ∘ k.symm) := by
    filter_upwards [k.open_target.mem_nhds (mem_chart_target _ x)] with y hy
    have hh : c ⟨k.symm y, T (k.symm y)⟩ = (y, a y) := by
      change (k (k.symm y), a y) = (y, a y)
      rw [k.right_inv hy]
    have hm : (⟨k.symm y, T (k.symm y)⟩ : TangentBundle (complexModel d) X) ∈ c.source := by
      simpa only [c, extChartAt_source, TangentBundle.mem_chart_source_iff] using k.map_target hy
    change H (c.symm (y, a y)) = g (k.symm y)
    rw [← hh, c.left_inv hm]
    rfl
  have hgcoord : DifferentiableAt ℝ (g ∘ k.symm) z := by
    exact ((hF.restrictScalars ℝ).comp z (differentiableAt_id.prodMk ha)).congr_of_eventuallyEq
      hpair.symm
  have hg : MDifferentiableAt (realModel d) 𝓘(ℝ, ℂ) g x := by
    have hh := hgcoord.mdifferentiableAt.comp x
      (mdifferentiableAt_atlas (I := realModel d) (chart_mem_atlas _ x) (mem_chart_source _ x))
    apply hh.congr_of_eventuallyEq
    filter_upwards [k.open_source.mem_nhds (mem_chart_source _ x)] with y hy
    exact congrArg g (k.left_inv hy).symm
  have hgd (w : TangentSpace (complexModel d) x) :
      QuotientLineConnection.realDifferential g x (complexTangentToReal d x w) =
        fderiv ℝ (g ∘ k.symm) z (C w) := by
    unfold QuotientLineConnection.realDifferential
    rw [hg.mfderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply]
    change fderivWithin ℝ (writtenInExtChartAt (realModel d) 𝓘(ℝ, ℂ) x g)
      (Set.range (realModel d)) (extChartAt (realModel d) x x) (C w) = _
    simp [writtenInExtChartAt, chartAt_self_eq, k, z]
  have hcalc := holomorphic_fiber_linear_dolbeault F a z L hF ha hL (C v)
  rw [hpair.fderiv_eq] at hcalc
  rw [compatible_dolbeault_in_frame D hD V e
    (fun y ↦ QuotientLineConnection.projection P y (T y)) x hx v]
  apply (e.coordinate x hx).injective
  rw [LinearEquiv.apply_symm_apply]
  change (1 / 2 : ℂ) *
    (QuotientLineConnection.realDifferential g x (complexTangentToReal d x v) +
      Complex.I * QuotientLineConnection.realDifferential g x
        (complexTangentToReal d x (Complex.I • v))) = L (C (vectorDolbeault T x v))
  rw [hgd, hgd, map_smul, hcalc]
  congr 1
  change antiholomorphicValue (fderiv ℝ a z) (C v) =
    C (t.symmL ℂ x (vectorDolbeaultMatrix T x (star (t.continuousLinearMapAt ℂ x v))))
  rw [htid, htsi]
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
  rw [antiholomorphicValue_basis]
  ext j
  simp only [vectorDolbeaultMatrix, ContinuousLinearMap.pi_apply,
    sum_apply, smul_apply, ContinuousLinearMap.proj_apply, Pi.star_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro l _
  rw [vectorDolbeaultCoefficient, fderiv_apply ha]
  simp only [antiholomorphicValue, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  have hsingle : Pi.single l Complex.I = Complex.I • (Pi.single l 1 : ComplexModel d) := by
    ext k
    by_cases h : l = k <;> simp [h]
  rw [hsingle]
  ring

end HolomorphicAnosov.ConnectionCalculus
