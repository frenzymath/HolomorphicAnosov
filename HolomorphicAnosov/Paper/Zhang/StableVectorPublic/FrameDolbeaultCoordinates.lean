import HolomorphicAnosov.Paper.Zhang.NormalizedVectorDolbeaultPullback
import HolomorphicAnosov.Analysis.Distribution.HolomorphicSectionCriterion
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

open Bundle Set Filter HolomorphicAnosov.DistributionalSection
open scoped ContDiff Manifold Topology
namespace HolomorphicAnosov
noncomputable section

/-- A holomorphic frame has holomorphic linear coordinates relative to a preferred frame. -/
theorem holomorphic_frame_transition_at
    {d : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    (c : OpenPartialHomeomorph X (ComplexModel d))
    (hc : c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X)
    (fr : Trivialization (ComplexModel d)
      (TotalSpace.proj : TangentBundle (complexModel d) X → X))
    (hfr : IsHolomorphicFrame (d := d) fr) [fr.IsLinear ℂ]
    (a : X) (z : ComplexModel d) (hz : z ∈ frameDomain c fr)
    (ha : c.symm z ∈ (chartAt (ComplexModel d) a).source) :
    ContDiffAt ℂ ∞ (fun w ↦ (fr.continuousLinearMapAt ℂ (c.symm w)).comp
      ((trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) a).symmL ℂ (c.symm w))) z := by
  let t := trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) a
  apply contDiffWithinAt_clm_apply.mpr
  intro v
  have hcinv := contMDiffAt_symm_of_mem_maximalAtlas hc hz.1
  have ht := (t.contMDiffOn_symm (IB := complexModel d) (n := ∞)).contMDiffAt
    (t.open_target.mem_nhds (show (c.symm z, v) ∈ t.target from ⟨ha, Set.mem_univ v⟩))
  have hs := ht.comp z (hcinv.prodMk contMDiffAt_const)
  have hsource : t.toOpenPartialHomeomorph.symm (c.symm z, v) ∈ fr.source := by
    rw [← t.mk_symm ha]
    exact fr.mem_source.mpr hz.2
  have hf := hfr.2.1.contMDiffAt (fr.open_source.mem_nhds hsource)
  have hresult := (contMDiffAt_snd.comp z (hf.comp z hs)).contDiffAt
  apply hresult.contDiffWithinAt.congr_of_eventuallyEq
  · have hn := c.continuousAt_symm hz.1
    filter_upwards [nhdsWithin_le_nhds (hn.preimage_mem_nhds (t.open_baseSet.mem_nhds ha)),
      nhdsWithin_le_nhds (hn.preimage_mem_nhds (fr.open_baseSet.mem_nhds hz.2))] with w hwa hwf
    rw [ContinuousLinearMap.comp_apply, t.symmL_apply hwa,
      fr.continuousLinearMapAt_apply_of_mem ℂ hwf, t.mk_symm hwa]
    rfl
  · rw [ContinuousLinearMap.comp_apply, t.symmL_apply ha,
      fr.continuousLinearMapAt_apply_of_mem ℂ hz.2, t.mk_symm ha]
    rfl

/-- In a holomorphic frame, the antiholomorphic derivative of a section is the coordinate expression
of its native Dolbeault tensor. (Demailly, V §11, pp.267–268) -/
theorem frame_dolbeault_vector_coordinates
    {d : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    (s : (x : X) → TangentSpace (complexModel d) x)
    (hs : ∀ a, ContDiffOn ℝ ∞ (preferredVectorCoefficients s a)
      (chartAt (ComplexModel d) a).target)
    (c : OpenPartialHomeomorph X (ComplexModel d))
    (hc : c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X)
    (fr : Trivialization (ComplexModel d)
      (TotalSpace.proj : TangentBundle (complexModel d) X → X))
    (hfr : IsHolomorphicFrame (d := d) fr) [fr.IsLinear ℂ]
    (z : ComplexModel d) (hz : z ∈ frameDomain c fr) (v : ComplexModel d) :
    antiholomorphicValue (fderiv ℝ (fun w ↦ fun k ↦ coefficient s c fr k w) z) v =
      fr.continuousLinearMapAt ℂ (c.symm z)
        (vectorDolbeault s (c.symm z)
          (mfderiv (complexModel d) (complexModel d) c.symm z
            ((NormedSpace.fromTangentSpace z).symm v))) := by
  let a := c.symm z
  let ca := chartAt (ComplexModel d) a
  let t := trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) a
  let C := fun w ↦ (fr.continuousLinearMapAt ℂ (c.symm w)).comp (t.symmL ℂ (c.symm w))
  let φ : ComplexModel d → ComplexModel d := fun w ↦ ca (c.symm w)
  have ha : c.symm z ∈ ca.source := mem_chart_source _ a
  have hC := (holomorphic_frame_transition_at c hc fr hfr a z hz ha).differentiableAt (by simp)
  have hφ : ContDiffAt ℂ ∞ φ z :=
    ((contMDiffAt_of_mem_maximalAtlas (n := ∞) (IsManifold.chart_mem_maximalAtlas a) ha).comp z
      (contMDiffAt_symm_of_mem_maximalAtlas hc hz.1)).contDiffAt
  have hsa := ((hs a).contDiffAt (ca.open_target.mem_nhds (ca.map_source ha))).differentiableAt (by simp)
  have heq : (fun w ↦ fun k ↦ coefficient s c fr k w) =ᶠ[𝓝 z]
      (fun w ↦ C w (preferredVectorCoefficients s a (φ w))) := by
    have hn := c.continuousAt_symm hz.1
    filter_upwards [hn.preimage_mem_nhds (ca.open_source.mem_nhds ha),
      hn.preimage_mem_nhds (fr.open_baseSet.mem_nhds hz.2)] with w hwa hwf
    change (fr (TotalSpace.mk' (ComplexModel d) (c.symm w) (s (c.symm w)))).2 = _
    dsimp only [C, φ, preferredVectorCoefficients, ContinuousLinearMap.comp_apply]
    rw [ca.left_inv hwa, ← t.continuousLinearMapAt_apply_of_mem ℂ hwa,
      t.symmL_continuousLinearMapAt hwa, fr.continuousLinearMapAt_apply_of_mem ℂ hwf]
  rw [heq.fderiv_eq]
  have hcalc := antiholomorphicValue_fderiv_pullback C (fderiv ℂ C z)
    (preferredVectorCoefficients s a) (fderiv ℝ (preferredVectorCoefficients s a) (φ z))
    φ (fderiv ℂ φ z) z hC.hasFDerivAt hsa.hasFDerivAt
    (hφ.differentiableAt (by simp)).hasFDerivAt v
  rw [hcalc]
  have hchart := vectorDolbeault_chart s hs a (φ z) (ca.map_source ha)
    (mfderiv (complexModel d) (complexModel d) c.symm z
      ((NormedSpace.fromTangentSpace z).symm v))
  have hleft : ca.symm (φ z) = c.symm z := ca.left_inv ha
  rw [hleft] at hchart
  rw [hchart]
  dsimp only [C, ContinuousLinearMap.comp_apply]
  apply congrArg (fr.continuousLinearMapAt ℂ (c.symm z))
  apply congrArg (t.symmL ℂ (c.symm z))
  apply congrArg (antiholomorphicValue (fderiv ℝ (preferredVectorCoefficients s a) (φ z)))
  have ht := TangentBundle.continuousLinearMapAt_trivializationAt (I := complexModel d) ha
  rw [ht]
  have hchain := mfderiv_comp z
    ((contMDiffAt_of_mem_maximalAtlas (n := ∞) (IsManifold.chart_mem_maximalAtlas a) ha).mdifferentiableAt (by simp))
    ((contMDiffAt_symm_of_mem_maximalAtlas hc hz.1).mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hchain
  exact congrArg (fun L ↦ L v) hchain

/-- The scalar Wirtinger coefficients of a section are the coordinates of its native Dolbeault
tensor. -/
theorem frame_dolbeault_scalar_coordinates
    {d : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    (s : (x : X) → TangentSpace (complexModel d) x)
    (hs : ∀ a, ContDiffOn ℝ ∞ (preferredVectorCoefficients s a)
      (chartAt (ComplexModel d) a).target)
    (c : OpenPartialHomeomorph X (ComplexModel d))
    (hc : c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X)
    (fr : Trivialization (ComplexModel d)
      (TotalSpace.proj : TangentBundle (complexModel d) X → X))
    (hfr : IsHolomorphicFrame (d := d) fr) [fr.IsLinear ℂ]
    (z : ComplexModel d) (hz : z ∈ frameDomain c fr)
    (hdiff : DifferentiableAt ℝ (fun w ↦ fun k ↦ coefficient s c fr k w) z)
    (j k : Fin d) :
    (2 : ℂ)⁻¹ * (fderiv ℝ (coefficient s c fr k) z (Pi.single j 1) +
      Complex.I * fderiv ℝ (coefficient s c fr k) z (Pi.single j Complex.I)) =
      (fr (TotalSpace.mk' (ComplexModel d) (c.symm z)
        (vectorDolbeault s (c.symm z) (hermitianTangentChartFrame c z j)))).2 k := by
  have heq := congrArg (fun w : ComplexModel d ↦ w k)
    (frame_dolbeault_vector_coordinates s hs c hc fr hfr z hz (Pi.single j 1))
  rw [fr.continuousLinearMapAt_apply_of_mem ℂ hz.2] at heq
  have hscl : Complex.I • Pi.single j (1 : ℂ) = Pi.single j Complex.I := by
    ext i
    by_cases hi : i = j <;> simp [hi]
  have hd := fderiv_apply hdiff k
  simpa only [antiholomorphicValue, Pi.smul_apply, Pi.add_apply, smul_eq_mul, one_div,
    hscl, hd, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    hermitianTangentChartFrame] using heq

end
end HolomorphicAnosov
