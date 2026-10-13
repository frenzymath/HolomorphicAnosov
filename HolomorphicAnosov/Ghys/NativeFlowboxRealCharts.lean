import HolomorphicAnosov.Ghys.NativeFlowboxRealSmooth
import HolomorphicAnosov.Geometry.ComplexTangent
import HolomorphicAnosov.Geometry.OpenDiffeomorphMaximalChartField
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Real regularity of the native scalar leaf charts (Ghys) -/
noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff Manifold
namespace HolomorphicAnosov.Ghys
universe u v
attribute [local instance] complex_isManifold_real curveScalarToProductChartedSpace

/-- Restricting the scalar field preserves injectivity of the derivative of an actual holomorphic scalar curve into the ambient manifold. (Ghys, Lemma 3.3) -/
theorem holomorphic_curve_real_mfderiv_injective
    {d : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    {φ : ℂ → M} {z : ℂ}
    (hc : ContMDiffAt 𝓘(ℂ) (complexModel d) ∞ φ z)
    (hinj : Function.Injective (mfderiv 𝓘(ℂ) (complexModel d) φ z)) :
    Function.Injective (mfderiv 𝓘(ℝ, ℂ) (realModel d) φ z) := by
  have hr : ContMDiffAt 𝓘(ℝ, ℂ) (realModel d) ∞ φ z := by
    obtain ⟨hcont, hsmooth⟩ := contMDiffAt_iff.mp hc
    exact contMDiffAt_iff.mpr ⟨hcont, hsmooth.restrict_scalars ℝ⟩
  have hcd := hc.mdifferentiableAt (show (∞ : WithTop ℕ∞) ≠ 0 by simp)
  have hrd := hr.mdifferentiableAt (show (∞ : WithTop ℕ∞) ≠ 0 by simp)
  have hd : DifferentiableAt ℂ (writtenInExtChartAt 𝓘(ℂ) (complexModel d) z φ) z := by
    simpa only [complexModel, modelWithCornersSelf_coe, Set.range_id,
      differentiableWithinAt_univ, extChartAt_self_apply, id_eq] using
      hcd.differentiableWithinAt_writtenInExtChartAt
  intro v w hvw
  apply (tangentSpaceCastModel 𝓘(ℝ, ℂ) z).injective
  apply (tangentSpaceCastModel 𝓘(ℂ) z).symm.injective
  apply hinj
  rw [hcd.mfderiv]
  rw [hrd.mfderiv] at hvw
  simp only [realModel, complexModel, modelWithCornersSelf_coe, Set.range_id,
    fderivWithin_univ] at hvw ⊢
  change fderiv ℂ (writtenInExtChartAt 𝓘(ℂ) (complexModel d) z φ) z v =
    fderiv ℂ (writtenInExtChartAt 𝓘(ℂ) (complexModel d) z φ) z w
  change fderiv ℝ (writtenInExtChartAt 𝓘(ℂ) (complexModel d) z φ) z v =
    fderiv ℝ (writtenInExtChartAt 𝓘(ℂ) (complexModel d) z φ) z w at hvw
  rw [hd.fderiv_restrictScalars (𝕜 := ℝ)] at hvw
  exact hvw


/-- A holomorphic scalar chart on a native leaf is smooth in both directions for the original real leaf atlas. (Ghys, Lemma 3.3) -/
theorem native_holomorphic_chart_real_smooth
    {d : ℕ} {M L : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    [TopologicalSpace L] [ChartedSpace (Fin 2 → ℝ) L]
    [IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ L]
    [ChartedSpace ℂ L] [IsManifold 𝓘(ℂ) ∞ L]
    {D : RealTangentDistribution (realModel d) M}
    (N : HPS.NativeLeaf (r := 2) D L)
    (hhol : ContMDiff 𝓘(ℂ) (complexModel d) ∞ N.inclusion)
    (hinj : ∀ x, Function.Injective (mfderiv 𝓘(ℂ) (complexModel d) N.inclusion x))
    (c : OpenPartialHomeomorph L ℂ)
    (hc : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ c c.source)
    (hci : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ c.symm c.target) :
    ContMDiffOn 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) ∞ c c.source ∧
      ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 2 → ℝ) ∞ c.symm c.target := by
  have hcreal (z : ℂ) (hz : z ∈ c.target) :
      ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 2 → ℝ) ∞ c.symm z := by
    have hh := hhol.contMDiffAt.comp z (hci.contMDiffAt (c.open_target.mem_nhds hz))
    have hr : ContMDiffAt 𝓘(ℝ, ℂ) (realModel d) ∞ (N.inclusion ∘ c.symm) z := by
      obtain ⟨hcont, hsmooth⟩ := contMDiffAt_iff.mp hh
      exact contMDiffAt_iff.mpr ⟨hcont, hsmooth.restrict_scalars ℝ⟩
    exact (ContMDiffAt.iff_comp_isImmersionAt (N.immersion.isImmersionAt _)).mpr
      ⟨c.continuousAt_symm hz, hr⟩
  have hcderiv (z : ℂ) (hz : z ∈ c.target) :
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 2 → ℝ) c.symm z) := by
    have hcD : c.MDifferentiable 𝓘(ℂ) 𝓘(ℂ) :=
      ⟨hc.mdifferentiableOn (by simp), hci.mdifferentiableOn (by simp)⟩
    have hcomp : Function.Injective
        (mfderiv 𝓘(ℂ) (complexModel d) (N.inclusion ∘ c.symm) z) := by
      rw [mfderiv_comp z (hhol.mdifferentiable (by simp) _)
        (hcD.symm.mdifferentiableAt hz)]
      exact (hinj _).comp (hcD.symm.mfderiv_bijective hz).injective
    have hr := holomorphic_curve_real_mfderiv_injective
      (hhol.contMDiffAt.comp z (hci.contMDiffAt (c.open_target.mem_nhds hz))) hcomp
    rw [mfderiv_comp z (N.immersion.contMDiff.mdifferentiable (by simp) _)
      ((hcreal z hz).mdifferentiableAt (by simp))] at hr
    exact Function.Injective.of_comp hr
  refine ⟨?_, fun z hz ↦ (hcreal z hz).contMDiffWithinAt⟩
  intro x hx
  let b : OpenPartialHomeomorph L (Fin 2 → ℝ) := chartAt (Fin 2 → ℝ) x
  have hbx : x ∈ b.source := mem_chart_source _ x
  have hbD : b.MDifferentiable 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, Fin 2 → ℝ) :=
    mdifferentiable_chart (I := 𝓘(ℝ, Fin 2 → ℝ)) x
  have hbs : ContMDiffAt 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, Fin 2 → ℝ) ∞ b x :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, Fin 2 → ℝ)) (n := ∞) x) hbx
  let e : OpenPartialHomeomorph ℂ (Fin 2 → ℝ) := c.symm.trans b
  have hex : c x ∈ e.source := ⟨c.map_source hx, by change c.symm (c x) ∈ b.source; rwa [c.left_inv hx]⟩
  have heval : e (c x) = b x := by change b (c.symm (c x)) = b x; rw [c.left_inv hx]
  have htarget : b x ∈ e.target := heval ▸ e.map_source hex
  have hinverse : e.symm (b x) = c x := heval ▸ e.left_inv hex
  have hem : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 2 → ℝ) ∞ e (c x) := by
    exact hbs.comp_of_eq (hcreal (c x) (c.map_source hx)) (c.left_inv hx)
  have heDiff : ContDiffAt ℝ ∞ e (c x) := contMDiffAt_iff_contDiffAt.mp hem
  have heinj : Function.Injective (fderiv ℝ e (c x)) := by
    rw [← mfderiv_eq_fderiv]
    change Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 2 → ℝ) (b ∘ c.symm) (c x))
    rw [mfderiv_comp (c x)
      (by simpa only [c.left_inv hx] using hbD.mdifferentiableAt hbx)
      ((hcreal (c x) (c.map_source hx)).mdifferentiableAt (by simp))]
    have hbinj : Function.Injective (mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, Fin 2 → ℝ) b
        (c.symm (c x))) := by
      rw [c.left_inv hx]
      exact (hbD.mfderiv_bijective hbx).injective
    exact hbinj.comp (hcderiv (c x) (c.map_source hx))
  have hdim : Module.finrank ℝ ℂ = Module.finrank ℝ (Fin 2 → ℝ) := by simp
  let A : ℂ ≃L[ℝ] (Fin 2 → ℝ) :=
    ((fderiv ℝ e (c x)).toLinearMap.linearEquivOfInjective heinj hdim).toContinuousLinearEquiv
  have hAe : HasFDerivAt e (A : ℂ →L[ℝ] (Fin 2 → ℝ)) (c x) :=
    heDiff.differentiableAt (by simp) |>.hasFDerivAt
  have heInv : ContDiffAt ℝ ∞ e.symm (b x) :=
    e.contDiffAt_symm htarget (by simpa only [hinverse] using hAe)
      (by simpa only [hinverse] using heDiff)
  have hs : ContMDiffAt 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) ∞ (e.symm ∘ b) x :=
    (contMDiffAt_iff_contDiffAt.mpr heInv).comp x hbs
  apply (hs.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [b.open_source.mem_nhds hbx] with y hy
  change c y = c (b.symm (b y))
  rw [b.left_inv hy]


/-- Every nonempty native scalar plaque has a chart with the exact stored source and target, holomorphic in the scalar atlas and smooth in both directions in the original real atlas. (Ghys, Lemma 3.3) -/
theorem native_flowbox_real_chart
    {d : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    {ι : Type u} (L : ι → Type u)
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
    [∀ i, ChartedSpace ℂ (L i)] [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]
    (U : HPS.LeafPartition a.splitting.unstable.toDistribution ι L (fun _ ↦ 2))
    (G : NativeInvariantJetAffineLeafFamily f a L U)
    (j : Fin G.boxCount) (t : G.transverse j)
    (z : nativeAffineFlowboxSlice (G.box j) t.val) :
    ∃ c : OpenPartialHomeomorph (L (G.label j t)) ℂ,
      c ∈ IsManifold.maximalAtlas 𝓘(ℂ) ∞ (L (G.label j t)) ∧
      c.source = G.branch j t ∧ c.target = nativeAffineFlowboxSlice (G.box j) t.val ∧
      (∀ y ∈ c.source, c y = nativeLeafFlowboxScalar L U (G.box j) (G.label j t) y) ∧
      (∀ v : nativeAffineFlowboxSlice (G.box j) t.val,
        c.symm v = (G.parametrization j t v).val) ∧
      ContMDiffOn 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) ∞ c c.source ∧
      ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 2 → ℝ) ∞ c.symm c.target := by
  obtain ⟨c, hc, hs, ht, hi, _⟩ := open_diffeomorph_maximal_chart_field
    (nativeAffineFlowboxSlice (G.box j) t.val) (G.branch j t) z (G.parametrization j t)
  refine ⟨c, hc, hs, ht, ?_, hi, native_holomorphic_chart_real_smooth (U.leaf (G.label j t))
    (G.holomorphic_inclusion _).1 (G.holomorphic_inclusion _).2 c
    (contMDiffOn_of_mem_maximalAtlas hc) (contMDiffOn_symm_of_mem_maximalAtlas hc)⟩
  intro y hy
  let v : nativeAffineFlowboxSlice (G.box j) t.val := ⟨c y, by change c y ∈ (nativeAffineFlowboxSlice (G.box j) t.val : Set ℂ); rw [← ht]; exact c.map_source hy⟩
  have hpoint : (G.parametrization j t v).val = y := (hi v).symm.trans (c.left_inv hy)
  have hinc := G.parametrization_inclusion j t v
  rw [hpoint] at hinc
  have hv : (c y, t.val) ∈ (G.box j).target := v.property
  have hbox := (G.box j).right_inv hv
  rw [hinc] at hbox
  exact (congrArg Prod.fst hbox).symm

/-- Each actual ambient inverse slice is a real immersion in the original ambient atlas. (Ghys, Lemma 3.3) -/
theorem native_flowbox_slice_real_immersion
    {d : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    {ι : Type u} (L : ι → Type u)
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
    [∀ i, ChartedSpace ℂ (L i)] [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]
    (U : HPS.LeafPartition a.splitting.unstable.toDistribution ι L (fun _ ↦ 2))
    (G : NativeInvariantJetAffineLeafFamily f a L U)
    (j : Fin G.boxCount) (t : G.transverse j)
    (z : ℂ) (hz : (z, t.val) ∈ (G.box j).target) :
    ContMDiffAt 𝓘(ℝ, ℂ) (realModel d) ∞
      (fun w : ℂ ↦ (G.box j).symm (w, t.val)) z ∧
    Function.Injective (mfderiv 𝓘(ℝ, ℂ) (realModel d)
      (fun w : ℂ ↦ (G.box j).symm (w, t.val)) z) := by
  obtain ⟨c, _, _, ht, _, hi, hc, hci⟩ := native_flowbox_real_chart f a L U G j t ⟨z, hz⟩
  have hzt : z ∈ c.target := by rw [ht]; exact hz
  have heq : (fun w : ℂ ↦ (G.box j).symm (w, t.val)) =ᶠ[𝓝 z]
      (U.leaf (G.label j t)).inclusion ∘ c.symm := by
    filter_upwards [c.open_target.mem_nhds hzt] with w hw
    let v : nativeAffineFlowboxSlice (G.box j) t.val := ⟨w, by change w ∈ (nativeAffineFlowboxSlice (G.box j) t.val : Set ℂ); rwa [← ht]⟩
    change (G.box j).symm (w, t.val) = (U.leaf (G.label j t)).inclusion (c.symm w)
    rw [hi v]
    exact G.parametrization_inclusion j t v
  have hinc := (U.leaf (G.label j t)).immersion
  have hInv := hci.contMDiffAt (c.open_target.mem_nhds hzt)
  have hcomp := hinc.contMDiff.contMDiffAt.comp z hInv
  refine ⟨hcomp.congr_of_eventuallyEq heq, ?_⟩
  rw [heq.mfderiv_eq, mfderiv_comp z
    (hinc.contMDiff.mdifferentiable (by simp) _) (hInv.mdifferentiableAt (by simp))]
  have hcD : c.MDifferentiable 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) :=
    ⟨hc.mdifferentiableOn (by simp), hci.mdifferentiableOn (by simp)⟩
  exact (hinc.mfderiv_injective (by simp) _).comp (hcD.symm.mfderiv_bijective hzt).injective

end HolomorphicAnosov.Ghys
