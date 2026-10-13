import HolomorphicAnosov.Geometry.ComplexTangent
import HolomorphicAnosov.Geometry.TangentSectionContinuity
import HolomorphicAnosov.Geometry.TangentOneFormEvaluation
import HolomorphicAnosov.Geometry.InverseDerivative
import HolomorphicAnosov.Geometry.InverseDerivativeEquiv
import HolomorphicAnosov.Geometry.TangentDimension
import HolomorphicAnosov.Geometry.TangentLineFrame
import HolomorphicAnosov.Geometry.TangentFullFrame
import HolomorphicAnosov.Geometry.TangentZeroFrame
import HolomorphicAnosov.Geometry.ComplexSubmoduleTransfer
import HolomorphicAnosov.Analysis.Complex.NormalizedFunctional
import HolomorphicAnosov.Geometry.BiholomorphToReal
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm
import HolomorphicAnosov.Paper.Zhang.RankOneStableHolomorphicUnstable
import HolomorphicAnosov.Paper.Zhang.StableVectorHolomorphic
import HolomorphicAnosov.Targets.Theorem11
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ComplexTangentRankOne
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicTangentSubbundle
import HolomorphicAnosov.Topology.HomotopyTorusRigidity
import HolomorphicAnosov.Geometry.ComplexToRealManifold
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Under homotopy-torus rigidity, a holomorphic Anosov diffeomorphism with stable complex rank one
has holomorphic stable and unstable tangent subbundles. This file also contains local section
and inverse-map lemmas. (Zhang, Theorem 1.3, §4, pp. 13–16; Ghys, Prop. 2.2, pp. 589–590) -/

namespace HolomorphicAnosov

universe u

open Set Bundle
open scoped ContDiff Manifold _root_.Topology Bundle

attribute [local instance] complex_isManifold_real

/-- A holomorphic one-form has holomorphic coefficients in the tangent frame induced by each
compatible inverse chart. (Zhang, Lemmas 4.2–4.3, pp. 14–15) -/
private theorem theorem13_oneForm_chart_coefficients {d : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    (θ : ∀ x : X, TangentSpace (complexModel d) x →L[ℂ] ℂ)
    (hθ : ContMDiff (complexModel d)
      ((complexModel d).prod 𝓘(ℂ, ComplexModel d →L[ℂ] ℂ)) ∞
      (fun x ↦ (⟨x, θ x⟩ : Bundle.TotalSpace (ComplexModel d →L[ℂ] ℂ)
        (fun y : X ↦ TangentSpace (complexModel d) y →L[ℂ] ℂ))))
    (c : OpenPartialHomeomorph X (ComplexModel d))
    (hc : c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X) (j : Fin d) :
    DifferentiableOn ℂ
      (fun z ↦ θ (c.symm z) (hermitianTangentChartFrame c z j)) c.target := by
  have hinv := contMDiffOn_symm_of_mem_maximalAtlas hc
  have htm := hinv.contMDiffOn_tangentMapWithin (m := ∞) (by simp)
    (c.open_target.uniqueMDiffOn (I := complexModel d))
  have hconst : ContMDiff (complexModel d) (complexModel d).tangent ∞
      (fun z : ComplexModel d ↦
        (⟨z, (NormedSpace.fromTangentSpace z).symm (Pi.single j 1)⟩ :
          TangentBundle (complexModel d) (ComplexModel d))) := by
    rw [contMDiff_vectorSpace_iff_contDiff]
    change ContDiff ℂ ∞ (fun _ : ComplexModel d ↦ Pi.single j 1)
    exact contDiff_const
  have hframe : ContMDiffOn (complexModel d) (complexModel d).tangent ∞
      (fun z ↦ (⟨c.symm z, hermitianTangentChartFrame c z j⟩ :
        TangentBundle (complexModel d) X)) c.target := by
    have hcomp := htm.comp hconst.contMDiffOn (fun z hz ↦ hz)
    apply hcomp.congr
    intro z hz
    simp only [hermitianTangentChartFrame]
    congr 1
    rw [mfderivWithin_of_mem_nhds (c.open_target.mem_nhds hz)]
  have hform := hθ.comp_contMDiffOn hinv
  have heval := hform.clm_bundle_apply (F₂ := ℂ) (E₂ := fun _ : X ↦ ℂ)
    (b := c.symm) (ϕ := fun z ↦ θ (c.symm z)) hframe
  intro z hz
  have hscalar := (Bundle.contMDiffWithinAt_totalSpace.mp (heval z hz)).2
  change ContMDiffWithinAt (complexModel d) 𝓘(ℂ, ℂ) ∞
    (fun z ↦ θ (c.symm z) (hermitianTangentChartFrame c z j)) c.target z at hscalar
  exact hscalar.contDiffWithinAt.differentiableWithinAt (by simp)


/-- A section in `S` normalized by `θ(e) = 1` is continuous when `S` has nonzero continuous local
generators, `ker θ = U` complements `S`, and evaluation by `θ` is continuous. (Zhang, Lemma 4.3,
p. 15) -/
private theorem theorem13_normalized_section_continuous {d : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    (S U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    (θ : (x : X) → TangentSpace (complexModel d) x →L[ℂ] ℂ)
    (hcompl : ∀ x, IsCompl (S x) (U x))
    (hker : ∀ x, LinearMap.ker (θ x).toLinearMap = U x)
    (e : (x : X) → TangentSpace (complexModel d) x)
    (he : ∀ x, e x ∈ S x ∧ θ x (e x) = 1)
    (hlocal : ∀ x : X, ∃ v : (y : X) → TangentSpace (complexModel d) y,
      ContinuousAt (fun y ↦ (⟨y, v y⟩ : TangentBundle (complexModel d) X)) x ∧
      (∀ᶠ y in 𝓝 x, v y ∈ S y) ∧ v x ≠ 0)
    (heval : ∀ x : X, ∀ v : (y : X) → TangentSpace (complexModel d) y,
      ContinuousAt (fun y ↦ (⟨y, v y⟩ : TangentBundle (complexModel d) X)) x →
      ContinuousAt (fun y ↦ θ y (v y)) x) :
    Continuous (fun y ↦ (⟨y, e y⟩ :
      TangentBundle (complexModel d) X)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨v, hv, hvS, hv0⟩ := hlocal x
  have hvSx : v x ∈ S x := hvS.self_of_nhds
  have hθv0 : θ x (v x) ≠ 0 := by
    intro h
    exact hv0 (form_injective_on (S x) (U x) (θ x) (hcompl x) (hker x)
      hvSx (S x).zero_mem (by simpa using h))
  have hevc := heval x v hv
  have hnonzero : ∀ᶠ y in 𝓝 x, θ y (v y) ≠ 0 :=
    hevc.eventually_ne hθv0
  have hnormcont := continuousAt_section_smul v (fun y ↦ (θ y (v y))⁻¹) x
    hv (hevc.inv₀ hθv0)
  apply hnormcont.congr_of_eventuallyEq
  filter_upwards [hvS, hnonzero] with y hyS hy0
  congr 1
  symm
  apply form_injective_on (S y) (U y) (θ y) (hcompl y) (hker y)
    ((S y).smul_mem _ hyS) (he y).1
  simp [hy0, (he y).2]


noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} {X : Type*}
variable [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]

/-- A nonzero vector in a continuous real tangent subbundle extends to a continuous nowhere-zero
section on an open neighborhood. (Zhang, p. 1) -/
private theorem theorem13_real_local_section (P : ContinuousRealTangentSubbundle I X) (x : X)
    (v : P.toDistribution x) (hv : v ≠ 0) :
    ∃ O : Set X, IsOpen O ∧ x ∈ O ∧
      ∃ s : (y : O) → TangentSpace I y.val,
        Continuous (fun y : O ↦ (⟨y.val, s y⟩ : TangentBundle I X)) ∧
        ∀ y : O, s y ∈ P.toDistribution y.val ∧ s y ≠ 0 := by
  obtain ⟨r, e, hx, hl⟩ := P.locally_trivial x
  let : TopologicalSpace
      (Bundle.TotalSpace (Fin r → ℝ) (fun y : X ↦ ↥(P.toDistribution y))) :=
    TopologicalSpace.induced
      (fun z ↦ (⟨z.proj, z.snd.val⟩ : TangentBundle I X)) inferInstance
  let : e.IsLinear ℝ := hl
  let w : Fin r → ℝ := e.linearEquivAt ℝ x hx v
  have hw : w ≠ 0 := by
    exact fun h ↦ hv ((e.linearEquivAt ℝ x hx).map_eq_zero_iff.mp h)
  let s : (y : e.baseSet) → ↥(P.toDistribution y.val) :=
    fun y ↦ (e.linearEquivAt ℝ y.val y.property).symm w
  have hc : Continuous (fun y : e.baseSet ↦
      (⟨y.val, s y⟩ : Bundle.TotalSpace (Fin r → ℝ)
        (fun y : X ↦ ↥(P.toDistribution y)))) := by
    simpa only [s, w, Function.comp_def, Bundle.Trivialization.linearEquivAt_symm_apply] using
      e.continuousOn_symm.comp_continuous
        (continuous_subtype_val.prodMk continuous_const)
        (fun y ↦ ⟨y.property, Set.mem_univ w⟩)
  refine ⟨e.baseSet, e.open_baseSet, hx, fun y ↦ (s y).val, ?_, ?_⟩
  · exact continuous_induced_dom.comp hc
  · intro y
    refine ⟨(s y).property, ?_⟩
    intro h
    have hs : s y = 0 := Subtype.ext h
    exact hw ((e.linearEquivAt ℝ y.val y.property).symm.map_eq_zero_iff.mp hs)


section ComplexComparison
variable {d : ℕ} {M : Type*} [TopologicalSpace M]
variable [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
attribute [local instance] complex_isManifold_real

/-- A complex line distribution whose realification is a continuous real tangent subbundle has a
nonzero continuous local generator at every point. (Zhang, p. 1; Lemma 4.3, p. 15) -/
private theorem theorem13_complex_local_generator
    (P : ContinuousRealTangentSubbundle (realModel d) M)
    (S : (x : M) → Submodule ℂ (TangentSpace (complexModel d) x))
    (hRank : ∀ x, Module.finrank ℂ (S x) = 1)
    (hReal : ∀ x, ((S x).restrictScalars ℝ).map
      (complexTangentToReal d x).toLinearEquiv.toLinearMap = P.toDistribution x)
    (x : M) :
    ∃ v : (y : M) → TangentSpace (complexModel d) y,
      ContinuousAt (fun y ↦ (⟨y, v y⟩ : TangentBundle (complexModel d) M)) x ∧
      (∀ᶠ y in nhds x, v y ∈ S y) ∧ v x ≠ 0 := by
  classical
  let : Nontrivial (S x) := Module.nontrivial_of_finrank_pos (by rw [hRank x]; omega)
  obtain ⟨u, hu⟩ := exists_ne (0 : S x)
  let vr : P.toDistribution x := ⟨complexTangentToReal d x u.val, by
    rw [← hReal x]
    exact Submodule.mem_map.mpr ⟨u.val, u.property, rfl⟩⟩
  have hvr : vr ≠ 0 := by
    intro h
    have he : complexTangentToReal d x u.val = 0 := congrArg Subtype.val h
    exact hu (Subtype.ext ((complexTangentToReal d x).map_eq_zero_iff.mp he))
  obtain ⟨O, hO, hx, s, hs, hm⟩ := theorem13_real_local_section P x vr hvr
  let c : (y : O) → TangentSpace (complexModel d) y.val :=
    fun y ↦ (complexTangentToReal d y.val).symm (s y)
  have hc : Continuous (fun y : O ↦ (⟨y.val, c y⟩ :
      TangentBundle (complexModel d) M)) :=
    continuous_complexTangentToReal_symm.comp hs
  have hcm (y : O) : c y ∈ S y.val ∧ c y ≠ 0 := by
    refine ⟨?_, ?_⟩
    · have hm' := (hm y).1
      rw [← hReal y.val] at hm'
      exact (Submodule.mem_map_equiv ((S y.val).restrictScalars ℝ)
        (e := (complexTangentToReal d y.val).toLinearEquiv)).mp hm'
    · exact fun h ↦ (hm y).2
        ((complexTangentToReal d y.val).symm.map_eq_zero_iff.mp h)
  let v : (y : M) → TangentSpace (complexModel d) y :=
    fun y ↦ if hy : y ∈ O then c ⟨y, hy⟩ else 0
  refine ⟨v, ?_, ?_, ?_⟩
  · have hcOn : ContinuousOn (fun y ↦ (⟨y, v y⟩ :
        TangentBundle (complexModel d) M)) O := by
      apply continuousOn_iff_continuous_domRestrict.mpr
      convert hc using 1
      funext y
      simp [Set.domRestrict, v]
    exact hcOn.continuousAt (hO.mem_nhds hx)
  · filter_upwards [hO.mem_nhds hx] with y hy
    simpa only [v, dite_eq_left hy] using (hcm ⟨y, hy⟩).1
  · simpa only [v, dite_eq_left hx] using (hcm ⟨x, hx⟩).2

end ComplexComparison

end

namespace Theorem13InverseEndpoints

variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X]

section Metric

variable [Bundle.RiemannianBundle (fun x : X ↦ TangentSpace (realModel d) x)]

/-- The linear isometry between distribution fibres at equal base points for the given Riemannian
metric. (Zhang, p. 1) -/
private noncomputable def fibreTransport (P : RealTangentDistribution (realModel d) X)
    {x y : X} (h : x = y) : P x ≃ₗᵢ[ℝ] P y := by
  subst y
  exact LinearIsometryEquiv.refl ℝ (P x)

/-- The inverse fibre transport sends a vector to its tangent-space cast along the equality of base
points. -/
private theorem fibreTransport_symm_apply (P : RealTangentDistribution (realModel d) X)
    {x y : X} (h : x = y) (v : P y) :
    ((fibreTransport P h).symm v).val = tangentSpaceCast (realModel d) y x v.val := by
  subst y
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The derivative of `g.symm` restricted to an invariant distribution at `x` has operator norm
bounded by the inverse of the restricted derivative of `g` at `g.symm x`. (Ghys, pp. 589–590;
Zhang, p. 1) -/
private theorem inverse_restriction_opNorm_le
    (g : Diffeomorph (realModel d) (realModel d) X X ∞)
    (P : RealTangentDistribution (realModel d) X)
    (hP : ∀ x, (P x).map (mfderiv (realModel d) (realModel d) g x).toLinearMap = P (g x))
    (hPi : ∀ x, (P x).map (mfderiv (realModel d) (realModel d) g.symm x).toLinearMap =
      P (g.symm x)) (x : X) :
    ‖((g.symm.mfderivToContinuousLinearEquiv (by simp) x).ofSubmodules
      (P x) (P (g.symm x)) (hPi x)).toContinuousLinearMap‖ ≤
    ‖((g.mfderivToContinuousLinearEquiv (by simp) (g.symm x)).ofSubmodules
      (P (g.symm x)) (P (g (g.symm x))) (hP (g.symm x))).symm.toContinuousLinearMap‖ := by
  let A := (g.symm.mfderivToContinuousLinearEquiv (by simp) x).ofSubmodules
    (P x) (P (g.symm x)) (hPi x)
  let B := ((g.mfderivToContinuousLinearEquiv (by simp) (g.symm x)).ofSubmodules
    (P (g.symm x)) (P (g (g.symm x))) (hP (g.symm x))).symm
  let T := fibreTransport P (g.apply_symm_apply x)
  change ‖A.toContinuousLinearMap‖ ≤ ‖B.toContinuousLinearMap‖
  apply A.toContinuousLinearMap.opNorm_le_bound
    (M := ‖B.toContinuousLinearMap‖) (norm_nonneg B.toContinuousLinearMap)
  intro v
  have hav : A v = B (T.symm v) := by
    apply Subtype.ext
    change mfderiv (realModel d) (realModel d) g.symm x v.val =
      (g.mfderivToContinuousLinearEquiv (by simp) (g.symm x)).symm (T.symm v).val
    rw [derivative_equiv_symm_apply, fibreTransport_symm_apply]
    rfl
  change ‖A v‖ ≤ ‖B.toContinuousLinearMap‖ * ‖v‖
  rw [hav]
  exact (B.toContinuousLinearMap.le_opNorm (T.symm v)).trans_eq
    (by rw [T.symm.norm_map])


set_option backward.isDefEq.respectTransparency false in
/-- The inverse of the restricted derivative of `g.symm` at `x` has operator norm bounded by the
restricted derivative of `g` at `g.symm x`. (Ghys, pp. 589–590; Zhang, p. 1) -/
private theorem inverse_symm_restriction_opNorm_le
    (g : Diffeomorph (realModel d) (realModel d) X X ∞)
    (P : RealTangentDistribution (realModel d) X)
    (hP : ∀ x, (P x).map (mfderiv (realModel d) (realModel d) g x).toLinearMap = P (g x))
    (hPi : ∀ x, (P x).map (mfderiv (realModel d) (realModel d) g.symm x).toLinearMap =
      P (g.symm x)) (x : X) :
    ‖((g.symm.mfderivToContinuousLinearEquiv (by simp) x).ofSubmodules
      (P x) (P (g.symm x)) (hPi x)).symm.toContinuousLinearMap‖ ≤
    ‖((g.mfderivToContinuousLinearEquiv (by simp) (g.symm x)).ofSubmodules
      (P (g.symm x)) (P (g (g.symm x))) (hP (g.symm x))).toContinuousLinearMap‖ := by
  let A := (g.symm.mfderivToContinuousLinearEquiv (by simp) x).ofSubmodules
    (P x) (P (g.symm x)) (hPi x)
  let B := ((g.mfderivToContinuousLinearEquiv (by simp) (g.symm x)).ofSubmodules
    (P (g.symm x)) (P (g (g.symm x))) (hP (g.symm x))).symm
  let T := fibreTransport P (g.apply_symm_apply x)
  have hav (v : P x) : A v = B (T.symm v) := by
    apply Subtype.ext
    change mfderiv (realModel d) (realModel d) g.symm x v.val =
      (g.mfderivToContinuousLinearEquiv (by simp) (g.symm x)).symm (T.symm v).val
    rw [derivative_equiv_symm_apply, fibreTransport_symm_apply]
    rfl
  change ‖A.symm.toContinuousLinearMap‖ ≤ ‖B.symm.toContinuousLinearMap‖
  apply A.symm.toContinuousLinearMap.opNorm_le_bound
    (M := ‖B.symm.toContinuousLinearMap‖) (norm_nonneg B.symm.toContinuousLinearMap)
  intro w
  have hw : A.symm w = T (B.symm w) := by
    apply A.injective
    rw [A.apply_symm_apply, hav, T.symm_apply_apply, B.apply_symm_apply]
  change ‖A.symm w‖ ≤ ‖B.symm.toContinuousLinearMap‖ * ‖w‖
  rw [hw, T.norm_map]
  exact B.symm.toContinuousLinearMap.le_opNorm w


end Metric

end Theorem13InverseEndpoints

set_option backward.isDefEq.respectTransparency false in
/-- A tangent distribution invariant under a diffeomorphism is invariant under its inverse. (Zhang,
p. 1; Ghys, pp. 589–590) -/
private theorem theorem13_inverse_distribution_invariant
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (realModel d) ∞ X]
    (g : Diffeomorph (realModel d) (realModel d) X X ∞)
    (P : RealTangentDistribution (realModel d) X)
    (hP : ∀ x, (P x).map (mfderiv (realModel d) (realModel d) g x).toLinearMap =
      P (g x)) (x : X) :
    (P x).map (mfderiv (realModel d) (realModel d) g.symm x).toLinearMap =
      P (g.symm x) := by
  have h := hP (g.symm x)
  have heq : P (g (g.symm x)) = P x := by rw [g.apply_symm_apply]
  rw [heq] at h
  rw [← h, ← Submodule.map_comp]
  have hc := mfderiv_comp (g.symm x)
    (g.symm.contMDiff.mdifferentiableAt (by simp))
    (g.contMDiff.mdifferentiableAt (by simp))
  have hd : mfderiv (realModel d) (realModel d) g.symm (g (g.symm x)) =
      mfderiv (realModel d) (realModel d) g.symm x := by rw [g.apply_symm_apply]
  rw [hd] at hc
  have hid : (g.symm : X → X) ∘ g = id := by
    funext y
    exact g.symm_apply_apply y
  rw [hid, mfderiv_id] at hc
  rw [← ContinuousLinearMap.toLinearMap_comp, ← hc]
  exact Submodule.map_id _

/-- The invariant tangent splitting for `g.symm` obtained by exchanging the stable and unstable
subbundles of `g`. (Zhang, p. 1; Ghys, pp. 589–590) -/
private def theorem13_inverse_splitting
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (realModel d) ∞ X]
    (g : Diffeomorph (realModel d) (realModel d) X X ∞)
    (P : InvariantRealTangentSplitting g) : InvariantRealTangentSplitting g.symm where
  stable := P.unstable
  unstable := P.stable
  isCompl x := (P.isCompl x).symm
  stable_map := theorem13_inverse_distribution_invariant g _ P.unstable_map
  unstable_map := theorem13_inverse_distribution_invariant g _ P.stable_map


/-- The Anosov datum for `f.symm` obtained by exchanging stable and unstable subbundles while
retaining the metric and contracting iterate. (Ghys, Prop. 2.2, pp. 589–590; Zhang, p. 1) -/
private noncomputable def theorem13_inverse_anosov
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    (f : Biholomorph d d X X) (a : AnosovDatum f) : AnosovDatum f.symm where
  metric := a.metric
  splitting := theorem13_inverse_splitting f.toReal a.splitting
  k := a.k
  one_le_k := a.one_le_k
  stable_contracting := by
    let : Bundle.RiemannianBundle (fun x : X ↦ TangentSpace (realModel d) x) :=
      ⟨a.metric.toRiemannianMetric⟩
    intro x
    let g := realIterate (realModel d) f.toReal a.k
    have hP := real_distribution_iterate_invariant f.toReal
      a.splitting.unstable.toDistribution a.splitting.unstable_map a.k
    have hPi := theorem13_inverse_distribution_invariant g
      a.splitting.unstable.toDistribution hP
    have hb := Theorem13InverseEndpoints.inverse_restriction_opNorm_le g
      a.splitting.unstable.toDistribution hP hPi x
    have h := a.unstable_contracting (g.symm x)
    exact lt_of_le_of_lt hb h
  unstable_contracting := by
    let : Bundle.RiemannianBundle (fun x : X ↦ TangentSpace (realModel d) x) :=
      ⟨a.metric.toRiemannianMetric⟩
    intro x
    let g := realIterate (realModel d) f.toReal a.k
    have hP := real_distribution_iterate_invariant f.toReal
      a.splitting.stable.toDistribution a.splitting.stable_map a.k
    have hPi := theorem13_inverse_distribution_invariant g
      a.splitting.stable.toDistribution hP
    have hb := Theorem13InverseEndpoints.inverse_symm_restriction_opNorm_le g
      a.splitting.stable.toDistribution hP hPi x
    have h := a.stable_contracting (g.symm x)
    exact lt_of_le_of_lt hb h



/-- A complex rank-one tangent distribution on a nonempty complex manifold forces its complex
dimension to be at least one. (Zhang, Theorem 1.3, p. 3) -/
private theorem theorem13_stable_rank_pos {d : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X] [Nonempty X]
    (S : RealTangentDistribution (realModel d) X)
    (hS : HasComplexRankOne S) : 1 ≤ d := by
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨K, hK, _⟩ := hS x
  have h := K.finrank_le
  rw [hK, tangent_finrank] at h
  exact h


/-- In complex dimension one, a stable distribution of complex rank one and its unstable complement
are the realifications of holomorphic subbundles of ranks one and zero. (Zhang, Theorem 1.3, p.
3) -/
private theorem theorem13_dimension_one_conclusion {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel 1) X]
    [IsCompactComplexManifold 1 X]
    (f : Biholomorph 1 1 X X) (a : AnosovDatum f)
    (hstable : HasComplexRankOne a.splitting.stable.toDistribution) :
    ∃ S U : (x : X) → Submodule ℂ (TangentSpace (complexModel 1) x),
      (∀ x, ((S x).restrictScalars ℝ).map
        (complexTangentToReal 1 x).toLinearEquiv.toLinearMap =
          a.splitting.stable.toDistribution x) ∧
      (∀ x, ((U x).restrictScalars ℝ).map
        (complexTangentToReal 1 x).toLinearEquiv.toLinearMap =
          a.splitting.unstable.toDistribution x) ∧
      IsHolomorphicTangentSubbundle 1 S ∧ IsHolomorphicTangentSubbundle 0 U := by
  have hs : ∀ x, a.splitting.stable.toDistribution x = ⊤ := by
    intro x
    obtain ⟨K, hK, hreal⟩ := hstable x
    have htop : K = ⊤ := Submodule.eq_top_of_finrank_eq (hK.trans
      (tangent_finrank x).symm)
    rw [htop] at hreal
    simpa using hreal.symm
  have hu : ∀ x, a.splitting.unstable.toDistribution x = ⊥ := by
    intro x
    have hc := (a.splitting.isCompl x).disjoint.eq_bot
    rw [hs x, top_inf_eq] at hc
    exact hc
  refine ⟨fun _ ↦ ⊤, fun _ ↦ ⊥, ?_, ?_, holomorphic_top,
    holomorphic_bot⟩
  · intro x
    rw [hs x]
    simp
  · intro x
    rw [hu x]
    simp


/-- Under `HomotopyTorusRigidity`, a holomorphic Anosov diffeomorphism with stable complex rank one
has holomorphic tangent subbundles of ranks one and `d - 1` whose realifications are its stable
and unstable distributions. (Zhang, Theorem 1.3, §4, pp. 13–16; Ghys, Prop. 2.2, pp. 589–590) -/
theorem theorem_1_3 {d : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsCompactComplexManifold d X]
    (f : Biholomorph d d X X) (a : AnosovDatum f)
    (hstable : HasComplexRankOne a.splitting.stable.toDistribution)
    (HS : HomotopyTorusRigidity.{u}) :
    ∃ S U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x),
      (∀ x, ((S x).restrictScalars ℝ).map
        (complexTangentToReal d x).toLinearEquiv.toLinearMap =
          a.splitting.stable.toDistribution x) ∧
      (∀ x, ((U x).restrictScalars ℝ).map
        (complexTangentToReal d x).toLinearEquiv.toLinearMap =
          a.splitting.unstable.toDistribution x) ∧
      IsHolomorphicTangentSubbundle 1 S ∧ IsHolomorphicTangentSubbundle (d - 1) U := by
  classical
  have hdpos : 1 ≤ d := theorem13_stable_rank_pos _ hstable
  by_cases hd1 : d = 1
  · subst d
    simpa using theorem13_dimension_one_conclusion f a hstable
  have hd2 : 2 ≤ d := by omega
  obtain ⟨U, hU_hol, hU_real⟩ := rank_one_stable_holomorphic_unstable hd2 f a hstable
  let S : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x) :=
    fun x ↦ Classical.choose (hstable x)
  have hS_rank : ∀ x, Module.finrank ℂ (S x) = 1 :=
    fun x ↦ (Classical.choose_spec (hstable x)).1
  have hS_real : ∀ x, ((S x).restrictScalars ℝ).map
      (complexTangentToReal d x).toLinearEquiv.toLinearMap =
      a.splitting.stable.toDistribution x :=
    fun x ↦ (Classical.choose_spec (hstable x)).2
  refine ⟨S, U, hS_real, hU_real, ?_, hU_hol⟩
  by_cases hd_surface : d = 2
  · have hcompl : ∀ x, IsCompl (S x) (U x) := by
      intro x
      apply isCompl_of_realifications
        (complexTangentToReal d x).toLinearEquiv
      rw [hS_real x, hU_real x]
      exact a.splitting.isCompl x
    have hU_rank : ∀ x, Module.finrank ℂ (U x) = 1 := by
      intro x
      have hsum := Submodule.finrank_add_eq_of_isCompl (hcompl x)
      rw [hS_rank x, tangent_finrank] at hsum
      omega
    let ai := theorem13_inverse_anosov f a
    have hi : HasComplexRankOne ai.splitting.stable.toDistribution := by
      intro x
      exact ⟨U x, hU_rank x, hU_real x⟩
    obtain ⟨S', hS'_hol, hS'_real⟩ :=
      rank_one_stable_holomorphic_unstable hd2 f.symm ai hi
    have hSS' : S = S' := by
      funext x
      apply eq_of_realifications (complexTangentToReal d x).toLinearEquiv
      exact (hS_real x).trans (hS'_real x).symm
    rw [hSS']
    have hdim : d - 1 = 1 := by omega
    simpa only [hdim] using hS'_hol
  have hd3 : 3 ≤ d := by omega
  have hcompl : ∀ x, IsCompl (S x) (U x) := by
    intro x
    apply isCompl_of_realifications
      (complexTangentToReal d x).toLinearEquiv
    rw [hS_real x, hU_real x]
    exact a.splitting.isCompl x
  have hS_inv : ∀ x, (S x).map
      (mfderiv (complexModel d) (complexModel d) f x).toLinearMap = S (f x) := by
    intro x
    exact complex_map_of_original_map f x _ _ _ _
      (hS_real x) (hS_real (f x)) (a.splitting.stable_map x)
  have hU_inv : ∀ x, (U x).map
      (mfderiv (complexModel d) (complexModel d) f x).toLinearMap = U (f x) := by
    intro x
    exact complex_map_of_original_map f x _ _ _ _
      (hU_real x) (hU_real (f x)) (a.splitting.unstable_map x)
  obtain ⟨θ, μ, hθ_hol, hθ_ne, hθ_closed, hθ_ker, hμ_pos, hμ_lt, hθ_pull⟩ :=
    Paper.Zhang.invariant_holomorphic_one_form HS hd3 X f a hstable
  have hθ_kernel : ∀ x, LinearMap.ker (θ x).toLinearMap = U x := by
    intro x
    ext v
    change θ x v = 0 ↔ v ∈ U x
    rw [hθ_ker x v, ← hU_real x]
    simp
  have hθ_pullback : ∀ x v, θ (f x) (mfderiv (complexModel d) (complexModel d) f x v) =
      μ * θ x v := by
    intro x v
    have hv := DFunLike.congr_fun (hθ_pull x) v
    simpa using hv
  let e : (x : X) → TangentSpace (complexModel d) x := fun x ↦
    (normalized_exists_unique (S x) (U x) (θ x)
      (hcompl x) (hθ_kernel x) (hS_rank x)).exists.choose
  have he : ∀ x, e x ∈ S x ∧ θ x (e x) = 1 := fun x ↦
    (normalized_exists_unique (S x) (U x) (θ x)
      (hcompl x) (hθ_kernel x) (hS_rank x)).exists.choose_spec
  have hlocal : ∀ x : X, ∃ v : (y : X) → TangentSpace (complexModel d) y,
      ContinuousAt (fun y ↦ (⟨y, v y⟩ : TangentBundle (complexModel d) X)) x ∧
      (∀ᶠ y in 𝓝 x, v y ∈ S y) ∧ v x ≠ 0 := by
    exact theorem13_complex_local_generator a.splitting.stable S hS_rank hS_real
  have heval : ∀ x : X, ∀ v : (y : X) → TangentSpace (complexModel d) y,
      ContinuousAt (fun y ↦ (⟨y, v y⟩ : TangentBundle (complexModel d) X)) x →
      ContinuousAt (fun y ↦ θ y (v y)) x := by
    exact fun x v hv ↦ oneForm_evaluation_continuousAt θ hθ_hol.continuous
      x v hv
  have he_cont := theorem13_normalized_section_continuous S U θ hcompl hθ_kernel e he
    hlocal heval
  obtain ⟨he_hol, he_ne, he_span⟩ := stable_vector_holomorphic hd3 f a S U hS_real
    hU_real hcompl hS_rank hS_inv hU_inv θ
    (fun c hc j ↦ theorem13_oneForm_chart_coefficients θ hθ_hol c hc j)
    hθ_ne hθ_kernel μ hμ_pos hμ_lt hθ_pullback e he_cont
    (fun x ↦ (he x).1) (fun x ↦ (he x).2)
  exact holomorphic_line_of_section S e he_hol he_ne he_span

end HolomorphicAnosov
