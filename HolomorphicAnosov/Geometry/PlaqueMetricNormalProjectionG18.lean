import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace HolomorphicAnosov
variable {r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The coordinate Gram operator of an injective plaque derivative in a positive tensor. -/
def plaqueGram (b : E →L[ℝ] E →L[ℝ] ℝ) (D : (Fin r → ℝ) →L[ℝ] E) :
    (Fin r → ℝ) →L[ℝ] (Fin r → ℝ) :=
  (ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) (Fin r)).toContinuousLinearMap.comp
    (b.bilinearComp D D)

/-- The Gram operator of an injective plaque derivative in a positive tensor is invertible. -/
theorem plaqueGram_isInvertible
    (b : E →L[ℝ] E →L[ℝ] ℝ) (hb : ∀ v, v ≠ 0 → 0 < b v v)
    (D : (Fin r → ℝ) →L[ℝ] E) (hD : Function.Injective D) :
    (plaqueGram b D).IsInvertible := by
  have hinj : Function.Injective (plaqueGram b D) := by
    suffices hker : ∀ v, plaqueGram b D v = 0 → v = 0 by
      intro v w hvw
      exact sub_eq_zero.mp (hker (v-w) (by simp [map_sub, hvw]))
    intro v hv
    have he : b.bilinearComp D D v = 0 :=
      (ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) (Fin r)).injective
        (by simpa [plaqueGram] using hv)
    have hzero : b (D v) (D v) = 0 := congrArg (fun l ↦ l v) he
    by_contra hn
    have hDn : D v ≠ 0 := by intro hz; apply hn; exact hD (hz.trans (map_zero D).symm)
    exact (ne_of_gt (hb (D v) hDn)) hzero
  exact ⟨(LinearEquiv.ofBijective (plaqueGram b D).toLinearMap
    ⟨hinj, LinearMap.surjective_of_injective hinj⟩).toContinuousLinearEquiv, rfl⟩

/-- The coefficients of the metric-orthogonal projection onto the plaque tangent image. -/
def plaqueMetricCoordinates (b : E →L[ℝ] E →L[ℝ] ℝ)
    (D : (Fin r → ℝ) →L[ℝ] E) : E →L[ℝ] (Fin r → ℝ) :=
  (plaqueGram b D).inverse.comp
    ((ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) (Fin r)).toContinuousLinearMap.comp
      (b.bilinearComp (ContinuousLinearMap.id ℝ E) D))

/-- The metric-orthogonal projection onto the plaque tangent image. -/
def plaqueMetricProjection (b : E →L[ℝ] E →L[ℝ] ℝ)
    (D : (Fin r → ℝ) →L[ℝ] E) : E →L[ℝ] E :=
  D.comp (plaqueMetricCoordinates b D)

theorem plaqueMetricCoordinates_derivative
    (b : E →L[ℝ] E →L[ℝ] ℝ) (hb : ∀ v, v ≠ 0 → 0 < b v v)
    (D : (Fin r → ℝ) →L[ℝ] E) (hD : Function.Injective D) (v : Fin r → ℝ) :
    plaqueMetricCoordinates b D (D v) = v := by
  change (plaqueGram b D).inverse (plaqueGram b D v) = v
  exact (plaqueGram_isInvertible b hb D hD).inverse_apply_self v

theorem plaqueMetricProjection_derivative
    (b : E →L[ℝ] E →L[ℝ] ℝ) (hb : ∀ v, v ≠ 0 → 0 < b v v)
    (D : (Fin r → ℝ) →L[ℝ] E) (hD : Function.Injective D) (v : Fin r → ℝ) :
    plaqueMetricProjection b D (D v) = D v := by
  exact congrArg D (plaqueMetricCoordinates_derivative b hb D hD v)

/-- The normal remainder is perpendicular to every plaque tangent with respect to the metric tensor. -/
theorem plaqueMetricProjection_normal
    (b : E →L[ℝ] E →L[ℝ] ℝ) (hb : ∀ v, v ≠ 0 → 0 < b v v)
    (D : (Fin r → ℝ) →L[ℝ] E) (hD : Function.Injective D) (w : E) (v : Fin r → ℝ) :
    b (w - plaqueMetricProjection b D w) (D v) = 0 := by
  have hi := (plaqueGram_isInvertible b hb D hD).self_apply_inverse
    ((ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) (Fin r))
      (b.bilinearComp (ContinuousLinearMap.id ℝ E) D w))
  have he : b.bilinearComp D D (plaqueMetricCoordinates b D w) =
      b.bilinearComp (ContinuousLinearMap.id ℝ E) D w :=
    (ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) (Fin r)).injective hi
  have hv := congrArg (fun l : (Fin r → ℝ) →L[ℝ] ℝ ↦ l v) he
  simpa only [plaqueMetricProjection, ContinuousLinearMap.comp_apply,
    map_sub, sub_apply, sub_eq_zero,
    ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.id_apply] using hv.symm
/-- Orthogonality and membership in the plaque tangent image uniquely characterize the metric
projection. -/
theorem plaqueMetricProjection_unique
    (b : E →L[ℝ] E →L[ℝ] ℝ) (hb : ∀ v, v ≠ 0 → 0 < b v v)
    (D : (Fin r → ℝ) →L[ℝ] E) (hD : Function.Injective D) (w y : E)
    (hy : y ∈ LinearMap.range D.toLinearMap)
    (hn : ∀ v, b (w-y) (D v) = 0) : plaqueMetricProjection b D w = y := by
  obtain ⟨v, rfl⟩ := hy
  let c := plaqueMetricCoordinates b D w
  have he : D (c-v) = plaqueMetricProjection b D w - D v := by
    simp [map_sub, plaqueMetricProjection, c]
  have h₁ := hn (c-v)
  have h₂ := plaqueMetricProjection_normal b hb D hD w (c-v)
  rw [he] at h₁ h₂
  change b (w-D v) (plaqueMetricProjection b D w - D v) = 0 at h₁
  have hzero : b (plaqueMetricProjection b D w - D v)
      (plaqueMetricProjection b D w - D v) = 0 := by
    have he' : plaqueMetricProjection b D w - D v =
        (w-D v) - (w-plaqueMetricProjection b D w) := by abel
    calc
      _ = b ((w-D v) - (w-plaqueMetricProjection b D w))
          (plaqueMetricProjection b D w - D v) := congrArg
        (fun a ↦ b a (plaqueMetricProjection b D w - D v)) he'
      _ = 0 := by rw [map_sub b, sub_apply, h₁, h₂, sub_self]
  apply sub_eq_zero.mp
  by_contra hn
  exact (ne_of_gt (hb _ hn)) hzero

/-- Two parametrizations of the same tangent image give the same metric projection. -/
theorem plaqueMetricProjection_eq_of_range_eq
    {s : ℕ} (b : E →L[ℝ] E →L[ℝ] ℝ) (hb : ∀ v, v ≠ 0 → 0 < b v v)
    (D : (Fin r → ℝ) →L[ℝ] E) (hD : Function.Injective D)
    (D' : (Fin s → ℝ) →L[ℝ] E) (hD' : Function.Injective D')
    (hrange : LinearMap.range D.toLinearMap = LinearMap.range D'.toLinearMap) :
    plaqueMetricProjection b D = plaqueMetricProjection b D' := by
  ext w
  apply plaqueMetricProjection_unique b hb D hD
  · rw [hrange]
    exact ⟨plaqueMetricCoordinates b D' w, rfl⟩
  · intro v
    have hm : D v ∈ LinearMap.range D'.toLinearMap := by rw [← hrange]; exact ⟨v,rfl⟩
    obtain ⟨v', hv'⟩ := hm
    rw [← hv']
    exact plaqueMetricProjection_normal b hb D' hD' w v'

/-- The kernel of the tangent coefficient operator for the supplied metric and plaque frame. -/
def plaqueNormalSpace (b : E →L[ℝ] E →L[ℝ] ℝ)
    (D : (Fin r → ℝ) →L[ℝ] E) : Submodule ℝ E :=
  (plaqueMetricCoordinates b D).ker

theorem plaqueMetricCoordinates_normal
    (b : E →L[ℝ] E →L[ℝ] ℝ) (hb : ∀ v, v ≠ 0 → 0 < b v v)
    (D : (Fin r → ℝ) →L[ℝ] E) (hD : Function.Injective D) (w : E) :
    w - plaqueMetricProjection b D w ∈ plaqueNormalSpace b D := by
  change plaqueMetricCoordinates b D (w - D (plaqueMetricCoordinates b D w)) = 0
  rw [map_sub, plaqueMetricCoordinates_derivative b hb D hD, sub_self]

/-- The tangent frame and its metric-normal space give continuous linear product coordinates on the
ambient tangent space. The inverse maps a vector to its tangent coefficients and its normal
remainder. -/
def plaqueTangentNormalEquiv
    (b : E →L[ℝ] E →L[ℝ] ℝ) (hb : ∀ v, v ≠ 0 → 0 < b v v)
    (D : (Fin r → ℝ) →L[ℝ] E) (hD : Function.Injective D) :
    ((Fin r → ℝ) × plaqueNormalSpace b D) ≃L[ℝ] E where
  toFun z := D z.1 + z.2.val
  invFun w := (plaqueMetricCoordinates b D w,
    ⟨w - plaqueMetricProjection b D w, plaqueMetricCoordinates_normal b hb D hD w⟩)
  left_inv z := by
    have hz : plaqueMetricCoordinates b D z.2.val = 0 := z.2.property
    have hc : plaqueMetricCoordinates b D (D z.1 + z.2.val) = z.1 := by
      rw [map_add, plaqueMetricCoordinates_derivative b hb D hD, hz, add_zero]
    apply Prod.ext
    · exact hc
    · apply Subtype.ext
      change D z.1 + z.2.val - D (plaqueMetricCoordinates b D (D z.1 + z.2.val)) = z.2.val
      rw [hc]
      abel
  right_inv w := by change D (plaqueMetricCoordinates b D w) + (w-D (plaqueMetricCoordinates b D w)) = w; abel
  map_add' z w := by simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, map_add]; abel
  map_smul' c z := by simp
  continuous_toFun := (D.continuous.comp continuous_fst).add
    (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := (plaqueMetricCoordinates b D).continuous.prodMk
    ((continuous_id.sub (plaqueMetricProjection b D).continuous).subtype_mk _)

/-- The Gram projection depends smoothly on positive tensors and injective plaque derivatives. -/
theorem contDiffAt_plaqueMetricProjection
    (b : E →L[ℝ] E →L[ℝ] ℝ) (hb : ∀ v, v ≠ 0 → 0 < b v v)
    (D : (Fin r → ℝ) →L[ℝ] E) (hD : Function.Injective D) (n : WithTop ℕ∞) :
    ContDiffAt ℝ n (fun z : (E →L[ℝ] E →L[ℝ] ℝ) × ((Fin r → ℝ) →L[ℝ] E) ↦
      plaqueMetricProjection z.1 z.2) (b,D) := by
  let : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedAddCommGroup ((Fin r → ℝ) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedAddCommGroup ((Fin r → ℝ) →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedAddCommGroup (E →L[ℝ] (Fin r → ℝ) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedAddCommGroup ((Fin r → ℝ) →L[ℝ] (Fin r → ℝ) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedAddCommGroup ((Fin r → ℝ) →L[ℝ] (Fin r → ℝ)) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedAddCommGroup ((Fin r → ℝ) →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedAddCommGroup (E →L[ℝ] (Fin r → ℝ)) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
  let R := ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) (Fin r)
  let flipVV : ((Fin r → ℝ) →L[ℝ] (Fin r → ℝ) →L[ℝ] ℝ) →L[ℝ]
      ((Fin r → ℝ) →L[ℝ] (Fin r → ℝ) →L[ℝ] ℝ) :=
    (ContinuousLinearMap.flipₗᵢ ℝ (Fin r → ℝ) (Fin r → ℝ) ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  let flipVE : ((Fin r → ℝ) →L[ℝ] E →L[ℝ] ℝ) →L[ℝ]
      (E →L[ℝ] (Fin r → ℝ) →L[ℝ] ℝ) :=
    (ContinuousLinearMap.flipₗᵢ ℝ (Fin r → ℝ) E ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  let flipEE : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  have hfVV : ContDiff ℝ n (fun q : (Fin r → ℝ) →L[ℝ] (Fin r → ℝ) →L[ℝ] ℝ ↦ q.flip) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := n) (E := (Fin r → ℝ) →L[ℝ] (Fin r → ℝ) →L[ℝ] ℝ)
      (F := (Fin r → ℝ) →L[ℝ] (Fin r → ℝ) →L[ℝ] ℝ) flipVV
  have hfVE : ContDiff ℝ n (fun q : (Fin r → ℝ) →L[ℝ] E →L[ℝ] ℝ ↦ q.flip) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := n) (E := (Fin r → ℝ) →L[ℝ] E →L[ℝ] ℝ)
      (F := E →L[ℝ] (Fin r → ℝ) →L[ℝ] ℝ) flipVE
  have hfEE : ContDiff ℝ n (fun q : E →L[ℝ] E →L[ℝ] ℝ ↦ q.flip) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := n) (E := E →L[ℝ] E →L[ℝ] ℝ)
      (F := E →L[ℝ] E →L[ℝ] ℝ) flipEE
  have hbil : ContDiff ℝ n (fun z : (E →L[ℝ] E →L[ℝ] ℝ) × ((Fin r → ℝ) →L[ℝ] E) ↦
      z.1.bilinearComp z.2 z.2) := by
    exact hfVV.comp
      ((hfVE.comp (contDiff_fst.clm_comp contDiff_snd)).clm_comp contDiff_snd)
  have hgram : ContDiff ℝ n (fun z : (E →L[ℝ] E →L[ℝ] ℝ) × ((Fin r → ℝ) →L[ℝ] E) ↦
      plaqueGram z.1 z.2) := contDiff_const.clm_comp hbil
  have hcross : ContDiff ℝ n (fun z : (E →L[ℝ] E →L[ℝ] ℝ) × ((Fin r → ℝ) →L[ℝ] E) ↦
      z.1.bilinearComp (ContinuousLinearMap.id ℝ E) z.2) := by
    exact hfVE.comp
      ((hfEE.comp (contDiff_fst.clm_comp contDiff_const)).clm_comp contDiff_snd)
  have hi0 : ContDiffAt ℝ n
      (ContinuousLinearMap.inverse : ((Fin r → ℝ) →L[ℝ] (Fin r → ℝ)) → ((Fin r → ℝ) →L[ℝ] (Fin r → ℝ)))
      (plaqueGram b D) := (plaqueGram_isInvertible b hb D hD).contDiffAt_map_inverse
  have hinv : ContDiffAt ℝ n (fun z : (E →L[ℝ] E →L[ℝ] ℝ) × ((Fin r → ℝ) →L[ℝ] E) ↦
      (plaqueGram z.1 z.2).inverse) (b,D) := by
    have hi := hi0.comp (b,D) hgram.contDiffAt
    exact hi
  have hcoeff : ContDiffAt ℝ n (fun z : (E →L[ℝ] E →L[ℝ] ℝ) × ((Fin r → ℝ) →L[ℝ] E) ↦
      plaqueMetricCoordinates z.1 z.2) (b,D) :=
    hinv.clm_comp (contDiffAt_const.clm_comp hcross.contDiffAt)
  exact contDiffAt_snd.clm_comp hcoeff

open scoped _root_.Topology

/-- A fixed normal frame projected onto the normal spaces of nearby plaque frames. -/
def plaqueNormalFrame {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    (b : E →L[ℝ] E →L[ℝ] ℝ) (D : (Fin r → ℝ) →L[ℝ] E)
    (C : K →L[ℝ] E) : K →L[ℝ] E :=
  (ContinuousLinearMap.id ℝ E - plaqueMetricProjection b D).comp C

/-- The metric-normal complement at a reference plaque point gives normal coordinates for all
sufficiently close tensor-frame pairs. -/
theorem eventually_invertible_plaque_normal_frame_g18 [FiniteDimensional ℝ E]
    (b : E →L[ℝ] E →L[ℝ] ℝ) (hb : ∀ v, v ≠ 0 → 0 < b v v)
    (D : (Fin r → ℝ) →L[ℝ] E) (hD : Function.Injective D) :
    ∀ᶠ z : (E →L[ℝ] E →L[ℝ] ℝ) × ((Fin r → ℝ) →L[ℝ] E) in 𝓝 (b,D),
      (z.2.coprod (plaqueNormalFrame z.1 z.2 (plaqueNormalSpace b D).subtypeL)).IsInvertible := by
  let C := (plaqueNormalSpace b D).subtypeL
  have hbase : (D.coprod (plaqueNormalFrame b D C)).IsInvertible := by
    refine ⟨plaqueTangentNormalEquiv b hb D hD, ?_⟩
    apply ContinuousLinearMap.ext
    intro z
    have hz : plaqueMetricCoordinates b D z.2.val = 0 := z.2.property
    simp [plaqueTangentNormalEquiv, plaqueNormalFrame, plaqueMetricProjection, C, hz]
  have hP := (contDiffAt_plaqueMetricProjection b hb D hD 0).continuousAt
  have hN : ContinuousAt (fun z : (E →L[ℝ] E →L[ℝ] ℝ) × ((Fin r → ℝ) →L[ℝ] E) ↦
      plaqueNormalFrame z.1 z.2 C) (b,D) :=
    (continuousAt_const.sub hP).clm_comp continuousAt_const
  exact (continuousAt_snd.continuousLinearMapCoprod hN).eventually hbase.eventually_nhds

/-- At the zero normal vector, the differential of the local-addition tube maps tangent-normal
coordinates to the sum of the plaque tangent and normal vectors. -/
theorem hasFDerivAt_plaque_normal_tube_zero_g18
    {V K : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    (q : V → E) (D : V →L[ℝ] E) (u : V) (hq : HasFDerivAt q D u)
    (N : V → K →L[ℝ] E) (N' : V →L[ℝ] K →L[ℝ] E)
    (hN : HasFDerivAt N N' u)
    (a : E × E → E)
    (ha : HasFDerivAt a ((ContinuousLinearMap.fst ℝ E E) +
      ContinuousLinearMap.snd ℝ E E) (q u,0)) :
    HasFDerivAt (fun z : V × K ↦ a (q z.1,N z.1 z.2)) (D.coprod (N u)) (u,0) := by
  have hf : HasFDerivAt (Prod.fst : V × K → V) (ContinuousLinearMap.fst ℝ V K) (u,0) :=
    hasFDerivAt_fst
  have hs : HasFDerivAt (Prod.snd : V × K → K) (ContinuousLinearMap.snd ℝ V K) (u,0) :=
    hasFDerivAt_snd
  have h1 := hq.comp (u,(0 : K)) hf
  have h2 := (hN.comp (u,(0 : K)) hf).clm_apply hs
  have ha' : HasFDerivAt a ((ContinuousLinearMap.fst ℝ E E) +
      ContinuousLinearMap.snd ℝ E E) (q u,N u 0) := by simpa only [map_zero] using ha
  have h3 := ha'.comp (u,(0 : K)) (h1.prodMk h2)
  simpa only [Function.comp_def, map_zero, add_zero,
    ContinuousLinearMap.add_comp, ContinuousLinearMap.fst_comp_prod,
    ContinuousLinearMap.snd_comp_prod, ContinuousLinearMap.comp_fst_add_comp_snd, Prod.fst, Prod.snd]
    using h3

/-- Composition with a smooth map preserves joint continuity of spatial values and first spatial
derivatives. -/
theorem continuous_spatial_first_jet_comp_g18
    {P V B C : Type*} [TopologicalSpace P]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    (F : P → V → B) (DF : P × V → V →L[ℝ] B) (g : B → C)
    (Ω : Set (P × V))
    (hF : ContinuousOn (fun z : P × V ↦ F z.1 z.2) Ω)
    (hDF : ContinuousOn DF Ω)
    (hdF : ∀ z ∈ Ω, HasFDerivAt (F z.1) (DF z) z.2)
    (hg : ∀ z ∈ Ω, ContDiffAt ℝ 1 g (F z.1 z.2)) :
    ContinuousOn (fun z : P × V ↦ g (F z.1 z.2)) Ω ∧
      ∃ DG : P × V → V →L[ℝ] C,
        ContinuousOn DG Ω ∧ ∀ z ∈ Ω,
          HasFDerivAt (fun v ↦ g (F z.1 v)) (DG z) z.2 := by
  refine ⟨fun z hz ↦ (hg z hz).continuousAt.comp_continuousWithinAt
    (f := fun z : P × V ↦ F z.1 z.2) (hF z hz), ?_⟩
  let DG : P × V → V →L[ℝ] C :=
    fun z ↦ (fderiv ℝ g (F z.1 z.2)).comp (DF z)
  refine ⟨DG, ?_, ?_⟩
  · intro z hz
    exact (((hg z hz).continuousAt_fderiv one_ne_zero).comp_continuousWithinAt
      (f := fun z : P × V ↦ F z.1 z.2) (hF z hz)).clm_comp (hDF z hz)
  · intro z hz
    exact ((hg z hz).differentiableAt one_ne_zero).hasFDerivAt.comp z.2 (hdF z hz)

end HolomorphicAnosov
