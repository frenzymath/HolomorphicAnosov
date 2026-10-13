import HolomorphicAnosov.Dynamics.HirschPughFactOneData
import HolomorphicAnosov.Paper.Zhang.CompactAnosovHermitianOperatorBounds
import HolomorphicAnosov.Geometry.UniformExponentialLift.continuous_metricNorm
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.Algebra.Module.Complement

/-!
# Restricted tangent splitting on bounded sections

Shub, *Global Stability of Dynamical Systems* (1987), pp.72–74: the supplied continuous
splitting over the compact invariant set induces the stable/unstable splitting of all bounded
sections. The proof uses relative bundle frames, continuous oblique projections, a uniform
metric bound, and the genuine dependent supremum-norm carrier. No ambient extension of the
splitting and no manifold structure on the invariant set is assumed.

DAG node: `dynamics.hirsch_pugh_restricted_bounded_splitting_g9`.
-/

noncomputable section
open Set Bundle
open scoped ContDiff Manifold Topology _root_.Topology
namespace HolomorphicAnosov.HirschRestrictedCoordinates

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Relative local coordinate frames of a continuous tangent subbundle on an arbitrary subset.
Source: the local linear trivialization in `ContinuousTangentSubbundleOn` and the ambient
standard tangent chart. Compose the inverse subbundle chart, actual tangent inclusion and
ambient chart. Finite-dimensionality of the model domain promotes pointwise continuity to
operator-norm continuity. This construction neither extends the subbundle off the subset nor
requires the subset to be a manifold. -/
theorem exists_restricted_coordinate_frame {Λ : Set M}
    (S : ContinuousTangentSubbundleOn (E := E) Λ) (x : Λ) :
    ∃ r : ℕ, ∃ O : Set Λ, IsOpen O ∧ x ∈ O ∧
    ∃ (a : Trivialization E (TotalSpace.proj (F := E) (E := TangentSpace 𝓘(ℝ, E)))),
    a = trivializationAt E (TangentSpace 𝓘(ℝ, E)) (x : M) ∧
    ∃ (_ha : a.IsLinear ℝ), ∃ hO : ∀ y ∈ O, (y : M) ∈ a.baseSet,
    ∃ j : O → (Fin r → ℝ) →L[ℝ] E,
      Continuous j ∧ (∀ y, Function.Injective (j y)) ∧
      ∀ y, (j y).toLinearMap.range =
        (S.fibre y.val).map (a.linearEquivAt ℝ (y.val : M) (hO y.val y.property)).toLinearMap := by
  obtain ⟨r, e, hx, he⟩ := S.locally_trivial x
  let : TopologicalSpace (TotalSpace (Fin r → ℝ) (fun y : Λ ↦ ↥(S.fibre y))) :=
    TopologicalSpace.induced
      (fun z ↦ (⟨(z.proj : M), z.snd.val⟩ : TangentBundle 𝓘(ℝ, E) M)) inferInstance
  let := he
  let a := trivializationAt E (TangentSpace 𝓘(ℝ, E)) (x : M)
  let O : Set Λ := e.baseSet ∩ Subtype.val ⁻¹' a.baseSet
  have hO : ∀ y ∈ O, (y : M) ∈ a.baseSet := fun _ hy ↦ hy.2
  let j : O → (Fin r → ℝ) →L[ℝ] E := fun y ↦
    (((a.linearEquivAt ℝ (y.val : M) y.property.2).toLinearMap.comp
      (S.fibre y.val).subtype).comp
      (e.linearEquivAt ℝ y.val y.property.1).symm.toLinearMap).toContinuousLinearMap
  refine ⟨r, O, e.open_baseSet.inter (a.open_baseSet.preimage continuous_subtype_val),
    ⟨hx, mem_baseSet_trivializationAt E (TangentSpace 𝓘(ℝ, E)) (x : M)⟩,
    a, rfl, inferInstance, hO, j, ?_, ?_, ?_⟩
  · apply continuous_clm_apply.mpr
    intro v
    have hframe : Continuous (fun y : O ↦
        (⟨y.val, e.symm y.val v⟩ :
          TotalSpace (Fin r → ℝ) (fun z : Λ ↦ ↥(S.fibre z)))) :=
      e.continuousOn_symm.comp_continuous
        (continuous_subtype_val.prodMk continuous_const)
        (fun y ↦ ⟨y.property.1, mem_univ _⟩)
    have hincl : Continuous (fun y : O ↦
        (⟨(y.val : M), (e.symm y.val v).val⟩ : TangentBundle 𝓘(ℝ, E) M)) :=
      continuous_induced_dom.comp hframe
    have hcoord := (a.continuousOn.comp_continuous hincl
      (fun y ↦ a.mem_source.mpr y.property.2)).snd
    simpa [j, LinearEquiv.coe_coe] using hcoord
  · intro y
    exact (a.linearEquivAt ℝ (y.val : M) y.property.2).injective.comp
      (Subtype.val_injective.comp (e.linearEquivAt ℝ y.val y.property.1).symm.injective)
  · intro y
    change ((((a.linearEquivAt ℝ (y.val : M) y.property.2).toLinearMap.comp
      (S.fibre y.val).subtype).comp
      (e.linearEquivAt ℝ y.val y.property.1).symm.toLinearMap).range) = _
    simp [LinearMap.range_comp]

/-- Complementary subbundles on Λ admit complementary continuous coordinate frames in one
ambient tangent chart. The relative base neighborhoods are intersected and both chart choices
are the standard chart at the same original center. Complementarity is transported by that
linear chart. This is the paired-frame step of Shub's compact-set graph construction. -/
theorem exists_restricted_paired_frames {Λ : Set M}
    (S U : ContinuousTangentSubbundleOn (E := E) Λ)
    (hc : ∀ x, IsCompl (S.fibre x) (U.fibre x)) (x : Λ) :
    ∃ r t : ℕ, ∃ O : Set Λ, IsOpen O ∧ x ∈ O ∧
    ∃ (a : Trivialization E (TotalSpace.proj (F := E) (E := TangentSpace 𝓘(ℝ, E)))),
    ∃ (_ha : a.IsLinear ℝ), ∃ hO : ∀ y ∈ O, (y : M) ∈ a.baseSet,
    ∃ (js : O → (Fin r → ℝ) →L[ℝ] E) (ju : O → (Fin t → ℝ) →L[ℝ] E),
      Continuous js ∧ Continuous ju ∧
      (∀ y, Function.Injective (js y)) ∧ (∀ y, Function.Injective (ju y)) ∧
      (∀ y, (js y).toLinearMap.range = (S.fibre y.val).map
        (a.linearEquivAt ℝ (y.val : M) (hO y.val y.property)).toLinearMap) ∧
      (∀ y, (ju y).toLinearMap.range = (U.fibre y.val).map
        (a.linearEquivAt ℝ (y.val : M) (hO y.val y.property)).toLinearMap) ∧
      ∀ y, IsCompl (js y).toLinearMap.range (ju y).toLinearMap.range := by
  obtain ⟨r, Os, hOs, hxs, a, haeq, ha, hsO, js, hscont, hsinj, hsrange⟩ :=
    exists_restricted_coordinate_frame S x
  obtain ⟨t, Ou, hOu, hxu, b, hbeq, hb, huO, ju, hucont, huinj, hurange⟩ :=
    exists_restricted_coordinate_frame U x
  subst a
  subst b
  let a := trivializationAt E (TangentSpace 𝓘(ℝ, E)) (x : M)
  let O := Os ∩ Ou
  let fs : O → Os := fun y ↦ ⟨y.val, y.property.1⟩
  let fu : O → Ou := fun y ↦ ⟨y.val, y.property.2⟩
  have hfs : Continuous fs := continuous_subtype_val.subtype_mk _
  have hfu : Continuous fu := continuous_subtype_val.subtype_mk _
  have hO : ∀ y ∈ O, (y : M) ∈ a.baseSet := fun _ hy ↦ hsO _ hy.1
  refine ⟨r, t, O, hOs.inter hOu, ⟨hxs, hxu⟩, a, inferInstance, hO,
    js ∘ fs, ju ∘ fu, hscont.comp hfs, hucont.comp hfu,
    fun y ↦ hsinj (fs y), fun y ↦ huinj (fu y), ?_, ?_, ?_⟩
  · intro y
    exact hsrange (fs y)
  · intro y
    exact hurange (fu y)
  · intro y
    dsimp only [Function.comp_apply]
    rw [hsrange (fs y), hurange (fu y)]
    exact Submodule.isCompl_map (a.linearEquivAt ℝ (y.val : M) (hO y.val y.property))
      (hc y.val)

/-- Complementary continuous subbundles over an arbitrary subset have continuous oblique
projections in the original tangent topology, locally over the subset. Use the paired frames,
the existing finite-dimensional projection theorem, and naturality of the algebraic projector.
This is the relative-base version of the compact splitting construction. -/
theorem exists_continuous_restricted_projection {Λ : Set M}
    (S U : ContinuousTangentSubbundleOn (E := E) Λ)
    (hc : ∀ x, IsCompl (S.fibre x) (U.fibre x)) (x : Λ) :
    ∃ O : Set Λ, IsOpen O ∧ x ∈ O ∧
      Continuous (fun z : {z : {z : TangentBundle 𝓘(ℝ, E) M // z.proj ∈ Λ} //
          (⟨z.val.proj, z.property⟩ : Λ) ∈ O} ↦
        (⟨z.val.val.proj, (S.fibre ⟨z.val.val.proj, z.val.property⟩).projection
          (U.fibre ⟨z.val.val.proj, z.val.property⟩)
          (hc ⟨z.val.val.proj, z.val.property⟩) z.val.val.snd⟩ :
            TangentBundle 𝓘(ℝ, E) M)) := by
  obtain ⟨r, t, O, hOopen, hx, a, ha, hO, js, ju,
    hscont, hucont, hsinj, huinj, hsrange, hurange, hcompl⟩ :=
    exists_restricted_paired_frames S U hc x
  let := ha
  let Z := {z : {z : TangentBundle 𝓘(ℝ, E) M // z.proj ∈ Λ} //
    (⟨z.val.proj, z.property⟩ : Λ) ∈ O}
  let base (z : Z) : Λ := ⟨z.val.val.proj, z.val.property⟩
  have hz : Continuous (fun z : Z ↦ z.val.val) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hbase : Continuous (fun z : Z ↦ z.val.val.proj) :=
    (FiberBundle.continuous_proj E (TangentSpace 𝓘(ℝ, E))).comp hz
  have hcoord : Continuous (fun z : Z ↦ (a z.val.val).2) :=
    (a.continuousOn.comp_continuous hz
      (fun z ↦ a.mem_source.mpr (hO (base z) z.property))).snd
  have hinput : Continuous (fun z : Z ↦ ((⟨base z, z.property⟩ : O), (a z.val.val).2)) :=
    ((hbase.subtype_mk _).subtype_mk _).prodMk hcoord
  let P : O × E → E := fun z ↦
    (js z.1).toLinearMap.range.projection (ju z.1).toLinearMap.range (hcompl z.1) z.2
  have hP : Continuous P := NativeSplittingPreparation.continuous_projection_from_frames
    js ju hsinj huinj hcompl hscont hucont
  have hout : Continuous (fun z : Z ↦
      (⟨z.val.val.proj,
        a.symm z.val.val.proj (P (⟨base z, z.property⟩, (a z.val.val).2))⟩ :
        TangentBundle 𝓘(ℝ, E) M)) :=
    a.continuousOn_symm.comp_continuous (hbase.prodMk (hP.comp hinput))
      (fun z ↦ ⟨hO (base z) z.property, mem_univ _⟩)
  refine ⟨O, hOopen, hx, hout.congr ?_⟩
  intro z
  apply congrArg (fun v : TangentSpace 𝓘(ℝ, E) z.val.val.proj ↦
    (⟨z.val.val.proj, v⟩ : TangentBundle 𝓘(ℝ, E) M))
  let y : O := ⟨base z, z.property⟩
  let e := a.linearEquivAt ℝ z.val.val.proj (hO (base z) z.property)
  have hp : P (y, (a z.val.val).2) =
      e ((S.fibre (base z)).projection (U.fibre (base z))
        (hc (base z)) z.val.val.snd) := by
    dsimp only [P]
    simp only [hsrange y, hurange y]
    exact NativeSplittingPreparation.projection_map_apply
      (S.fibre (base z)) (U.fibre (base z)) (hc (base z)) e z.val.val.snd
  rw [hp]
  change e.symm (e _) = _
  exact e.symm_apply_apply _

/-- The oblique projection of a complementary continuous splitting over Λ is continuous
on the whole restricted tangent bundle. Relative open frame neighborhoods cover the base. -/
theorem continuous_restricted_projection {Λ : Set M}
    (S U : ContinuousTangentSubbundleOn (E := E) Λ)
    (hc : ∀ x, IsCompl (S.fibre x) (U.fibre x)) :
    Continuous (fun z : {z : TangentBundle 𝓘(ℝ, E) M // z.proj ∈ Λ} ↦
      (⟨z.val.proj, (S.fibre ⟨z.val.proj, z.property⟩).projection
        (U.fibre ⟨z.val.proj, z.property⟩) (hc ⟨z.val.proj, z.property⟩) z.val.snd⟩ :
          TangentBundle 𝓘(ℝ, E) M)) := by
  let Z := {z : TangentBundle 𝓘(ℝ, E) M // z.proj ∈ Λ}
  have hb : Continuous (fun z : Z ↦ (⟨z.val.proj, z.property⟩ : Λ)) :=
    ((FiberBundle.continuous_proj E (TangentSpace 𝓘(ℝ, E))).comp
      continuous_subtype_val).subtype_mk _
  apply continuous_iff_continuousAt.mpr
  intro z
  obtain ⟨O, hO, hx, hcont⟩ :=
    exists_continuous_restricted_projection S U hc ⟨z.val.proj, z.property⟩
  have hOn : ContinuousOn (fun w : Z ↦
      (⟨w.val.proj, (S.fibre ⟨w.val.proj, w.property⟩).projection
        (U.fibre ⟨w.val.proj, w.property⟩) (hc ⟨w.val.proj, w.property⟩) w.val.snd⟩ :
          TangentBundle 𝓘(ℝ, E) M))
      {w | (⟨w.val.proj, w.property⟩ : Λ) ∈ O} :=
    continuousOn_iff_continuous_domRestrict.mpr hcont
  exact hOn.continuousAt ((hO.preimage hb).mem_nhds hx)

/-- On a compact base the oblique projector is uniformly bounded in any supplied smooth
Riemannian norm. Apply the compact metric-tube lemma to the relative open set where the
projected norm is below one, then rescale. This proves the uniform bound needed for the
bounded-section splitting in Shub's construction, without a global frame or an ambient
extension of either subbundle. -/
theorem exists_uniform_restricted_projection_bound {Λ : Set M} (hΛ : IsCompact Λ)
    (S U : ContinuousTangentSubbundleOn (E := E) Λ)
    (hc : ∀ x, IsCompl (S.fibre x) (U.fibre x))
    (h : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : Λ) (v : TangentSpace 𝓘(ℝ, E) (x : M)),
      hyperbolicRiemannianNorm h ((S.fibre x).projection (U.fibre x) (hc x) v) ≤
        C * hyperbolicRiemannianNorm h v := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨h.toContinuousRiemannianMetric.toRiemannianMetric⟩
  have hn (x : M) (v : TangentSpace 𝓘(ℝ, E) x) :
      hyperbolicRiemannianNorm h v = ‖v‖ := by rfl
  let Z := {z : TangentBundle 𝓘(ℝ, E) M // z.proj ∈ Λ}
  let P (x : Λ) := (S.fibre x).projection (U.fibre x) (hc x)
  let F : Z → ℝ := fun z ↦ hyperbolicRiemannianNorm h
    (P ⟨z.val.proj, z.property⟩ z.val.snd)
  have hF : Continuous F :=
    (ExponentialLift.continuous_metricNorm h).comp (continuous_restricted_projection S U hc)
  obtain ⟨Ω, hΩ, heq⟩ := isOpen_induced_iff.mp (isOpen_Iio.preimage hF)
  have hzero : ∀ p ∈ Λ, (⟨p, 0⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ Ω := by
    intro p hp
    change (⟨⟨p, 0⟩, hp⟩ : Z) ∈ Subtype.val ⁻¹' Ω
    rw [heq]
    change F ⟨⟨p, 0⟩, hp⟩ < 1
    simp [F, P, hn]
  obtain ⟨V, ε, hV, hε, htube⟩ :=
    ExponentialLift.compact_metric_tube h hΩ Λ hΛ hzero
  refine ⟨2 / ε, div_pos (by norm_num) hε, ?_⟩
  intro x v
  rw [hn, hn]
  by_cases hv : v = 0
  · simp [hv]
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let c : ℝ := ε / (2 * ‖v‖)
  have hcpos : 0 < c := div_pos hε (mul_pos (by norm_num) hvpos)
  have hncv : ‖c • v‖ = ε / 2 := by
    rw [norm_smul, Real.norm_of_nonneg hcpos.le]
    dsimp [c]
    field_simp
  have hcv : (⟨(x : M), c • v⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ Ω :=
    htube ⟨hV x.property, by
      change hyperbolicRiemannianNorm h (c • v) < ε
      rw [hn, hncv]
      linarith⟩
  have hsmall : ‖P x (c • v)‖ < 1 := by
    have hz : (⟨⟨(x : M), c • v⟩, x.property⟩ : Z) ∈ Subtype.val ⁻¹' Ω := hcv
    rw [heq] at hz
    exact hz
  rw [map_smul, norm_smul, Real.norm_of_nonneg hcpos.le] at hsmall
  have hbound : ‖P x v‖ < 1 / c :=
    (lt_div_iff₀ hcpos).mpr (by simpa only [mul_comm] using hsmall)
  have he : 1 / c = (2 / ε) * ‖v‖ := by dsimp [c]; field_simp
  rw [he] at hbound
  exact hbound.le

/-- The original fibre projector acts as a bounded linear map on all bounded dependent
sections over Λ, including discontinuous sections. This is Shub's bounded-section splitting
operator, using the actual metric and fibres. The uniform projector bound supplies the supremum
norm estimate. -/
theorem exists_bounded_section_projection {Λ : Set M} (hΛ : IsCompact Λ)
    (S U : ContinuousTangentSubbundleOn (E := E) Λ)
    (hc : ∀ x, IsCompl (S.fibre x) (U.fibre x))
    (h : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _)) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
      ⟨h.toContinuousRiemannianMetric.toRiemannianMetric⟩
    ∃ P : lp (fun x : Λ ↦ TangentSpace 𝓘(ℝ, E) (x : M)) ⊤ →L[ℝ]
        lp (fun x : Λ ↦ TangentSpace 𝓘(ℝ, E) (x : M)) ⊤,
      ∀ s x, P s x = (S.fibre x).projection (U.fibre x) (hc x) (s x) := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨h.toContinuousRiemannianMetric.toRiemannianMetric⟩
  obtain ⟨C, hC, hb⟩ := exists_uniform_restricted_projection_bound hΛ S U hc h
  let B := lp (fun x : Λ ↦ TangentSpace 𝓘(ℝ, E) (x : M)) ⊤
  let p (x : Λ) := (S.fibre x).projection (U.fibre x) (hc x)
  have hb' (x : Λ) (v : TangentSpace 𝓘(ℝ, E) (x : M)) : ‖p x v‖ ≤ C * ‖v‖ := hb x v
  let P : B → B := fun s ↦ ⟨fun x ↦ p x (s x), memℓp_infty
    ⟨C * ‖s‖, by
      rintro _ ⟨x, rfl⟩
      exact (hb' x (s x)).trans
        (mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm ENNReal.top_ne_zero s x) hC.le)⟩⟩
  let L : B →ₗ[ℝ] B :=
    { toFun := P
      map_add' := by
        intro s t
        ext x
        exact (p x).map_add (s x) (t x)
      map_smul' := by
        intro c s
        ext x
        exact (p x).map_smul c (s x) }
  have hbL (s : B) : ‖L s‖ ≤ C * ‖s‖ :=
    lp.norm_le_of_forall_le (mul_nonneg hC.le (norm_nonneg s)) (fun x ↦
      (hb' x (s x)).trans
        (mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm ENNReal.top_ne_zero s x) hC.le))
  exact ⟨L.mkContinuous C hbL, fun _ _ ↦ rfl⟩

/-- The submodule of bounded dependent sections taking values in the given fibres. -/
def boundedSectionSubmodule {A : Type*} {V : A → Type*}
    [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
    (S : ∀ x, Submodule ℝ (V x)) : Submodule ℝ (lp V ⊤) where
  carrier := {s | ∀ x, s x ∈ S x}
  zero_mem' := fun x ↦ (S x).zero_mem
  add_mem' := fun hs ht x ↦ (S x).add_mem (hs x) (ht x)
  smul_mem' := fun c _ hs x ↦ (S x).smul_mem c (hs x)

/-- The stable and unstable bounded-section spaces are topological complements.
This is the Banach splitting used in Shub p.74: arbitrary bounded sections are allowed,
the base is Λ, and the norm is the supplied metric's supremum norm. The projector is
idempotent; its range and kernel are exactly the two original fibrewise section spaces.
Mathlib then supplies their closedness and the continuous linear product equivalence. -/
theorem bounded_sections_split {Λ : Set M} (hΛ : IsCompact Λ)
    (S U : ContinuousTangentSubbundleOn (E := E) Λ)
    (hc : ∀ x, IsCompl (S.fibre x) (U.fibre x))
    (h : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _)) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
      ⟨h.toContinuousRiemannianMetric.toRiemannianMetric⟩
    Submodule.IsTopCompl (boundedSectionSubmodule S.fibre) (boundedSectionSubmodule U.fibre) := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨h.toContinuousRiemannianMetric.toRiemannianMetric⟩
  let B := lp (fun x : Λ ↦ TangentSpace 𝓘(ℝ, E) (x : M)) ⊤
  obtain ⟨Ps, hPs⟩ := exists_bounded_section_projection hΛ S U hc h
  have hidem : IsIdempotentElem Ps := by
    ext s x
    change Ps (Ps s) x = Ps s x
    simp only [hPs]
    exact Submodule.projection_apply_of_mem_left (hc x)
      (Submodule.projection_apply_mem (hc x) (s x))
  have hrange : Ps.range = boundedSectionSubmodule S.fibre := by
    ext s
    constructor
    · rintro ⟨t, rfl⟩ x
      change Ps t x ∈ S.fibre x
      rw [hPs]
      exact Submodule.projection_apply_mem (hc x) (t x)
    · intro hs
      refine ⟨s, ?_⟩
      ext x
      change Ps s x = s x
      rw [hPs]
      exact Submodule.projection_apply_of_mem_left (hc x) (hs x)
  have hker : Ps.ker = boundedSectionSubmodule U.fibre := by
    ext s
    change Ps s = 0 ↔ ∀ x, s x ∈ U.fibre x
    constructor
    · intro hs x
      have hx : Ps s x = 0 := congrArg (fun t : B ↦ t x) hs
      rw [hPs] at hx
      exact (Submodule.projection_apply_eq_zero_iff (hc x)).mp hx
    · intro hs
      ext x
      change Ps s x = 0
      rw [hPs]
      exact (Submodule.projection_apply_eq_zero_iff (hc x)).mpr (hs x)
  rw [← hrange, ← hker]
  exact ContinuousLinearMap.IsIdempotentElem.isTopCompl hidem

end HolomorphicAnosov.HirschRestrictedCoordinates
