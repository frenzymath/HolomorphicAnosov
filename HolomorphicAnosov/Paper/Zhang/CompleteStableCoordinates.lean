import HolomorphicAnosov.Geometry.NativeCompleteChartFamilyContinuity
import HolomorphicAnosov.Geometry.NormalizedLocalCoordinateContinuousG5
import HolomorphicAnosov.Topology.CompactDiagonalFamilySmallness
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine.ContinuousTangentScale
import HolomorphicAnosov.Geometry.HermitianLeafPathMap
import HolomorphicAnosov.Geometry.DiffeomorphOfExhaustion
import HolomorphicAnosov.Geometry.PartialChartComponentEntry
import HolomorphicAnosov.Topology.CompactDiagonalSmallness
import HolomorphicAnosov.Geometry.ComplexToRealMap
import HolomorphicAnosov.Paper.Zhang.StableFoliationsForwardAsymptoticApplyIff
import HolomorphicAnosov.Geometry.Biholomorph
import HolomorphicAnosov.Geometry.NativeComplexStableLeafDatum
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import HolomorphicAnosov.Topology.Franks.IntrinsicLeafMetricBounds
import HolomorphicAnosov.Geometry.ComplexToRealManifold
import HolomorphicAnosov.Geometry.HermitianLeafPathDistance
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.OriginalAllIteratesHermitian
import Mathlib.Analysis.SpecificLimits.Basic
import HolomorphicAnosov.Paper.Zhang.CompactAnosovHermitianOperatorBounds
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.OriginalSmoothTangentMetricExists
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousComplexTangentSubbundle
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine
import HolomorphicAnosov.Paper.Zhang.LocalLinearization
import HolomorphicAnosov.Paper.Zhang.StableFoliations
import HolomorphicAnosov.Paper.Zhang.UniformLocalStableCoordinates
import HolomorphicAnosov.Geometry.NormalizedLocalStableCoordinate
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientLineConnection
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ComplexTangentRankOne
import Mathlib.Geometry.Manifold.Metrizable
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Analysis.Normed.Group.Submodule

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-! Linear changes of chart models, stable-leaf transport, and contraction of intrinsic Hermitian
distances. (Zhang, Lemma 2.7, eq. (18)) -/

open Set
open scoped ContDiff Manifold

namespace HolomorphicAnosov.CompleteStableCoordinatesScratch

variable {E E' M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace M] [ChartedSpace E M]

/-- The charted-space structure obtained by postcomposing each chart with a continuous linear
equivalence. -/
@[instance_reducible]
def rechart (e : E ≃L[ℝ] E') : ChartedSpace E' M where
  atlas := (fun a : OpenPartialHomeomorph M E ↦ a.transHomeomorph e.toHomeomorph) ''
    atlas E M
  chartAt x := (chartAt E x).transHomeomorph e.toHomeomorph
  mem_chart_source x := ChartedSpace.mem_chart_source x
  chart_mem_atlas x := mem_image_of_mem _ (ChartedSpace.chart_mem_atlas x)

theorem rechart_isManifold (e : E ≃L[ℝ] E') [IsManifold 𝓘(ℝ, E) ∞ M] :
    letI := rechart (M := M) e
    IsManifold 𝓘(ℝ, E') ∞ M := by
  letI := rechart (M := M) e
  apply isManifold_of_contDiffOn
  rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
  have h := ((contDiffGroupoid ∞ 𝓘(ℝ, E)).compatible ha hb).1
  simp only [contDiffPregroupoid, mfld_simps] at h
  have hc := e.contDiff.comp_contDiffOn
    (h.comp e.symm.contDiff.contDiffOn (Set.mapsTo_preimage _ _))
  simp only [mfld_simps]
  convert hc using 1
  · rfl
  · rfl

theorem rechart_identity_diffeomorph_exists (e : E ≃L[ℝ] E') [IsManifold 𝓘(ℝ, E) ∞ M] :
    letI := rechart (M := M) e
    ∃ a : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E') M M ∞, ∀ x, a x = x := by
  letI := rechart (M := M) e
  refine ⟨{ toEquiv := Equiv.refl M
            contMDiff_toFun := ?_
            contMDiff_invFun := ?_ }, fun _ ↦ rfl⟩
  · intro x
    refine contMDiffAt_iff.2 ⟨continuousAt_id, ?_⟩
    apply e.contDiff.contDiffWithinAt.congr_of_eventuallyEq
    · filter_upwards [mem_nhdsWithin_of_mem_nhds (chart_target_mem_nhds E x)] with y hy
      change e ((chartAt E x) ((chartAt E x).symm y)) = e y
      rw [(chartAt E x).right_inv hy]
    · change e ((chartAt E x) ((chartAt E x).symm ((chartAt E x) x))) = e ((chartAt E x) x)
      rw [(chartAt E x).right_inv (mem_chart_target E x)]
  · intro x
    refine contMDiffAt_iff.2 ⟨continuousAt_id, ?_⟩
    apply e.symm.contDiff.contDiffWithinAt.congr_of_eventuallyEq
    · filter_upwards [mem_nhdsWithin_of_mem_nhds (chart_target_mem_nhds E' x)] with y hy
      change (chartAt E x) ((chartAt E x).symm (e.symm y)) = e.symm y
      change e.symm y ∈ (chartAt E x).target at hy
      exact (chartAt E x).right_inv hy
    · change (chartAt E x) ((chartAt E x).symm (e.symm (e ((chartAt E x) x)))) =
        e.symm (e ((chartAt E x) x))
      rw [e.symm_apply_apply, (chartAt E x).right_inv (mem_chart_target E x)]

/-- Postcomposition by a continuous linear equivalence carries maximal-atlas charts into the
recharted maximal atlas. -/
theorem rechart_maximalAtlas (e : E ≃L[ℝ] E') [IsManifold 𝓘(ℝ, E) ∞ M]
    (a : OpenPartialHomeomorph M E) (ha : a ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) :
    letI := rechart (M := M) e
    a.transHomeomorph e.toHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℝ, E') ∞ M := by
  letI := rechart (M := M) e
  intro _ hb
  obtain ⟨b, hb, rfl⟩ := hb
  have transform (c t : OpenPartialHomeomorph M E)
      (hct : c.symm.trans t ∈ contDiffGroupoid ∞ 𝓘(ℝ, E)) :
      (c.transHomeomorph e.toHomeomorph).symm.trans
        (t.transHomeomorph e.toHomeomorph) ∈ contDiffGroupoid ∞ 𝓘(ℝ, E') := by
    constructor
    · have h := hct.1
      simp only [contDiffPregroupoid, mfld_simps] at h ⊢
      have hc := e.contDiff.comp_contDiffOn
        (h.comp e.symm.contDiff.contDiffOn (Set.mapsTo_preimage _ _))
      convert hc using 1 <;> rfl
    · have h := hct.2
      simp only [contDiffPregroupoid, mfld_simps] at h ⊢
      have hc := e.contDiff.comp_contDiffOn
        (h.comp e.symm.contDiff.contDiffOn (Set.mapsTo_preimage _ _))
      convert hc using 1 <;> rfl
  exact ⟨transform _ _ (ha b hb).1, transform _ _ (ha b hb).2⟩

variable {G G' N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup G'] [NormedSpace ℝ G'] [TopologicalSpace N] [ChartedSpace G N]

/-- Immersions remain immersions under continuous linear changes of the source and target chart
models. -/
theorem rechart_isImmersionAt (e : E ≃L[ℝ] E') (g : G ≃L[ℝ] G')
    [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, G) ∞ N]
    {f : M → N} {x : M} (h : Manifold.IsImmersionAt 𝓘(ℝ, E) 𝓘(ℝ, G) ∞ f x) :
    letI := rechart (M := M) e
    letI := rechart (M := N) g
    Manifold.IsImmersionAt 𝓘(ℝ, E') 𝓘(ℝ, G') ∞ f x := by
  letI := rechart (M := M) e
  letI := rechart (M := N) g
  let k := h.isImmersionAtOfComplement_complement
  apply Manifold.IsImmersionAt.mk_of_charts
    (((e.symm.prodCongr (ContinuousLinearEquiv.refl ℝ h.complement)).trans k.equiv).trans g)
    (k.domChart.transHomeomorph e.toHomeomorph)
    (k.codChart.transHomeomorph g.toHomeomorph)
    k.mem_domChart_source k.mem_codChart_source
    (rechart_maximalAtlas e k.domChart k.domChart_mem_maximalAtlas)
    (rechart_maximalAtlas g k.codChart k.codChart_mem_maximalAtlas)
    k.source_subset_preimage_source
  intro y hy
  have hy' : e.symm y ∈ (k.domChart.extend 𝓘(ℝ, E)).target := by
    simp only [mfld_simps] at hy ⊢
    change e.symm y ∈ k.domChart.target at hy
    exact hy
  have hk := k.writtenInCharts hy'
  change g (k.codChart (f (k.domChart.symm (e.symm y)))) =
    g (k.equiv (e.symm y, 0))
  exact congrArg g hk


/-- The identity from the original atlas to the recharted atlas has derivative `e`. -/
theorem rechart_identity_hasMFDerivAt (e : E ≃L[ℝ] E') (x : M) :
    letI := rechart (M := M) e
    HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E') (id : M → M) x e.toContinuousLinearMap := by
  letI := rechart (M := M) e
  refine ⟨continuousAt_id, ?_⟩
  change HasFDerivWithinAt _ e.toContinuousLinearMap _ _
  apply e.hasFDerivAt.hasFDerivWithinAt.congr_of_eventuallyEq
  · filter_upwards [mem_nhdsWithin_of_mem_nhds (chart_target_mem_nhds E x)] with y hy
    change e ((chartAt E x) ((chartAt E x).symm y)) = e y
    rw [(chartAt E x).right_inv hy]
  · change e ((chartAt E x) ((chartAt E x).symm ((chartAt E x) x))) = e ((chartAt E x) x)
    rw [(chartAt E x).right_inv (mem_chart_target E x)]

/-- The identity from the recharted atlas to the original atlas has derivative `e.symm`. -/
theorem rechart_identity_symm_hasMFDerivAt (e : E ≃L[ℝ] E') (x : M) :
    letI := rechart (M := M) e
    HasMFDerivAt 𝓘(ℝ, E') 𝓘(ℝ, E) (id : M → M) x e.symm.toContinuousLinearMap := by
  letI := rechart (M := M) e
  refine ⟨continuousAt_id, ?_⟩
  change HasFDerivWithinAt _ e.symm.toContinuousLinearMap _ _
  apply e.symm.hasFDerivAt.hasFDerivWithinAt.congr_of_eventuallyEq
  · filter_upwards [mem_nhdsWithin_of_mem_nhds (chart_target_mem_nhds E' x)] with y hy
    change (chartAt E x) ((chartAt E x).symm (e.symm y)) = e.symm y
    change e.symm y ∈ (chartAt E x).target at hy
    exact (chartAt E x).right_inv hy
  · change (chartAt E x) ((chartAt E x).symm (e.symm (e ((chartAt E x) x)))) =
      e.symm (e ((chartAt E x) x))
    rw [e.symm_apply_apply, (chartAt E x).right_inv (mem_chart_target E x)]


/-- The derivative in the recharted atlases is the original derivative conjugated by the source and
target linear equivalences. -/
theorem rechart_mfderiv (e : E ≃L[ℝ] E') (g : G ≃L[ℝ] G')
    {f : M → N} {x : M} (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, G) f x) :
    letI := rechart (M := M) e
    letI := rechart (M := N) g
    mfderiv 𝓘(ℝ, E') 𝓘(ℝ, G') f x =
      g.toContinuousLinearMap.comp
        ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, G) f x).comp e.symm.toContinuousLinearMap) := by
  letI := rechart (M := M) e
  letI := rechart (M := N) g
  have hpre := hf.hasMFDerivAt.comp x (rechart_identity_symm_hasMFDerivAt e x)
  have hpost := (rechart_identity_hasMFDerivAt g (f x)).comp x hpre
  exact hpost.mfderiv


/-- The range of the recharted derivative is the image of the original derivative range under the
target linear equivalence. -/
theorem rechart_mfderiv_range (e : E ≃L[ℝ] E') (g : G ≃L[ℝ] G')
    {f : M → N} {x : M} (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, G) f x) :
    letI := rechart (M := M) e
    letI := rechart (M := N) g
    (mfderiv 𝓘(ℝ, E') 𝓘(ℝ, G') f x).range =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, G) f x).range.map g.toLinearMap := by
  letI := rechart (M := M) e
  letI := rechart (M := N) g
  rw [rechart_mfderiv e g hf]
  let A : E →L[ℝ] G := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, G) f x
  change (g.toLinearMap.comp (A.toLinearMap.comp e.symm.toLinearMap)).range =
    A.range.map g.toLinearMap
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    exact Submodule.mem_map.mpr ⟨_, ⟨e.symm w, rfl⟩, rfl⟩
  · intro hv
    obtain ⟨u, ⟨w, hw⟩, hu⟩ := Submodule.mem_map.mp hv
    refine ⟨e w, ?_⟩
    change g (A (e.symm (e w))) = v
    rw [e.symm_apply_apply]
    change A w = u at hw
    rw [hw]
    exact hu


/-- A smooth immersion is a C¹ immersion. -/
theorem immersion_at_one_of_infty [IsManifold 𝓘(ℝ, E) ∞ M]
    [IsManifold 𝓘(ℝ, G) ∞ N] {f : M → N} {x : M}
    (h : Manifold.IsImmersionAt 𝓘(ℝ, E) 𝓘(ℝ, G) ∞ f x) :
    Manifold.IsImmersionAt 𝓘(ℝ, E) 𝓘(ℝ, G) 1 f x := by
  let k := h.isImmersionAtOfComplement_complement
  exact Manifold.IsImmersionAt.mk_of_charts k.equiv k.domChart k.codChart
    k.mem_domChart_source k.mem_codChart_source
    (IsManifold.maximalAtlas_subset_of_le (by simp) k.domChart_mem_maximalAtlas)
    (IsManifold.maximalAtlas_subset_of_le (by simp) k.codChart_mem_maximalAtlas)
    k.source_subset_preimage_source k.writtenInCharts

/-- A smooth map remains smooth under continuous linear changes of its source and target chart
models. -/
theorem rechart_contMDiff (e : E ≃L[ℝ] E') (g : G ≃L[ℝ] G')
    [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, G) ∞ N]
    {f : M → N} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, G) ∞ f) :
    letI := rechart (M := M) e
    letI := rechart (M := N) g
    ContMDiff 𝓘(ℝ, E') 𝓘(ℝ, G') ∞ f := by
  letI := rechart (M := M) e
  letI := rechart (M := N) g
  obtain ⟨a, ha⟩ := rechart_identity_diffeomorph_exists (M := M) e
  obtain ⟨b, hb⟩ := rechart_identity_diffeomorph_exists (M := N) g
  have hai : ∀ x, a.symm x = x := by
    intro x
    simpa only [ha] using a.apply_symm_apply x
  exact (b.contMDiff.comp (hf.comp a.symm.contMDiff)).congr
    (fun x ↦ by simp only [Function.comp_apply, hai, hb])

/-- The identity on an open plaque is a diffeomorphism between its original and recharted atlases. -/
theorem rechart_open_identity (e : E ≃L[ℝ] E')
    [IsManifold 𝓘(ℝ, E) ∞ M] (U : TopologicalSpace.Opens M) :
    letI old : ChartedSpace E U := inferInstance
    letI := rechart (M := M) e
    ∃ a : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E') U U ∞, ∀ x, a x = x := by
  letI old : ChartedSpace E U := inferInstance
  letI := rechart (M := M) e
  obtain ⟨a, ha⟩ := rechart_identity_diffeomorph_exists (M := M) e
  have hai : ∀ x, a.symm x = x := by
    intro x
    simpa only [ha] using a.apply_symm_apply x
  refine ⟨{ toEquiv := Equiv.refl U
            contMDiff_toFun := ?_
            contMDiff_invFun := ?_ }, fun _ ↦ rfl⟩
  · apply (ContMDiff.subtypeVal_comp_iff U _).mp
    exact (a.contMDiff.comp (contMDiff_subtype_val (I := 𝓘(ℝ, E)))).congr
      (fun x ↦ by simpa using (ha x.val).symm)
  · apply (ContMDiff.subtypeVal_comp_iff U _).mp
    exact (a.symm.contMDiff.comp (contMDiff_subtype_val (I := 𝓘(ℝ, E')))).congr
      (fun x ↦ by simpa using (hai x.val).symm)

/-- The diffeomorphism between corresponding open sets induced by the inverse of a continuous linear
equivalence. -/
noncomputable def discChange (e : E ≃L[ℝ] E') (U : TopologicalSpace.Opens E) :
    Diffeomorph 𝓘(ℝ, E') 𝓘(ℝ, E)
      (⟨e.symm ⁻¹' U, U.isOpen.preimage e.symm.continuous⟩ : TopologicalSpace.Opens E') U ∞ where
  toEquiv :=
    { toFun := fun x ↦ ⟨e.symm x, x.property⟩
      invFun := fun x ↦ ⟨e x, by simp⟩
      left_inv := fun x ↦ Subtype.ext (e.apply_symm_apply x)
      right_inv := fun x ↦ Subtype.ext (e.symm_apply_apply x) }
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff U _).mp
    exact (e.symm.contDiff.contMDiff).comp contMDiff_subtype_val
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff _ _).mp
    exact (e.contDiff.contMDiff).comp contMDiff_subtype_val

section Adapter
universe u
variable {n r : ℕ} {P : Type u} [TopologicalSpace P] [ChartedSpace E P]
  [IsManifold 𝓘(ℝ, E) ∞ P]
  {ι : Type u} {L : ι → Type u} [∀ i, TopologicalSpace (L i)]
  [∀ i, ChartedSpace (Fin r → ℝ) (L i)]
  [∀ i, IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ (L i)]
  {D : RealTangentDistribution 𝓘(ℝ, E) P}

/-- An HPS product box expressed in real Euclidean chart models. -/
noncomputable def franksBox (e : E ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (F : HPS.LeafPartition D ι L (fun _ ↦ r))
    {T : Type u} [TopologicalSpace T] (B : HPS.NativeProductBox F r T) :
    letI := rechart (M := P) e
    letI := rechart_isManifold (M := P) e
    letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin r)) (L i) :=
      fun i ↦ rechart (M := L i) (EuclideanSpace.equiv (Fin r) ℝ).symm
    letI : ∀ i, IsManifold (𝓡 r) ∞ (L i) :=
      fun i ↦ rechart_isManifold (M := L i) (EuclideanSpace.equiv (Fin r) ℝ).symm
    Franks.LeafBox (n := n) (r := r) (fun i ↦ (F.leaf i).inclusion) := by
  let c := (EuclideanSpace.equiv (Fin r) ℝ).symm
  letI := rechart (M := P) e
  letI := rechart_isManifold (M := P) e
  letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin r)) (L i) :=
    fun i ↦ rechart (M := L i) c
  letI : ∀ i, IsManifold (𝓡 r) ∞ (L i) :=
    fun i ↦ rechart_isManifold (M := L i) c
  let q := discChange c B.disc
  have hA := fun t ↦ rechart_open_identity (M := L (B.label t)) c (B.plaque t)
  let A := fun t ↦ Classical.choose (hA t)
  have hAeq : ∀ t x, A t x = x := fun t ↦ Classical.choose_spec (hA t)
  let C := fun t ↦ (q.trans (B.chart t)).trans (A t)
  exact
    { transversal := T
      disc := ⟨c.symm ⁻¹' B.disc, B.disc.isOpen.preimage c.symm.continuous⟩
      ambient := B.ambient
      box := (q.toHomeomorph.prodCongr (Homeomorph.refl T)).trans B.box
      label := B.label
      plaque := B.plaque
      chart := fun t ↦
        { toEquiv := (C t).toEquiv
          contMDiff_toFun := (C t).contMDiff.of_le (by simp)
          contMDiff_invFun := (C t).symm.contMDiff.of_le (by simp) }
      intertwining := by
        intro t z
        change (B.box (q z, t) : P) = (F.leaf (B.label t)).inclusion (A t (B.chart t (q z)))
        rw [hAeq]
        exact B.factorization t (q z) }

/-- An HPS leaf partition with product boxes expressed as a Franks leaf foliation in real Euclidean
models. -/
noncomputable def franksFoliation (e : E ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (F : HPS.LeafPartition D ι L (fun _ ↦ r))
    {β : Type u} {T : β → Type u} [∀ b, TopologicalSpace (T b)]
    (B : HPS.LaminationBoxes F β (fun _ ↦ r) T) :
    letI := rechart (M := P) e
    letI := rechart_isManifold (M := P) e
    letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin r)) (L i) :=
      fun i ↦ rechart (M := L i) (EuclideanSpace.equiv (Fin r) ℝ).symm
    letI : ∀ i, IsManifold (𝓡 r) ∞ (L i) :=
      fun i ↦ rechart_isManifold (M := L i) (EuclideanSpace.equiv (Fin r) ℝ).symm
    Franks.LeafFoliation (n := n) (r := r) (ι := ι) (L := L) (fun x ↦ (D x).map e.toLinearMap) := by
  let c := (EuclideanSpace.equiv (Fin r) ℝ).symm
  letI := rechart (M := P) e
  letI := rechart_isManifold (M := P) e
  letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin r)) (L i) :=
    fun i ↦ rechart (M := L i) c
  letI : ∀ i, IsManifold (𝓡 r) ∞ (L i) :=
    fun i ↦ rechart_isManifold (M := L i) c
  refine
    { inclusion := fun i ↦ (F.leaf i).inclusion
      injective := fun i ↦ (F.leaf i).injective
      immersion := ?_
      tangent := ?_
      connected := fun i ↦ (F.leaf i).connected
      hausdorff := fun i ↦ (F.leaf i).hausdorff
      second_countable := fun i ↦ (F.leaf i).countable
      cover := F.cover
      disjoint := F.disjoint
      box_cover := ?_ }
  · intro i x
    exact immersion_at_one_of_infty
      (rechart_isImmersionAt c e ((F.leaf i).immersion.isImmersionAt x))
  · intro i x
    rw [rechart_mfderiv_range c e
      (((F.leaf i).immersion.isImmersionAt x).contMDiffAt.mdifferentiableAt (by simp))]
    rw [(F.leaf i).tangent x]
    rfl
  · intro p
    obtain ⟨b, hb⟩ := B.cover p
    exact ⟨franksBox e F (B.boxes b), hb⟩


end Adapter

section NativeSpecialization
universe u
variable {d : ℕ} {X : Type u} [MetricSpace X] [ChartedSpace (ComplexModel d) X]
  [IsManifold (complexModel d) ∞ X]
  {ι : Type u} {L : ι → Type u} [∀ i, TopologicalSpace (L i)]
  [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
  [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]

/-- A continuous real linear equivalence between `ComplexModel d` and real Euclidean space of
dimension `2 * d`. -/
noncomputable def stableAmbientCLE (d : ℕ) :
    ComplexModel d ≃L[ℝ] EuclideanSpace ℝ (Fin (2 * d)) := by
  letI : ContinuousSMul ℝ (EuclideanSpace ℝ (Fin (2 * d))) := IsBoundedSMul.continuousSMul
  exact ContinuousLinearEquiv.ofFinrankEq (by simp [ComplexModel, finrank_real_of_complex])

/-- The Franks leaf foliation associated with a complex stable-leaf datum by real linear changes of
model. -/
noncomputable def nativeFranksFoliation {f : X ≃ₜ X}
    {S : ContinuousComplexTangentSubbundle (complexModel d) X}
    (F : NativeComplexStableLeafDatum f S ι L) :
    letI := complex_isManifold_real d X
    letI := rechart (M := X) (stableAmbientCLE d)
    letI := rechart_isManifold (M := X) (stableAmbientCLE d)
    letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 2)) (L i) :=
      fun i ↦ rechart (M := L i) (EuclideanSpace.equiv (Fin 2) ℝ).symm
    letI : ∀ i, IsManifold (𝓡 2) ∞ (L i) :=
      fun i ↦ rechart_isManifold (M := L i) (EuclideanSpace.equiv (Fin 2) ℝ).symm
    Franks.LeafFoliation (n := 2 * d) (r := 2) (ι := ι) (L := L)
      (fun x ↦ (complexStableRealDistribution S x).map (stableAmbientCLE d).toLinearMap) := by
  letI := complex_isManifold_real d X
  letI := F.transversalTopology
  exact franksFoliation (stableAmbientCLE d) F.partition F.boxes


/-- A map between stable leaves is continuous when its composition with the target leaf inclusion is
continuous. -/
theorem native_leaf_map_continuous {f : X ≃ₜ X}
    {S : ContinuousComplexTangentSubbundle (complexModel d) X}
    (F : NativeComplexStableLeafDatum f S ι L) (i j : ι) (q : L i → L j)
    (hq : Continuous ((F.partition.leaf j).inclusion ∘ q)) : Continuous q := by
  letI := complex_isManifold_real d X
  letI := rechart (M := X) (stableAmbientCLE d)
  letI := rechart_isManifold (M := X) (stableAmbientCLE d)
  letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 2)) (L i) :=
    fun i ↦ rechart (M := L i) (EuclideanSpace.equiv (Fin 2) ℝ).symm
  letI : ∀ i, IsManifold (𝓡 2) ∞ (L i) :=
    fun i ↦ rechart_isManifold (M := L i) (EuclideanSpace.equiv (Fin 2) ℝ).symm
  exact Franks.leaf_map_continuous_of_inclusion (nativeFranksFoliation F) i j q hq


end NativeSpecialization

end HolomorphicAnosov.CompleteStableCoordinatesScratch

open Set
open scoped Manifold ContDiff

namespace HolomorphicAnosov

universe u

/-- Each forward iterate induces a bijection between stable leaves that commutes with their
inclusions. (Zhang, Lemma 2.7, eq. (18)) -/
theorem nativeStableLeaf_iterate_equiv
    {d : ℕ} {M : Type u} [MetricSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (f : M ≃ₜ M) (S : ContinuousComplexTangentSubbundle (complexModel d) M)
    {ι : Type u} {L : ι → Type u}
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
    (F : NativeComplexStableLeafDatum f S ι L)
    (i : ι) (z : L i) (n : ℕ) :
    ∃ j, ∃ e : L i ≃ L j, ∀ p,
      (F.partition.leaf j).inclusion (e p) =
        (f : M → M)^[n] ((F.partition.leaf i).inclusion p) := by
  classical
  induction n with
  | zero => exact ⟨i, Equiv.refl _, fun _ ↦ rfl⟩
  | succ n ih =>
    obtain ⟨j, e, he⟩ := ih
    obtain ⟨k, w, hw⟩ := F.partition.cover (f ((F.partition.leaf j).inclusion (e z)))
    have hforward (p : L j) : ∃ q : L k,
        (F.partition.leaf k).inclusion q = f ((F.partition.leaf j).inclusion p) := by
      have hp : ForwardAsymptotic f ((F.partition.leaf j).inclusion (e z))
          ((F.partition.leaf j).inclusion p) := by
        have hp : (F.partition.leaf j).inclusion p ∈
            Set.range (F.partition.leaf j).inclusion := ⟨p, rfl⟩
        rw [F.asymptotic j (e z)] at hp
        exact hp
      have hfp := (StableFoliationsSupport.forwardAsymptotic_apply_iff f _ _).mpr hp
      rw [← hw] at hfp
      change f ((F.partition.leaf j).inclusion p) ∈
        {y | ForwardAsymptotic f ((F.partition.leaf k).inclusion w) y} at hfp
      rw [← F.asymptotic k w] at hfp
      exact hfp
    choose g hg using hforward
    have hginj : Function.Injective g := by
      intro p q hpq
      apply (F.partition.leaf j).injective
      apply f.injective
      rw [← hg p, ← hg q, hpq]
    have hgsurj : Function.Surjective g := by
      intro q
      have hq : ForwardAsymptotic f ((F.partition.leaf k).inclusion w)
          ((F.partition.leaf k).inclusion q) := by
        have hq : (F.partition.leaf k).inclusion q ∈
            Set.range (F.partition.leaf k).inclusion := ⟨q, rfl⟩
        rw [F.asymptotic k w] at hq
        exact hq
      rw [hw] at hq
      have hp : ForwardAsymptotic f ((F.partition.leaf j).inclusion (e z))
          (f.symm ((F.partition.leaf k).inclusion q)) := by
        apply (StableFoliationsSupport.forwardAsymptotic_apply_iff f _ _).mp
        simpa only [f.apply_symm_apply] using hq
      change f.symm ((F.partition.leaf k).inclusion q) ∈
        {y | ForwardAsymptotic f ((F.partition.leaf j).inclusion (e z)) y} at hp
      rw [← F.asymptotic j (e z)] at hp
      obtain ⟨p, hp⟩ := hp
      refine ⟨p, (F.partition.leaf k).injective ?_⟩
      rw [hg p, hp, f.apply_symm_apply]
    refine ⟨k, e.trans (Equiv.ofBijective g ⟨hginj, hgsurj⟩), ?_⟩
    intro p
    change (F.partition.leaf k).inclusion (g (e p)) = _
    rw [hg, he, Function.iterate_succ_apply']


end HolomorphicAnosov

open scoped Manifold ContDiff
namespace HolomorphicAnosov
universe u

/-- An equivalence between stable leaves that intertwines their inclusions with the ambient
biholomorphism is biholomorphic. -/
theorem nativeStableLeaf_equiv_biholomorph {d : ℕ} {M : Type u} [MetricSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M)
    (S : ContinuousComplexTangentSubbundle (complexModel d) M)
    {ι : Type u} {L : ι → Type u}
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
    (F : NativeComplexStableLeafDatum f.toHomeomorph S ι L)
    (i j : ι) (e : L i ≃ L j)
    (he : ∀ p, (F.partition.leaf j).inclusion (e p) =
      f ((F.partition.leaf i).inclusion p)) :
    letI := (F.complexUpgrade i).charts
    letI := (F.complexUpgrade j).charts
    ∃ a : Diffeomorph (complexModel 1) (complexModel 1) (L i) (L j) ∞,
      ∀ p, a p = e p := by
  letI := (F.complexUpgrade i).charts
  letI := (F.complexUpgrade j).charts
  have heinv : (F.partition.leaf i).inclusion ∘ e.symm =
      f.symm ∘ (F.partition.leaf j).inclusion := by
    funext q
    apply f.injective
    change f ((F.partition.leaf i).inclusion (e.symm q)) =
      f (f.symm ((F.partition.leaf j).inclusion q))
    rw [f.apply_symm_apply, ← he, e.apply_symm_apply]
  have hc : Continuous e := by
    apply CompleteStableCoordinatesScratch.native_leaf_map_continuous F i j
    have heq : (F.partition.leaf j).inclusion ∘ e =
        f ∘ (F.partition.leaf i).inclusion := funext he
    rw [heq]
    exact f.continuous.comp (F.complexUpgrade i).inclusion_holomorphic.continuous
  have hci : Continuous e.symm := by
    apply CompleteStableCoordinatesScratch.native_leaf_map_continuous F j i
    rw [heinv]
    exact f.symm.continuous.comp (F.complexUpgrade j).inclusion_holomorphic.continuous
  have hforward : ContMDiff (complexModel 1) (complexModel 1) ∞ e := by
    intro p
    apply (ContMDiffAt.iff_comp_isImmersionAt
      ((F.complexUpgrade j).inclusion_immersion (e p))).2
    refine ⟨hc.continuousAt, ?_⟩
    have heq : (F.partition.leaf j).inclusion ∘ e =
        f ∘ (F.partition.leaf i).inclusion := funext he
    rw [heq]
    exact f.contMDiff.contMDiffAt.comp p ((F.complexUpgrade i).inclusion_holomorphic p)
  have hbackward : ContMDiff (complexModel 1) (complexModel 1) ∞ e.symm := by
    intro q
    apply (ContMDiffAt.iff_comp_isImmersionAt
      ((F.complexUpgrade i).inclusion_immersion (e.symm q))).2
    refine ⟨hci.continuousAt, ?_⟩
    have heq : (F.partition.leaf i).inclusion ∘ e.symm =
        f.symm ∘ (F.partition.leaf j).inclusion := by
      funext q
      apply f.injective
      change f ((F.partition.leaf i).inclusion (e.symm q)) =
        f (f.symm ((F.partition.leaf j).inclusion q))
      rw [f.apply_symm_apply, ← he, e.apply_symm_apply]
    rw [heq]
    exact f.symm.contMDiff.contMDiffAt.comp q
      ((F.complexUpgrade j).inclusion_holomorphic q)
  refine ⟨{ toEquiv := e
            contMDiff_toFun := hforward
            contMDiff_invFun := hbackward }, fun _ ↦ rfl⟩


end HolomorphicAnosov

namespace HolomorphicAnosov
open scoped Manifold ContDiff
universe u

/-- Every forward iterate lifts to a biholomorphism between stable leaves. (Zhang, Lemma 2.7, eq.
(18)) -/
theorem nativeStableLeaf_iterate_biholomorph
    {d : ℕ} {M : Type u} [MetricSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (S : ContinuousComplexTangentSubbundle (complexModel d) M)
    {ι : Type u} {L : ι → Type u}
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
    (F : NativeComplexStableLeafDatum f.toHomeomorph S ι L)
    (i : ι) (z : L i) (n : ℕ) :
    letI : ∀ i, ChartedSpace (ComplexModel 1) (L i) := fun i ↦ (F.complexUpgrade i).charts
    ∃ j, ∃ e : Diffeomorph (complexModel 1) (complexModel 1) (L i) (L j) ∞,
      ∀ p, (F.partition.leaf j).inclusion (e p) =
        (f : M → M)^[n] ((F.partition.leaf i).inclusion p) := by
  letI : ∀ i, ChartedSpace (ComplexModel 1) (L i) := fun i ↦ (F.complexUpgrade i).charts
  induction n with
  | zero => exact ⟨i, Diffeomorph.refl _ _ ∞, fun _ ↦ rfl⟩
  | succ n ih =>
    obtain ⟨j, e, he⟩ := ih
    obtain ⟨k, a, ha⟩ := nativeStableLeaf_iterate_equiv f.toHomeomorph S F j (e z) 1
    have ha' : ∀ p, (F.partition.leaf k).inclusion (a p) =
        f ((F.partition.leaf j).inclusion p) := by simpa using ha
    obtain ⟨b, hb⟩ := nativeStableLeaf_equiv_biholomorph f S F j k a ha'
    refine ⟨k, e.trans b, ?_⟩
    intro p
    change (F.partition.leaf k).inclusion (b (e p)) = _
    rw [hb, ha', he, Function.iterate_succ_apply']

end HolomorphicAnosov

namespace HolomorphicAnosov
open scoped Manifold ContDiff
universe u

/-- Leaf lifts that intertwine their inclusions with an ambient iterate are smooth in the real leaf
atlases. -/
theorem nativeStableLeaf_iterate_lift_real_smooth
    {d : ℕ} {M : Type u} [MetricSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (S : ContinuousComplexTangentSubbundle (complexModel d) M)
    {ι : Type u} {L : ι → Type u}
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
    (F : NativeComplexStableLeafDatum f.toHomeomorph S ι L)
    (i j : ι) (q : L i → L j) (n : ℕ)
    (hq : ∀ p, (F.partition.leaf j).inclusion (q p) =
      (f : M → M)^[n] ((F.partition.leaf i).inclusion p)) :
    ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, Fin 2 → ℝ) ∞ q := by
  have hinc : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) (realModel d) ∞
      (F.partition.leaf i).inclusion :=
    fun x ↦ ((F.partition.leaf i).immersion.isImmersionAt x).contMDiffAt
  have hcomp : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) (realModel d) ∞
      ((F.partition.leaf j).inclusion ∘ q) := by
    rw [show (F.partition.leaf j).inclusion ∘ q =
      (f : M → M)^[n] ∘ (F.partition.leaf i).inclusion from funext hq]
    exact ((contMDiff_complex_to_real f.contMDiff).iterate n).comp hinc
  have hc := CompleteStableCoordinatesScratch.native_leaf_map_continuous F i j q hcomp.continuous
  intro x
  exact (ContMDiffAt.iff_comp_isImmersionAt
    ((F.partition.leaf j).immersion.isImmersionAt (q x))).2
      ⟨hc.continuousAt, hcomp x⟩

end HolomorphicAnosov

noncomputable section
namespace HolomorphicAnosov
open scoped Manifold ContDiff
universe u

attribute [local instance] complex_isManifold_real

/-- The all-iterate Anosov estimate bounds the intrinsic Hermitian distance between forward images
of stable-leaf points by a geometric contraction factor. -/
theorem nativeStableLeaf_all_iterates_contraction
    {d : ℕ} {M : Type u} [MetricSpace M] [ChartedSpace (ComplexModel d) M]
    [IsCompactComplexManifold d M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (S : ContinuousComplexTangentSubbundle (complexModel d) M)
    (hS : ∀ x, complexStableRealDistribution S x = a.splitting.stable.toDistribution x)
    (h : HermitianTangentMetricCore d M) (hh : IsSmoothHermitianTangentMetric h)
    {ι : Type u} {L : ι → Type u}
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
    (F : NativeComplexStableLeafDatum f.toHomeomorph S ι L) :
    letI : ∀ i, ChartedSpace (ComplexModel 1) (L i) := fun i ↦ (F.complexUpgrade i).charts
    ∃ C rate : ℝ, 0 < C ∧ (0 < rate ∧ rate < 1) ∧
      ∀ (i : ι) (z : L i) (n : ℕ),
      ∃ j, ∃ e : Diffeomorph (complexModel 1) (complexModel 1) (L i) (L j) ∞,
        (∀ p, (F.partition.leaf j).inclusion (e p) =
          (f : M → M)^[n] ((F.partition.leaf i).inclusion p)) ∧
        ∀ x y : L i,
          intrinsicHermitianLeafEDist (r := 2) (F.partition.leaf j).inclusion h (e x) (e y) ≤
          ENNReal.ofReal (C * rate ^ n) *
            intrinsicHermitianLeafEDist (r := 2) (F.partition.leaf i).inclusion h x y := by
  letI : ∀ i, ChartedSpace (ComplexModel 1) (L i) := fun i ↦ (F.complexUpgrade i).charts
  obtain ⟨C, rate, hC, hrate, hs, _⟩ := OneFormBundle.original_all_iterates_hermitian f a h hh
  refine ⟨C, rate, hC, hrate, ?_⟩
  intro i z n
  obtain ⟨j, e, he⟩ := nativeStableLeaf_iterate_biholomorph f S F i z n
  refine ⟨j, e, he, ?_⟩
  have he_real := (nativeStableLeaf_iterate_lift_real_smooth f S F i j e n he).of_le
    (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)
  have hinc (k : ι) : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) (realModel d) 1
      (F.partition.leaf k).inclusion := by
    intro p
    exact ((F.partition.leaf k).immersion.isImmersionAt p).contMDiffAt.of_le (by simp)
  apply IntrinsicPiecewiseC1Path.map_edist_le e he_real
    (F.partition.leaf i).inclusion (F.partition.leaf j).inclusion h (C * rate ^ n)
    (mul_pos hC (pow_pos hrate.1 n))
  apply IntrinsicPiecewiseC1Path.norm_bound_of_ambient e he_real
    (F.partition.leaf i).inclusion (F.partition.leaf j).inclusion (hinc i) (hinc j)
    ((f : M → M)^[n]) (((contMDiff_complex_to_real f.contMDiff).iterate n).of_le (by simp))
    (funext he) h (C * rate ^ n)
  intro p v
  apply hs n ((F.partition.leaf i).inclusion p)
  rw [← hS, ← (F.partition.leaf i).tangent p]
  exact ⟨v, rfl⟩

end HolomorphicAnosov
open Set MeasureTheory Bundle
open scoped ContDiff Manifold ENNReal
namespace HolomorphicAnosov
namespace IntrinsicPiecewiseC1Path

variable {r d : ℕ} {L M : Type*}
  [TopologicalSpace L] [ChartedSpace (Fin r → ℝ) L]
  [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
  [IsManifold (complexModel d) ∞ M]
attribute [local instance] complex_isManifold_real

/-- The Hermitian speed of a piecewise C¹ path is continuous on each closed C¹ piece. -/
theorem continuousOn_speed {x y : L} (p : IntrinsicPiecewiseC1Path (r := r) x y)
    (inc : L → M) (hinc : ContMDiff 𝓘(ℝ, Fin r → ℝ) (realModel d) 1 inc)
    (h : HermitianTangentMetricCore d M) (hh : IsSmoothHermitianTangentMetric h)
    (i : Fin (p.n + 1)) : ContinuousOn (p.speed inc h i) (p.pieceInterval i) := by
  have hu : UniqueMDiffOn 𝓘(ℝ, ℝ) (p.pieceInterval i) := by
    rw [uniqueMDiffOn_iff_uniqueDiffOn]
    exact uniqueDiffOn_Icc (p.time_strictMono Fin.castSucc_lt_succ)
  let γ := inc ∘ p.piece i
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) (realModel d) 1 γ (p.pieceInterval i) :=
    hinc.comp_contMDiffOn (p.piece_c1 i)
  have ht := hγ.continuousOn_tangentMapWithin (le_refl 1) hu
  have hv : ContinuousOn
      (fun t ↦ TotalSpace.mk' (ComplexModel d) (γ t)
        (mfderivWithin 𝓘(ℝ, ℝ) (realModel d) γ (p.pieceInterval i) t (1 : ℝ)))
      (p.pieceInterval i) := by
    have hc : Continuous (fun t : ℝ ↦ (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
      exact (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous.comp
        (continuous_id.prodMk continuous_const)
    exact ht.comp hc.continuousOn (fun _ ht ↦ ht)
  have hn := (Preparation.continuous_hermitian_tangent_norm h hh).comp
    continuous_complexTangentToReal_symm
  have hs := hn.comp_continuousOn hv
  apply hs.congr
  intro t ht
  have hd := congrArg
    (fun A : TangentSpace 𝓘(ℝ, ℝ) t →L[ℝ] TangentSpace (realModel d) (γ t) ↦ A (1 : ℝ))
    (mfderiv_comp_mfderivWithin t (hinc.mdifferentiable (by simp) _)
      ((p.piece_c1 i).mdifferentiableOn (by simp) t ht) (hu t ht))
  exact (congrArg (fun v : TangentSpace (realModel d) (γ t) ↦
    Real.sqrt (hermitianTangentRealPairing h (γ t) v v)) hd).symm


/-- A path with finitely many C¹ pieces has finite Hermitian length. -/
theorem length_ne_top {x y : L} (p : IntrinsicPiecewiseC1Path (r := r) x y)
    (inc : L → M) (hinc : ContMDiff 𝓘(ℝ, Fin r → ℝ) (realModel d) 1 inc)
    (h : HermitianTangentMetricCore d M) (hh : IsSmoothHermitianTangentMetric h) :
    p.length inc h ≠ ⊤ := by
  unfold length
  apply ENNReal.sum_ne_top.mpr
  intro i _
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image (p.continuousOn_speed inc hinc h hh i)
  apply ne_of_lt
  calc
    _ ≤ ∫⁻ _t in p.pieceInterval i, ENNReal.ofReal C := by
      apply setLIntegral_mono' measurableSet_Icc
      intro t ht
      exact ENNReal.ofReal_le_ofReal (hC ⟨t, ht, rfl⟩)
    _ < ⊤ := by
      simp only [pieceInterval, setLIntegral_const, Real.volume_Icc]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

end IntrinsicPiecewiseC1Path
end HolomorphicAnosov
namespace HolomorphicAnosov
open scoped ContDiff Manifold

/-- Any two points of a connected smooth real leaf can be joined by a path with finitely many C¹
pieces. -/
theorem native_piecewiseC1Path_nonempty {r : ℕ} {L : Type*}
    [TopologicalSpace L] [ChartedSpace (Fin r → ℝ) L]
    [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ L] [ConnectedSpace L] (x y : L) :
    Nonempty (IntrinsicPiecewiseC1Path (r := r) x y) := by
  let c := (EuclideanSpace.equiv (Fin r) ℝ).symm
  letI := CompleteStableCoordinatesScratch.rechart (M := L) c
  letI := CompleteStableCoordinatesScratch.rechart_isManifold (M := L) c
  obtain ⟨a, ha⟩ := CompleteStableCoordinatesScratch.rechart_identity_diffeomorph_exists (M := L) c
  have hai : ∀ z, a.symm z = z := by
    intro z
    simpa only [ha] using a.apply_symm_apply z
  obtain ⟨γ⟩ := Franks.connected_piecewiseC1Path_nonempty (r := r) x y
  obtain ⟨q, hqc, N, hN, times, ht, h0, h1, hq, hx, hy⟩ := γ
  cases N with
  | zero => omega
  | succ n =>
    refine ⟨{
      n := n
      time := times
      time_strictMono := ht
      time_zero := h0
      time_one := h1
      piece := fun _ ↦ a.symm ∘ q
      piece_c1 := fun i ↦ (a.symm.contMDiff.of_le (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)).comp_contMDiffOn (hq i)
      source := ?_
      target := ?_
      junction := fun _ ↦ rfl }⟩
    · change a.symm (q 0) = x
      rw [hx, hai]
    · change a.symm (q 1) = y
      rw [hy, hai]

/-- The intrinsic Hermitian extended distance between two points of a connected smooth leaf is
finite. -/
theorem native_intrinsicHermitianLeafEDist_ne_top {r d : ℕ} {L M : Type*}
    [TopologicalSpace L] [ChartedSpace (Fin r → ℝ) L]
    [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ L] [ConnectedSpace L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (inc : L → M) (hinc : ContMDiff 𝓘(ℝ, Fin r → ℝ) (realModel d) 1 inc)
    (h : HermitianTangentMetricCore d M) (hh : IsSmoothHermitianTangentMetric h)
    (x y : L) : intrinsicHermitianLeafEDist (r := r) inc h x y ≠ ⊤ := by
  obtain ⟨p⟩ := native_piecewiseC1Path_nonempty (r := r) x y
  exact ne_of_lt ((iInf_le _ p).trans_lt (lt_top_iff_ne_top.mpr (p.length_ne_top inc hinc h hh)))

end HolomorphicAnosov

namespace HolomorphicAnosov
open Filter
open scoped _root_.Topology

/-- A geometric contraction factor times a finite extended length eventually falls below any
positive radius. -/
theorem finite_length_geometric_eventually_lt (C rate δ : ℝ) (hC : 0 < C)
    (hrate : 0 < rate ∧ rate < 1) (hδ : 0 < δ) (R : ℝ≥0∞) (hR : R ≠ ⊤) :
    ∃ N : ℕ, ∀ n ≥ N, ENNReal.ofReal (C * rate ^ n) * R < ENNReal.ofReal δ := by
  have ht : Tendsto (fun n : ℕ ↦ C * rate ^ n * R.toReal) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hrate.1.le hrate.2).const_mul C).mul_const R.toReal
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually_lt_const hδ)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hb := (ENNReal.ofReal_lt_ofReal_iff hδ).mpr (hN n hn)
  rwa [ENNReal.ofReal_mul (mul_nonneg hC.le (pow_nonneg hrate.1.le n)),
    ENNReal.ofReal_toReal hR] at hb

open scoped ContDiff Manifold
universe u
attribute [local instance] complex_isManifold_real

/-- The forward images of a pair of stable-leaf points eventually remain within any prescribed
positive intrinsic radius. -/
theorem nativeStableLeaf_eventual_intrinsic_entry
    {d : ℕ} {M : Type u} [MetricSpace M] [ChartedSpace (ComplexModel d) M]
    [IsCompactComplexManifold d M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (S : ContinuousComplexTangentSubbundle (complexModel d) M)
    (hS : ∀ x, complexStableRealDistribution S x = a.splitting.stable.toDistribution x)
    (h : HermitianTangentMetricCore d M) (hh : IsSmoothHermitianTangentMetric h)
    {ι : Type u} {L : ι → Type u}
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
    (F : NativeComplexStableLeafDatum f.toHomeomorph S ι L)
    (i : ι) (z p : L i) (δ : ℝ) (hδ : 0 < δ) :
    letI : ∀ i, ChartedSpace (ComplexModel 1) (L i) := fun i ↦ (F.complexUpgrade i).charts
    ∃ N : ℕ, ∀ n ≥ N,
      ∃ j, ∃ e : Diffeomorph (complexModel 1) (complexModel 1) (L i) (L j) ∞,
        (∀ q, (F.partition.leaf j).inclusion (e q) =
          (f : M → M)^[n] ((F.partition.leaf i).inclusion q)) ∧
        intrinsicHermitianLeafEDist (r := 2) (F.partition.leaf j).inclusion h (e z) (e p) <
          ENNReal.ofReal δ := by
  letI : ∀ i, ChartedSpace (ComplexModel 1) (L i) := fun i ↦ (F.complexUpgrade i).charts
  obtain ⟨C, rate, hC, hrate, hcontraction⟩ :=
    nativeStableLeaf_all_iterates_contraction f a S hS h hh F
  letI := (F.partition.leaf i).connected
  have hinc : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) (realModel d) 1 (F.partition.leaf i).inclusion :=
    fun x ↦ ((F.partition.leaf i).immersion.isImmersionAt x).contMDiffAt.of_le (by simp)
  have hfinite := native_intrinsicHermitianLeafEDist_ne_top
    (F.partition.leaf i).inclusion hinc h hh z p
  obtain ⟨N, hN⟩ := finite_length_geometric_eventually_lt C rate δ hC hrate hδ _ hfinite
  refine ⟨N, fun n hn ↦ ?_⟩
  obtain ⟨j, e, he, hbound⟩ := hcontraction i z n
  exact ⟨j, e, he, (hbound z p).trans_lt (hN n hn)⟩

end HolomorphicAnosov

namespace HolomorphicAnosov
/-- An intrinsic distance below `δ / C` remains below `δ` after multiplication by any factor `C *
rate ^ n` with `0 < rate < 1`. -/
theorem geometric_intrinsic_trapping_bound (C rate δ : ℝ) (hC : 0 < C)
    (hrate : 0 < rate ∧ rate < 1) (hδ : 0 < δ) (R : ℝ≥0∞)
    (hR : R < ENNReal.ofReal (δ / C)) (n : ℕ) :
    ENNReal.ofReal (C * rate ^ n) * R < ENNReal.ofReal δ := by
  have hn : C * rate ^ n ≤ C := by
    exact (mul_le_mul_of_nonneg_left (pow_le_one₀ hrate.1.le hrate.2.le) hC.le).trans_eq (mul_one C)
  have hmul : ENNReal.ofReal C * R < ENNReal.ofReal C * ENNReal.ofReal (δ / C) :=
    by simpa only [mul_comm] using
      ENNReal.mul_lt_mul_left (ne_of_gt (ENNReal.ofReal_pos.mpr hC)) ENNReal.ofReal_ne_top hR
  have heq : ENNReal.ofReal C * ENNReal.ofReal (δ / C) = ENNReal.ofReal δ := by
    rw [← ENNReal.ofReal_mul hC.le]
    congr 1
    field_simp
  have hmono : ENNReal.ofReal (C * rate ^ n) * R ≤ ENNReal.ofReal C * R := by
    gcongr
  exact hmono.trans_lt (hmul.trans_eq heq)

end HolomorphicAnosov

namespace HolomorphicAnosov
open scoped Manifold ContDiff
universe u
attribute [local instance] complex_isManifold_real

/-- Forward iterates of a stable-leaf pair eventually remain in the intrinsic-coordinate domain of
any fixed positive radius. (Zhang, Lemma 2.7, eq. (18)) -/
theorem nativeStableLeaf_eventual_coordinate_domain_entry
    {d : ℕ} {M : Type u} [MetricSpace M] [ChartedSpace (ComplexModel d) M]
    [IsCompactComplexManifold d M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (S : ContinuousComplexTangentSubbundle (complexModel d) M)
    (hS : ∀ x, complexStableRealDistribution S x = a.splitting.stable.toDistribution x)
    (h : HermitianTangentMetricCore d M) (hh : IsSmoothHermitianTangentMetric h)
    {ι : Type u} {L : ι → Type u}
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
    (F : NativeComplexStableLeafDatum f.toHomeomorph S ι L)
    (i : ι) (z p : L i) (r : ℝ) (hr : 0 < r) :
    letI : ∀ i, ChartedSpace (ComplexModel 1) (L i) :=
      fun i ↦ (F.complexUpgrade i).charts
    ∀ᶠ n in Filter.atTop,
      ∃ (j : ι) (e : Diffeomorph (complexModel 1) (complexModel 1) (L i) (L j) ∞),
        (∀ q, (F.partition.leaf j).inclusion (e q) =
          (f : M → M)^[n] ((F.partition.leaf i).inclusion q)) ∧
        intrinsicHermitianLeafEDist (r := 2) (F.partition.leaf j).inclusion h
          (e z) (e p) < ENNReal.ofReal r := by
  letI : ∀ i, ChartedSpace (ComplexModel 1) (L i) :=
    fun i ↦ (F.complexUpgrade i).charts
  obtain ⟨N, hN⟩ := nativeStableLeaf_eventual_intrinsic_entry
    f a S hS h hh F i z p r hr
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  exact hN n hn

end HolomorphicAnosov

/-! Complete normalized coordinates on intrinsic stable leaves and their continuous dependence on
the base point. (Zhang, Lemma 2.7, eq. (18)) -/

open Set _root_.Topology TopologicalSpace
open scoped Manifold ContDiff Bundle

attribute [local instance] HolomorphicAnosov.complex_isManifold_real

namespace HolomorphicAnosov.Paper.Zhang

noncomputable section
universe u

set_option maxHeartbeats 750000 in
/-- For a holomorphic Anosov diffeomorphism in complex dimension at least three with complex stable
rank one, normalized local parallel coordinates extend to a continuous family of biholomorphisms
from stable leaves to their stable tangent lines, conjugating the dynamics to its derivative.
These coordinates satisfy the eventual iterate formula and have continuous inverse evaluation on
the stable tangent bundle. (Zhang, Lemma 2.7, eq. (18)) -/
theorem complete_stable_coordinates
    {d : ℕ} (hd : 3 ≤ d) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsCompactComplexManifold d X]
    (f : Biholomorph d d X X) (a : AnosovDatum f)
    (hstable : HasComplexRankOne a.splitting.stable.toDistribution)
    (S : ContinuousComplexTangentSubbundle (complexModel d) X)
    (hS : ∀ x, ((S.toDistribution x).restrictScalars ℝ).map
      (complexTangentToReal d x).toLinearEquiv.toLinearMap =
        a.splitting.stable.toDistribution x)
    (U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    (hunstable : ∀ x, ((U x).restrictScalars ℝ).map
      (complexTangentToReal d x).toLinearEquiv.toLinearMap =
        a.splitting.unstable.toDistribution x)
    (hU : ∀ x (v : TangentSpace (complexModel d) x), v ∈ U x →
      mfderiv (complexModel d) (complexModel d) f x v ∈ U (f x))
    (nabla : QuotientLineConnection.Connection U)
    (hcontinuous : QuotientLineConnection.IsContinuous nabla)
    (hcompatible : QuotientLineConnection.IsCompatible nabla)
    (hinvariant : QuotientLineConnection.IsInvariant nabla f hU)
    (ι : Type u) (L : ι → Type u)
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)] :
    letI : MetrizableSpace X := Manifold.metrizableSpace (realModel d) X
    letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
    letI : ∀ x : X, NormedAddCommGroup (TangentSpace (complexModel d) x) :=
      fun _ ↦ inferInstanceAs (NormedAddCommGroup (ComplexModel d))
    letI : ∀ x : X, NormedSpace ℂ (TangentSpace (complexModel d) x) :=
      fun _ ↦ inferInstanceAs (NormedSpace ℂ (ComplexModel d))
    ∀ F : NativeComplexStableLeafDatum f.toHomeomorph S ι L,
    letI : ∀ i, ChartedSpace (ComplexModel 1) (L i) := fun i ↦ (F.complexUpgrade i).charts
    letI : ∀ i, IsManifold (complexModel 1) ∞ (L i) :=
      fun i ↦ (F.complexUpgrade i).complex_manifold
    letI : ∀ b, TopologicalSpace (F.transversal b) := F.transversalTopology
    let inc := fun i ↦ (F.partition.leaf i).inclusion
    let valid := fun (V : Opens X) (σ : (x : X) → QuotientLineConnection.Fibre U x)
      (t : X → ℂ) ↦
      QuotientLineConnection.IsHolomorphicSection U V σ ∧
      (∀ x ∈ V, σ x ≠ 0) ∧ QuotientLineConnection.IsParallelOn nabla V σ ∧
      ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞ t V ∧
      (∀ x ∈ V, ∀ v : TangentSpace (complexModel d) x,
        QuotientLineConnection.projection U x v =
          ((tangentSpaceCastModel 𝓘(ℂ, ℂ) (t x)).toContinuousLinearMap.comp
            (mfderiv (complexModel d) 𝓘(ℂ, ℂ) t x)) v • σ x) ∧
      (∀ x ∈ V, ((tangentSpaceCastModel 𝓘(ℂ, ℂ) (t x)).toContinuousLinearMap.comp
        (mfderiv (complexModel d) 𝓘(ℂ, ℂ) t x)).ker = U x);
    ∃ (φ : ∀ (i : ι) (z : L i),
        Diffeomorph (complexModel 1) 𝓘(ℂ, S.toDistribution (inc i z))
          (L i) (S.toDistribution (inc i z)) ∞)
      (K : ∀ x : X, X → S.toDistribution x)
      (D : ∀ (i : ι), L i → Set (L i))
      (e : ∀ x : X, S.toDistribution x → X),
      (∀ (i : ι) (z : L i), φ i z z = 0) ∧
      (∀ (i : ι) (z : L i) (v : TangentSpace (complexModel 1) z),
        (((tangentSpaceCastModel 𝓘(ℂ, S.toDistribution (inc i z)) (φ i z z)).toContinuousLinearMap.comp
            (mfderiv (complexModel 1) 𝓘(ℂ, S.toDistribution (inc i z)) (φ i z) z)) v).val =
          mfderiv (complexModel 1) (complexModel d) (inc i) z v) ∧
      (∀ (V : Opens X) (σ : (x : X) → QuotientLineConnection.Fibre U x) (t : X → ℂ),
        valid V σ t → ∀ (i : ι) (z : L i), inc i z ∈ V →
          ∀ᶠ p in 𝓝 z, inc i p ∈ V ∧
            φ i z p = normalizedLocalStableCoordinate S.toDistribution t (inc i z) (inc i p)) ∧
      (∀ (i : ι) (z : L i), IsOpen (D i z) ∧ z ∈ D i z ∧
        ∃ (V : Opens X) (σ : (x : X) → QuotientLineConnection.Fibre U x) (t : X → ℂ),
          inc i z ∈ V ∧ valid V σ t ∧ ∀ p ∈ D i z,
            inc i p ∈ V ∧
            K (inc i z) (inc i p) =
              normalizedLocalStableCoordinate S.toDistribution t (inc i z) (inc i p) ∧
            φ i z p = K (inc i z) (inc i p)) ∧
      (∀ (i : ι) (z p : L i), ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∃ (j : ι) (w q : L j), inc j w = (f : X → X)^[n] (inc i z) ∧
          inc j q = (f : X → X)^[n] (inc i p) ∧ q ∈ D j w ∧
          (K (inc j w) (inc j q)).val =
            mfderiv (complexModel d) (complexModel d) ((f : X → X)^[n]) (inc i z)
              (φ i z p).val) ∧
      (∀ (i j : ι) (z p : L i) (w q : L j), inc j w = f (inc i z) →
        inc j q = f (inc i p) → (φ j w q).val =
          mfderiv (complexModel d) (complexModel d) f (inc i z) (φ i z p).val) ∧
      (∀ (i : ι) (z : L i) (v : S.toDistribution (inc i z)),
        e (inc i z) v = inc i ((φ i z).symm v)) ∧
      Continuous (fun v : {v : TangentBundle (complexModel d) X //
          v.snd ∈ S.toDistribution v.proj} ↦
        e v.val.proj ⟨v.val.snd, v.property⟩) ∧
      (∀ b : F.boxIndex,
        let B := F.boxes.boxes b
        Continuous (fun v : (B.disc × B.disc) × F.transversal b ↦
          let z : L (B.label v.2) := (B.chart v.2 v.1.1).val
          let p : L (B.label v.2) := (B.chart v.2 v.1.2).val
          (⟨inc (B.label v.2) z, (φ (B.label v.2) z p).val⟩ :
            TangentBundle (complexModel d) X))) := by
  letI : MetrizableSpace X := Manifold.metrizableSpace (realModel d) X
  letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  intro F
  letI : ∀ x : X, NormedAddCommGroup (TangentSpace (complexModel d) x) :=
    fun _ ↦ inferInstanceAs (NormedAddCommGroup (ComplexModel d))
  letI : ∀ x : X, NormedSpace ℂ (TangentSpace (complexModel d) x) :=
    fun _ ↦ inferInstanceAs (NormedSpace ℂ (ComplexModel d))
  obtain ⟨h, hh⟩ := OneFormBundle.original_smooth_tangent_metric_exists (d := d) (M := X)
  obtain ⟨C, rate, hC, hrate, hs, hu⟩ :=
    OneFormBundle.original_all_iterates_hermitian f a h hh
  obtain ⟨r, ε, K, inverse, hr, hε, hcenter, hgerm, hcharts, hfamily⟩ :=
    uniform_local_stable_coordinates hd X f a S hS U hunstable hU nabla
      hcontinuous hcompatible hinvariant ι L h hh F
  let D : Set (X × X) := {xp | ∃ i, ∃ z p : L i,
    (F.partition.leaf i).inclusion z = xp.1 ∧
    (F.partition.leaf i).inclusion p = xp.2 ∧
    intrinsicHermitianLeafEDist (r := 2) (F.partition.leaf i).inclusion h z p < ENNReal.ofReal r}
  letI : TopologicalSpace (Bundle.TotalSpace (ComplexModel d)
      (fun x ↦ ↥(S.toDistribution x))) :=
    TopologicalSpace.induced
      (fun w ↦ (⟨w.proj, w.snd.val⟩ : TangentBundle (complexModel d) X)) inferInstance
  let O : Set (Bundle.TotalSpace (ComplexModel d) (fun x ↦ ↥(S.toDistribution x))) :=
    (fun xp : X × X ↦ ⟨xp.1, K xp.1 xp.2⟩) '' D
  obtain ⟨hKcont, hOopen, hInvCont, hForward, hBack⟩ := hfamily
  have hself (i : ι) (z : L i) :
      intrinsicHermitianLeafEDist (r := 2) (F.partition.leaf i).inclusion h z z <
        ENNReal.ofReal r := by
    let path : IntrinsicPiecewiseC1Path (r := 2) z z :=
      { n := 0
        time := fun i ↦ (i.val : ℝ)
        time_strictMono := fun i j hij ↦ Nat.cast_lt.mpr (show i.val < j.val from hij)
        time_zero := by norm_num
        time_one := by norm_num
        piece := fun _ _ ↦ z
        piece_c1 := fun _ ↦ contMDiffOn_const
        source := rfl
        target := rfl
        junction := fun j ↦ Fin.elim0 j }
    have hv (j : Fin 1) (t : ℝ) : path.velocity j t = 0 := by
      unfold IntrinsicPiecewiseC1Path.velocity
      change mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin 2 → ℝ) (fun _ ↦ z) _ t (1 : ℝ) = 0
      rw [mfderivWithin_const]
      rfl
    have hs (j : Fin 1) (t : ℝ) : path.speed (F.partition.leaf i).inclusion h j t = 0 := by
      unfold IntrinsicPiecewiseC1Path.speed
      rw [hv]
      simp [leafPullbackHermitianNorm, leafPullbackHermitianPairing,
        hermitianTangentRealPairing, hermitianTangentPairing,
        InnerProductSpace.Core.inner_zero_left]
    have hlen : path.length (F.partition.leaf i).inclusion h = 0 := by
      change (∑ j : Fin 1, ∫⁻ t in path.pieceInterval j,
        ENNReal.ofReal (path.speed (F.partition.leaf i).inclusion h j t)) = 0
      simp only [hs, ENNReal.ofReal_zero, MeasureTheory.lintegral_zero, Finset.sum_const_zero]
    exact (iInf_le_of_le path le_rfl).trans_lt
      (hlen ▸ ENNReal.ofReal_pos.mpr hr)
  have hDdiag : ∀ x, (x, x) ∈ D := by
    intro x
    obtain ⟨i, z, hz⟩ := F.partition.cover x
    exact ⟨i, z, z, hz, hz, hself i z⟩
  have hnativeTransport := nativeStableLeaf_iterate_biholomorph f S F
  have hnativeContraction := nativeStableLeaf_all_iterates_contraction f a S hS h hh F
  have hOriginalDomainEntry (i : ι) (z p : L i) :
      ∀ᶠ n in Filter.atTop,
        ((f : X → X)^[n] ((F.partition.leaf i).inclusion z),
          (f : X → X)^[n] ((F.partition.leaf i).inclusion p)) ∈ D := by
    letI : ∀ j, ChartedSpace (ComplexModel 1) (L j) := fun j ↦ (F.complexUpgrade j).charts
    have hN := (nativeStableLeaf_eventual_coordinate_domain_entry
      f a S hS h hh F i z p r hr)
    filter_upwards [hN] with n hn
    obtain ⟨j, e, he, hdist⟩ := hn
    exact ⟨j, e z, e p, he z, he p, hdist⟩
  have hActualCoordinateEntry (i : ι) (z p : L i) (δ : ℝ) (hδ : 0 < δ) :
      ∀ᶠ n in Filter.atTop,
        let x := (f : X → X)^[n] ((F.partition.leaf i).inclusion z)
        let y := (f : X → X)^[n] ((F.partition.leaf i).inclusion p)
        Real.sqrt (((h x).inner (K x y).val (K x y).val).re) < δ := by
    have hp : (F.partition.leaf i).inclusion p ∈ Set.range (F.partition.leaf i).inclusion :=
      ⟨p, rfl⟩
    rw [F.asymptotic i z] at hp
    have hclose : Filter.Tendsto
        (fun n ↦ dist ((f : X → X)^[n] ((F.partition.leaf i).inclusion z))
          ((f : X → X)^[n] ((F.partition.leaf i).inclusion p)))
        Filter.atTop (𝓝 (0 : ℝ)) := by
      change Filter.Tendsto
        (fun n ↦ dist ((f : X → X)^[n] ((F.partition.leaf i).inclusion p))
          ((f : X → X)^[n] ((F.partition.leaf i).inclusion z)))
        Filter.atTop (𝓝 (0 : ℝ)) at hp
      simpa only [dist_comm] using hp
    have hi : Continuous (fun w : Bundle.TotalSpace (ComplexModel d)
        (fun x ↦ ↥(S.toDistribution x)) ↦
        (⟨w.proj, w.snd.val⟩ : TangentBundle (complexModel d) X)) := continuous_induced_dom
    apply centered_coordinate_eventually_small D
      (fun xp ↦ Real.sqrt (((h xp.1).inner
        (K xp.1 xp.2).val (K xp.1 xp.2).val).re))
      ((Preparation.continuous_hermitian_tangent_norm h hh).comp_continuousOn
        (hi.comp_continuousOn hKcont)) hDdiag
      (fun x ↦ by simp [hcenter, InnerProductSpace.Core.inner_zero_left])
      _ _ (hOriginalDomainEntry i z p) hclose hδ
  have hKrecurrence (i : ι) (z : L i) :
      ∀ᶠ p in 𝓝 z,
        (K (f ((F.partition.leaf i).inclusion z))
          (f ((F.partition.leaf i).inclusion p))).val =
        mfderiv (complexModel d) (complexModel d) f ((F.partition.leaf i).inclusion z)
          (K ((F.partition.leaf i).inclusion z) ((F.partition.leaf i).inclusion p)).val := by
    letI : ∀ j, ChartedSpace (ComplexModel 1) (L j) :=
      fun j ↦ (F.complexUpgrade j).charts
    let x := (F.partition.leaf i).inclusion z
    obtain ⟨j, b, hb⟩ := nativeStableLeaf_iterate_biholomorph f S F i z 1
    have hb' : ∀ p, (F.partition.leaf j).inclusion (b p) =
        f ((F.partition.leaf i).inclusion p) := by simpa using hb
    obtain ⟨V, hxV, σ, t, hσ, hnz, hparallel, ht, hsub, hformula⟩ :=
      transverse_parallel_coordinates hd X f a hstable U hunstable hU
        nabla hcontinuous hcompatible hinvariant x
    obtain ⟨V', hfxV', σ', t', hσ', hnz', hparallel', ht', hsub', hformula'⟩ :=
      transverse_parallel_coordinates hd X f a hstable U hunstable hU
        nabla hcontinuous hcompatible hinvariant (f x)
    obtain ⟨W, hWo, hzW, hWV, hKeq⟩ :=
      hgerm V σ t hσ hnz hparallel ht (fun y hy v ↦ (hformula y hy).1 v) i z hxV
    obtain ⟨W', hW'o, hbzW', hW'V', hK'eq⟩ :=
      hgerm V' σ' t' hσ' hnz' hparallel' ht'
        (fun y hy v ↦ (hformula' y hy).1 v) j (b z) (by rw [hb' z]; exact hfxV')
    obtain ⟨c, c₀, N, hNo, hxN, hNV, haff, hdt⟩ :=
      localLinearization_original_map_locally_affine U f hU nabla hinvariant V V'
        σ σ' t t' hσ hσ' hnz hnz' hparallel hparallel' ht ht'
        (fun y hy v ↦ (hformula y hy).1 v)
        (fun y hy v ↦ (hformula' y hy).1 v) x hxV hfxV'
    have hB := localLinearization_stable_coordinate_derivative_invertible
      f a S hS U hunstable t x (F.finrank x) (hformula x hxV).2
    have hB' := localLinearization_stable_coordinate_derivative_invertible
      f a S hS U hunstable t' (f x) (F.finrank (f x)) (hformula' (f x) hfxV').2
    have hinc := (F.partition.leaf i).immersion.contMDiff.continuous
    filter_upwards [hWo.mem_nhds hzW,
      b.continuous.continuousAt.eventually (hW'o.mem_nhds hbzW'),
      hinc.continuousAt.eventually (hNo.mem_nhds hxN)] with p hp hp' hpN
    rw [hKeq p hp]
    have hK' := hK'eq (b p) hp'
    rw [hb' z, hb' p] at hK'
    rw [hK']
    let v := normalizedLocalStableCoordinate S.toDistribution t x
      ((F.partition.leaf i).inclusion p)
    have hsv : mfderiv (complexModel d) (complexModel d) f x v.val ∈
        S.toDistribution (f x) := by
      rw [← localLinearization_complex_stable_derivative_image f a S hS x]
      exact Submodule.mem_map.mpr ⟨v.val, v.property, rfl⟩
    let w : S.toDistribution (f x) :=
      ⟨mfderiv (complexModel d) (complexModel d) f x v.val, hsv⟩
    have hv : localStableCoordinateDerivative S.toDistribution t x v =
        t ((F.partition.leaf i).inclusion p) - t x := hB.self_apply_inverse _
    have hw : localStableCoordinateDerivative S.toDistribution t' (f x) w =
        t' (f ((F.partition.leaf i).inclusion p)) - t' (f x) := by
      change transverseScalarDifferential t' (f x)
        (mfderiv (complexModel d) (complexModel d) f x v.val) = _
      rw [hdt]
      change (c : ℂ) * localStableCoordinateDerivative S.toDistribution t x v = _
      rw [hv, haff _ hpN, haff x hxN]
      ring
    have heq : normalizedLocalStableCoordinate S.toDistribution t' (f x)
        (f ((F.partition.leaf i).inclusion p)) = w := by
      unfold normalizedLocalStableCoordinate
      rw [← hw]
      exact hB'.inverse_apply_self w
    exact congrArg Subtype.val heq
  letI : ∀ i, ChartedSpace (ComplexModel 1) (L i) :=
    fun i ↦ (F.complexUpgrade i).charts
  letI : ∀ i, IsManifold (complexModel 1) ∞ (L i) :=
    fun i ↦ (F.complexUpgrade i).complex_manifold
  have hKiterate (i : ι) (z : L i) (n : ℕ) :
      ∀ᶠ p in 𝓝 z,
        (K ((f : X → X)^[n] ((F.partition.leaf i).inclusion z))
          ((f : X → X)^[n] ((F.partition.leaf i).inclusion p))).val =
        mfderiv (complexModel d) (complexModel d) ((f : X → X)^[n])
          ((F.partition.leaf i).inclusion z)
          (K ((F.partition.leaf i).inclusion z) ((F.partition.leaf i).inclusion p)).val := by
    induction n with
    | zero =>
      simp only [Function.iterate_zero, id_eq, mfderiv_id]
      exact Filter.Eventually.of_forall (fun _ ↦ rfl)
    | succ n ih =>
      obtain ⟨j, b, hb⟩ := nativeStableLeaf_iterate_biholomorph f S F i z n
      have hnext := b.continuous.continuousAt.eventually (hKrecurrence j (b z))
      filter_upwards [ih, hnext] with p hp hnextp
      change (K (f ((F.partition.leaf j).inclusion (b z)))
          (f ((F.partition.leaf j).inclusion (b p)))).val =
          (mfderiv (complexModel d) (complexModel d) f
            ((F.partition.leaf j).inclusion (b z)))
            (K ((F.partition.leaf j).inclusion (b z))
              ((F.partition.leaf j).inclusion (b p))).val at hnextp
      rw [hb z, hb p] at hnextp
      change (K ((f : X → X)^[n] ((F.partition.leaf i).inclusion z))
          ((f : X → X)^[n] ((F.partition.leaf i).inclusion p))).val = _ at hp
      rw [hp] at hnextp
      have hchain := mfderiv_comp ((F.partition.leaf i).inclusion z)
        (f.contMDiff.mdifferentiable (by simp) _)
        ((f.contMDiff.iterate n).mdifferentiable (by simp) _)
      change (K ((f : X → X)^[n + 1] ((F.partition.leaf i).inclusion z))
          ((f : X → X)^[n + 1] ((F.partition.leaf i).inclusion p))).val = _
      rw [Function.iterate_succ']
      change (K (f ((f : X → X)^[n] ((F.partition.leaf i).inclusion z)))
          (f ((f : X → X)^[n] ((F.partition.leaf i).inclusion p)))).val = _
      rw [hchain]
      exact hnextp
  obtain ⟨Cd, td, hCd, htd, hdistortion⟩ := hnativeContraction
  have hAnyDistortion (i j : ι)
      (b : Diffeomorph (complexModel 1) (complexModel 1) (L i) (L j) ∞)
      (n : ℕ) (hb : ∀ p, (F.partition.leaf j).inclusion (b p) =
        (f : X → X)^[n] ((F.partition.leaf i).inclusion p)) (x y : L i) :
      intrinsicHermitianLeafEDist (r := 2) (F.partition.leaf j).inclusion h (b x) (b y) ≤
        ENNReal.ofReal (Cd * td ^ n) *
          intrinsicHermitianLeafEDist (r := 2) (F.partition.leaf i).inclusion h x y := by
    obtain ⟨k, e, he, hed⟩ := hdistortion i x n
    have hkj : k = j := F.partition.disjoint k j (e x) (b x)
      ((he x).trans (hb x).symm)
    subst k
    have heq : ∀ p, e p = b p := fun p ↦
      (F.partition.leaf j).injective ((he p).trans (hb p).symm)
    simpa only [heq] using hed x y
  have hdecay : Filter.Tendsto (fun n : ℕ ↦ Cd * td ^ n) Filter.atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one htd.1.le htd.2).const_mul Cd
  obtain ⟨block, hblockpos, hblock⟩ :=
    ((Filter.eventually_ge_atTop (1 : ℕ)).and
      (hdecay.eventually_lt_const (show (0 : ℝ) < 1 by norm_num))).exists
  have hSinvariant := localLinearization_complex_stable_derivative_image f a S hS
  let derivative (n : ℕ) (x : X) :
      S.toDistribution x ≃L[ℂ] S.toDistribution ((f : X → X)^[n] x) :=
    (hermitianBoundsDerivative f n x).ofSubmodules _ _
      (CompactHermitianBoundsScratch.actual_iterate_subspace_invariant
        f S.toDistribution hSinvariant n x)
  have hderivative (n : ℕ) (x : X) (v : S.toDistribution x) :
      (derivative n x v).val =
        mfderiv (complexModel d) (complexModel d) ((f : X → X)^[n]) x v.val := rfl
  have hderivativeBound (n : ℕ) (x : X) (v : S.toDistribution x) :
      Real.sqrt ((h ((f : X → X)^[n] x)).inner
        (derivative n x v).val (derivative n x v).val).re ≤
      C * rate ^ n * Real.sqrt ((h x).inner v.val v.val).re := by
    have hv : complexTangentToReal d x v.val ∈ a.splitting.stable.toDistribution x := by
      rw [← hS x]
      exact Submodule.mem_map.mpr ⟨v.val, v.property, rfl⟩
    have hbound := hs n x (complexTangentToReal d x v.val) hv
    rw [TranslationInvariantDescent.holomorphic_mfderiv_realification
      ((f.contMDiff.iterate n).mdifferentiable (by simp) x) v.val] at hbound
    simpa only [hermitianTangentRealPairing, hermitianTangentPairing,
      ContinuousLinearEquiv.symm_apply_apply, hderivative] using hbound
  clear_value derivative
  choose scalar chart hchartsource hchartK hcharthol hchartinv hcharttarget hchartnorm
    using hcharts
  have hchartcenter (i : ι) (z : L i) : chart i z z = 0 := by
    rw [hchartK i z z]
    · exact hcenter _
    · exact hself i z
  let component (i : ι) (z : L i) := connectedComponentIn (chart i z).source z
  have hComponentEntry (i : ι) (z p : L i) :
      ∀ᶠ n in Filter.atTop,
        ∃ (j : ι) (b : Diffeomorph (complexModel 1) (complexModel 1) (L i) (L j) ∞),
          (∀ q, (F.partition.leaf j).inclusion (b q) =
            (f : X → X)^[n] ((F.partition.leaf i).inclusion q)) ∧
          b p ∈ component j (b z) := by
    filter_upwards [nativeStableLeaf_eventual_coordinate_domain_entry
        f a S hS h hh F i z p r hr, hActualCoordinateEntry i z p ε hε] with n hn hsmall
    obtain ⟨j, b, hb, hdist⟩ := hn
    refine ⟨j, b, hb, ?_⟩
    change b p ∈ connectedComponentIn (chart j (b z)).source (b z)
    have hzsrc : b z ∈ (chart j (b z)).source := by
      rw [hchartsource]
      exact hself j (b z)
    have hpsrc : b p ∈ (chart j (b z)).source := by
      rw [hchartsource]
      exact hdist
    refine partialChart_hermitian_component_entry
      (X := L j) (E := TangentSpace (complexModel d)
        ((F.partition.leaf j).inclusion (b z)))
      (S.toDistribution ((F.partition.leaf j).inclusion (b z)))
      (h ((F.partition.leaf j).inclusion (b z))) (chart j (b z))
      hzsrc hpsrc (hchartcenter j (b z)) hε (hcharttarget j (b z)) ?_
    rw [hchartK j (b z) (b p) hdist]
    let normK : X → X → ℝ := fun x y ↦
      Real.sqrt ((h x).inner (K x y).val (K x y).val).re
    change normK ((F.partition.leaf j).inclusion (b z))
      ((F.partition.leaf j).inclusion (b p)) < ε
    change normK ((f : X → X)^[n] ((F.partition.leaf i).inclusion z))
      ((f : X → X)^[n] ((F.partition.leaf i).inclusion p)) < ε at hsmall
    rwa [hb z, hb p]
  have hComponentCenter (i : ι) (z : L i) : z ∈ component i z :=
    mem_connectedComponentIn (by rw [hchartsource]; exact hself i z)
  have hComponentOpen (i : ι) (z : L i) : IsOpen (component i z) := by
    letI : LocallyConnectedSpace (L i) :=
      ChartedSpace.locallyConnectedSpace (ComplexModel 1) (L i)
    exact (chart i z).open_source.connectedComponentIn
  have hComponentMap (i j : ι) (z : L i)
      (b : Diffeomorph (complexModel 1) (complexModel 1) (L i) (L j) ∞)
      (hb : ∀ p, (F.partition.leaf j).inclusion (b p) =
        (f : X → X)^[block] ((F.partition.leaf i).inclusion p)) :
      Set.MapsTo b (component i z) (component j (b z)) := by
    have hsrc : Set.MapsTo b (chart i z).source (chart j (b z)).source := by
      intro p hp
      rw [hchartsource] at hp ⊢
      have hc : ENNReal.ofReal (Cd * td ^ block) ≤ 1 := by
        simpa using ENNReal.ofReal_le_ofReal hblock.le
      exact (hAnyDistortion i j b block hb z p).trans_lt
        ((mul_le_mul_of_nonneg_right hc (by positivity)).trans_lt (by simpa using hp))
    have himg : IsPreconnected (b '' component i z) :=
      isPreconnected_connectedComponentIn.image _ b.continuous.continuousOn
    have hsub : b '' component i z ⊆ (chart j (b z)).source := by
      rintro _ ⟨p, hp, rfl⟩
      exact hsrc (connectedComponentIn_subset _ _ hp)
    exact fun p hp ↦ himg.subset_connectedComponentIn
      ⟨z, hComponentCenter i z, rfl⟩ hsub ⟨p, hp, rfl⟩
  have hChartSmooth (i : ι) (z : L i) :
      ContMDiffOn (complexModel 1) 𝓘(ℂ, S.toDistribution ((F.partition.leaf i).inclusion z))
        ∞ (chart i z) (chart i z).source := by
    have hc := (scalar i z).symm.contDiff.contMDiff.comp_contMDiffOn (hcharthol i z)
    simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply, ← hchartsource] using hc
  have hChartInverseSmooth (i : ι) (z : L i) :
      ContMDiffOn 𝓘(ℂ, S.toDistribution ((F.partition.leaf i).inclusion z)) (complexModel 1)
        ∞ (chart i z).symm (chart i z).target := by
    have hc := (hchartinv i z).comp (scalar i z).contDiff.contMDiff.contMDiffOn
      (fun p hp ↦ by simpa using hp)
    simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using hc
  have hGlobal (i : ι) (z : L i) :
      ∃ φ : Diffeomorph (complexModel 1)
          𝓘(ℂ, S.toDistribution ((F.partition.leaf i).inclusion z))
          (L i) (S.toDistribution ((F.partition.leaf i).inclusion z)) ∞,
        ∀ᶠ p in 𝓝 z, φ p = K ((F.partition.leaf i).inclusion z)
          ((F.partition.leaf i).inclusion p) := by
    choose leaf lift hlift using fun n ↦ hnativeTransport i z (n * block)
    let x := (F.partition.leaf i).inclusion z
    have hsub (n : ℕ) : S.toDistribution ((f : X → X)^[n * block] x) =
        S.toDistribution ((F.partition.leaf (leaf n)).inclusion (lift n z)) := by
      dsimp [x]
      rw [hlift n z]
    let Dn (n : ℕ) : S.toDistribution x ≃L[ℂ]
        S.toDistribution ((F.partition.leaf (leaf n)).inclusion (lift n z)) :=
      (hermitianBoundsDerivative f (n * block) x).ofSubmodules _ _
        ((CompactHermitianBoundsScratch.actual_iterate_subspace_invariant
          f S.toDistribution hSinvariant (n * block) x).trans (hsub n))
    have hDn (n : ℕ) (v : S.toDistribution x) :
        (Dn n v).val = mfderiv (complexModel d) (complexModel d)
          ((f : X → X)^[n * block]) x v.val := rfl
    clear_value Dn
    let e (n : ℕ) : OpenPartialHomeomorph (L i) (S.toDistribution x) :=
      ((lift n).toHomeomorph.transOpenPartialHomeomorph
        ((chart (leaf n) (lift n z)).restrOpen
          (component (leaf n) (lift n z)) (hComponentOpen _ _))).transHomeomorph
            (Dn n).symm.toHomeomorph
    have hesource (n : ℕ) : (e n).source = (lift n) ⁻¹' component (leaf n) (lift n z) := by
      change (lift n) ⁻¹' ((chart (leaf n) (lift n z)).source ∩
        component (leaf n) (lift n z)) = _
      rw [Set.inter_eq_right.mpr (connectedComponentIn_subset _ _)]
    have hecenter (n : ℕ) : z ∈ (e n).source := by
      rw [hesource]
      exact hComponentCenter _ _
    have hemonotone : Monotone fun n ↦ (e n).source := by
      apply monotone_nat_of_le_succ
      intro n p hp
      rw [hesource] at hp ⊢
      let b := (lift n).symm.trans (lift (n + 1))
      have hb : ∀ q, (F.partition.leaf (leaf (n + 1))).inclusion (b q) =
          (f : X → X)^[block] ((F.partition.leaf (leaf n)).inclusion q) := by
        intro q
        change (F.partition.leaf (leaf (n + 1))).inclusion
          (lift (n + 1) ((lift n).symm q)) = _
        rw [hlift]
        have hq := hlift n ((lift n).symm q)
        rw [(lift n).apply_symm_apply] at hq
        rw [hq, Nat.add_mul, one_mul, Nat.add_comm, Function.iterate_add_apply]
      have hmap := hComponentMap (leaf n) (leaf (n + 1)) (lift n z) b hb hp
      change (lift (n + 1)) p ∈ component (leaf (n + 1)) ((lift (n + 1)) z)
      simpa only [b, Diffeomorph.coe_trans, Function.comp_apply, Diffeomorph.symm_apply_apply] using hmap
    have heconnected (n : ℕ) : IsPreconnected (e n).source := by
      rw [hesource, ← (lift n).symm_image_eq_preimage]
      exact isPreconnected_connectedComponentIn.image _ (lift n).symm.continuous.continuousOn
    have heK (n : ℕ) : (e n : L i → S.toDistribution x) =ᶠ[𝓝 z]
        (fun p ↦ K x ((F.partition.leaf i).inclusion p)) := by
      filter_upwards [(lift n).continuous.continuousAt.eventually
          ((hComponentOpen (leaf n) (lift n z)).mem_nhds
            (hComponentCenter (leaf n) (lift n z))),
        hKiterate i z (n * block)] with p hp hrec
      apply (Dn n).injective
      change Dn n ((Dn n).symm (chart (leaf n) (lift n z) (lift n p))) = _
      rw [(Dn n).apply_symm_apply, hchartK _ _ _
        (by rw [← hchartsource]; exact connectedComponentIn_subset _ _ hp)]
      apply Subtype.ext
      rw [hDn]
      let Kv : X → X → ComplexModel d := fun x y ↦ (K x y).val
      change Kv ((F.partition.leaf (leaf n)).inclusion (lift n z))
        ((F.partition.leaf (leaf n)).inclusion (lift n p)) = _
      rw [hlift n z, hlift n p]
      exact hrec
    have hecover : ∀ p, ∃ n, p ∈ (e n).source := by
      intro p
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hComponentEntry i z p)
      obtain ⟨j, b, hb, hp⟩ := hN (N * block) (Nat.le_mul_of_pos_right N hblockpos)
      have hj : j = leaf N := F.partition.disjoint j (leaf N) (b z) (lift N z)
        ((hb z).trans (hlift N z).symm)
      subst j
      have heq : ∀ q, b q = lift N q := fun q ↦
        (F.partition.leaf (leaf N)).injective ((hb q).trans (hlift N q).symm)
      refine ⟨N, ?_⟩
      rw [hesource]
      change (lift N) p ∈ component (leaf N) ((lift N) z)
      simpa only [heq] using hp
    have hesmooth (n : ℕ) : ContMDiffOn (complexModel 1)
        𝓘(ℂ, S.toDistribution x) ∞ (e n) (e n).source := by
      apply (Dn n).symm.contDiff.contMDiff.comp_contMDiffOn
      apply (hChartSmooth (leaf n) (lift n z)).comp (lift n).contMDiff.contMDiffOn
      intro p hp
      exact hp.1
    have heinverse (n : ℕ) : ContMDiffOn 𝓘(ℂ, S.toDistribution x)
        (complexModel 1) ∞ (e n).symm (e n).target := by
      apply (lift n).symm.contMDiff.comp_contMDiffOn
      apply (hChartInverseSmooth (leaf n) (lift n z)).comp
        (Dn n).contDiff.contMDiff.contMDiffOn
      intro v hv
      exact hv.1
    have hetarget : ∀ v, ∃ n, v ∈ (e n).target := by
      intro v
      have hsmall : Filter.Tendsto
          (fun n : ℕ ↦ C * rate ^ n * Real.sqrt ((h x).inner v.val v.val).re)
          Filter.atTop (𝓝 0) := by
        simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hrate.1.le hrate.2).const_mul C).mul_const
          (Real.sqrt ((h x).inner v.val v.val).re)
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hsmall.eventually_lt_const hε)
      have hbound := (hderivativeBound (N * block) x v).trans_lt
        (hN (N * block) (Nat.le_mul_of_pos_right N hblockpos))
      have hvsmall : Real.sqrt ((h ((F.partition.leaf (leaf N)).inclusion (lift N z))).inner
          (Dn N v).val (Dn N v).val).re < ε := by
        rw [hDn, hlift N z]
        simpa only [hderivative] using hbound
      have hvt := hcharttarget (leaf N) (lift N z) (Dn N v) hvsmall
      refine ⟨N, hvt, ?_⟩
      have hzsrc : lift N z ∈ (chart (leaf N) (lift N z)).source := by
        rw [hchartsource]
        exact hself _ _
      have hpsrc := (chart (leaf N) (lift N z)).map_target hvt
      refine partialChart_hermitian_component_entry
        (S.toDistribution ((F.partition.leaf (leaf N)).inclusion (lift N z)))
        (h ((F.partition.leaf (leaf N)).inclusion (lift N z)))
        (chart (leaf N) (lift N z)) hzsrc hpsrc
        (hchartcenter (leaf N) (lift N z)) hε (hcharttarget (leaf N) (lift N z)) ?_
      change Real.sqrt ((h ((F.partition.leaf (leaf N)).inclusion (lift N z))).inner
        ((chart (leaf N) (lift N z)) ((chart (leaf N) (lift N z)).symm (Dn N v))).val
        ((chart (leaf N) (lift N z)) ((chart (leaf N) (lift N z)).symm (Dn N v))).val).re < ε
      rwa [(chart (leaf N) (lift N z)).right_inv hvt]
    obtain ⟨φ, hφ⟩ := line_biholomorph_of_exhaustion_of_germs
      ((scalar i z).trans (ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ).symm)
      e z (hecenter 0) hemonotone heconnected
      (fun n ↦ (heK n).trans (heK 0).symm) hecover hetarget hesmooth heinverse
    refine ⟨φ, ?_⟩
    exact (Filter.eventuallyEq_of_mem ((e 0).open_source.mem_nhds (hecenter 0))
      (hφ 0)).trans (heK 0)
  choose φ hφgerm using hGlobal
  have hφchart (i : ι) (z : L i) : Set.EqOn (φ i z) (chart i z) (component i z) := by
    apply line_holomorphic_eqOn_of_germ
      ((scalar i z).trans (ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ).symm)
      _ _ (hComponentOpen i z) isPreconnected_connectedComponentIn (hComponentCenter i z)
      (φ i z).contMDiff.contMDiffOn
      ((hChartSmooth i z).mono (connectedComponentIn_subset _ _))
    filter_upwards [hφgerm i z, (chart i z).open_source.mem_nhds
      (by rw [hchartsource]; exact hself i z)] with p hp hpchart
    exact hp.trans (hchartK i z p (by rwa [← hchartsource])).symm
  have hφcenter (i : ι) (z : L i) : φ i z z = 0 :=
    (hφchart i z (hComponentCenter i z)).trans (hchartcenter i z)
  have hφnormalization (i : ι) (z : L i)
      (v : TangentSpace (complexModel 1) z) :
      (mfderiv (complexModel 1) 𝓘(ℂ, S.toDistribution ((F.partition.leaf i).inclusion z))
        (φ i z) z v).val =
      mfderiv (complexModel 1) (complexModel d) (F.partition.leaf i).inclusion z v := by
    set_option backward.isDefEq.respectTransparency false in
      have hg := (hφgerm i z).mono (fun p hp ↦ congrArg (scalar i z) hp)
      have hdg := Filter.EventuallyEq.mfderiv_eq (I := complexModel 1) (I' := 𝓘(ℂ, ℂ)) hg
      change mfderiv (complexModel 1) 𝓘(ℂ, ℂ) (fun p ↦ scalar i z (φ i z p)) z =
        mfderiv (complexModel 1) 𝓘(ℂ, ℂ)
          (fun p ↦ scalar i z (K ((F.partition.leaf i).inclusion z)
            ((F.partition.leaf i).inclusion p))) z at hdg
      have hnorm := congrArg (fun A ↦ A v) (hchartnorm i z)
      change ((scalar i z).symm
        (mfderiv (complexModel 1) 𝓘(ℂ, ℂ)
          (fun p ↦ scalar i z (K ((F.partition.leaf i).inclusion z)
            ((F.partition.leaf i).inclusion p))) z v)).val = _ at hnorm
      have hc := (scalar i z).hasMFDerivAt.comp z
        (((φ i z).contMDiff.mdifferentiable (by simp) z).hasMFDerivAt)
      have hcv := congrArg (fun A ↦ A v) hc.mfderiv
      change mfderiv (complexModel 1) 𝓘(ℂ, ℂ)
        (fun p ↦ scalar i z (φ i z p)) z v =
        scalar i z (mfderiv (complexModel 1)
          𝓘(ℂ, S.toDistribution ((F.partition.leaf i).inclusion z)) (φ i z) z v) at hcv
      have hvalue : scalar i z (mfderiv (complexModel 1)
          𝓘(ℂ, S.toDistribution ((F.partition.leaf i).inclusion z)) (φ i z) z v) =
          mfderiv (complexModel 1) 𝓘(ℂ, ℂ)
            (fun p ↦ scalar i z (K ((F.partition.leaf i).inclusion z)
              ((F.partition.leaf i).inclusion p))) z v :=
        hcv.symm.trans (congrArg (fun A ↦ A v) hdg)
      have hresult := (congrArg (fun c : ℂ ↦ ((scalar i z).symm c).val) hvalue).trans hnorm
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using hresult
  have hφtransport (i j : ι) (z : L i) (n : ℕ)
      (b : Diffeomorph (complexModel 1) (complexModel 1) (L i) (L j) ∞)
      (hb : ∀ p, (F.partition.leaf j).inclusion (b p) =
        (f : X → X)^[n] ((F.partition.leaf i).inclusion p)) (p : L i) :
      (φ j (b z) (b p)).val = mfderiv (complexModel d) (complexModel d)
        ((f : X → X)^[n]) ((F.partition.leaf i).inclusion z) (φ i z p).val := by
    set_option backward.isDefEq.respectTransparency false in
      let E : S.toDistribution ((F.partition.leaf i).inclusion z) ≃L[ℂ]
          S.toDistribution ((F.partition.leaf j).inclusion (b z)) :=
        (hermitianBoundsDerivative f n ((F.partition.leaf i).inclusion z)).ofSubmodules _ _
          ((CompactHermitianBoundsScratch.actual_iterate_subspace_invariant
            f S.toDistribution hSinvariant n ((F.partition.leaf i).inclusion z)).trans
              (by change S.toDistribution ((f : X → X)^[n] ((F.partition.leaf i).inclusion z)) = _; rw [hb z]))
      have hE (v : S.toDistribution ((F.partition.leaf i).inclusion z)) :
          (E v).val = mfderiv (complexModel d) (complexModel d) ((f : X → X)^[n])
            ((F.partition.leaf i).inclusion z) v.val := rfl
      clear_value E
      letI := (F.partition.leaf i).connected
      have heq : Set.EqOn (fun q ↦ φ j (b z) (b q)) (fun q ↦ E (φ i z q)) Set.univ := by
        apply line_holomorphic_eqOn_of_germ
          ((scalar j (b z)).trans (ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ).symm)
          _ _ isOpen_univ isPreconnected_univ (Set.mem_univ z)
          ((φ j (b z)).contMDiff.comp b.contMDiff).contMDiffOn
          (E.contDiff.contMDiff.comp (φ i z).contMDiff).contMDiffOn
        filter_upwards [hφgerm i z, b.continuous.continuousAt.eventually (hφgerm j (b z)),
          hKiterate i z n] with q hq hq' hrec
        change φ j (b z) (b q) = E (φ i z q)
        rw [hq, hq']
        apply Subtype.ext
        rw [hE]
        let Kv : X → X → ComplexModel d := fun x y ↦ (K x y).val
        change Kv ((F.partition.leaf j).inclusion (b z))
          ((F.partition.leaf j).inclusion (b q)) =
            mfderiv (complexModel d) (complexModel d) ((f : X → X)^[n])
              ((F.partition.leaf i).inclusion z) (K ((F.partition.leaf i).inclusion z)
                ((F.partition.leaf i).inclusion q)).val
        calc
          _ = Kv ((f : X → X)^[n] ((F.partition.leaf i).inclusion z))
              ((f : X → X)^[n] ((F.partition.leaf i).inclusion q)) :=
            congrArg₂ Kv (hb z) (hb q)
          _ = _ := hrec
      exact (congrArg Subtype.val (heq (Set.mem_univ p))).trans (hE _)
  choose base point hpoint using F.partition.cover
  let evaluation (x : X) (v : S.toDistribution x) : X :=
    (F.partition.leaf (base x)).inclusion
      ((φ (base x) (point x)).symm ⟨v.val, by rw [hpoint]; exact v.property⟩)
  have hEvaluation (i : ι) (z : L i) (v : S.toDistribution ((F.partition.leaf i).inclusion z)) :
      evaluation ((F.partition.leaf i).inclusion z) v =
        (F.partition.leaf i).inclusion ((φ i z).symm v) := by
    have hsame (j : ι) (w : L j)
        (hw : (F.partition.leaf j).inclusion w = (F.partition.leaf i).inclusion z) :
        (F.partition.leaf j).inclusion ((φ j w).symm
          ⟨v.val, by rw [hw]; exact v.property⟩) =
        (F.partition.leaf i).inclusion ((φ i z).symm v) := by
      have hji : j = i := F.partition.disjoint j i w z hw
      subst j
      have hwz : w = z := (F.partition.leaf i).injective hw
      subst w
      rfl
    exact hsame (base ((F.partition.leaf i).inclusion z))
      (point ((F.partition.leaf i).inclusion z)) (hpoint _)
  clear_value evaluation
  clear base point hpoint
  have hEvaluationSmall (x : X) (v : S.toDistribution x)
      (hv : Real.sqrt ((h x).inner v.val v.val).re < ε) :
      evaluation x v = inverse ⟨x, v⟩ := by
    obtain ⟨i, z, rfl⟩ := F.partition.cover x
    rw [hEvaluation]
    have hvt := hcharttarget i z v hv
    have hqsrc := (chart i z).map_target hvt
    have hqcomp : (chart i z).symm v ∈ component i z := by
      have hzsrc : z ∈ (chart i z).source := by
        rw [hchartsource]
        exact hself i z
      refine partialChart_hermitian_component_entry
        (S.toDistribution ((F.partition.leaf i).inclusion z))
        (h ((F.partition.leaf i).inclusion z)) (chart i z)
        hzsrc hqsrc (hchartcenter i z)
        hε (hcharttarget i z) ?_
      rwa [(chart i z).right_inv hvt]
    have hφq : φ i z ((chart i z).symm v) = v :=
      (hφchart i z hqcomp).trans ((chart i z).right_inv hvt)
    have hq : (φ i z).symm v = (chart i z).symm v := by
      exact (congrArg (φ i z).symm hφq).symm.trans ((φ i z).symm_apply_apply _)
    rw [hq]
    have hqdist := hqsrc
    rw [hchartsource] at hqdist
    have hKq := hchartK i z ((chart i z).symm v) hqdist
    rw [(chart i z).right_inv hvt] at hKq
    have hF := hForward (((F.partition.leaf i).inclusion z),
      ((F.partition.leaf i).inclusion ((chart i z).symm v)))
      ⟨i, z, (chart i z).symm v, rfl, rfl, hqdist⟩
    dsimp only at hF
    rw [← hKq] at hF
    exact hF.symm
  have hSmallInO (x : X) (v : S.toDistribution x)
      (hv : Real.sqrt ((h x).inner v.val v.val).re < ε) :
      (⟨x, v⟩ : Bundle.TotalSpace (ComplexModel d) (fun x ↦ ↥(S.toDistribution x))) ∈ O := by
    obtain ⟨i, z, rfl⟩ := F.partition.cover x
    have hvt := hcharttarget i z v hv
    have hqdist := (chart i z).map_target hvt
    rw [hchartsource] at hqdist
    refine ⟨⟨(F.partition.leaf i).inclusion z,
        (F.partition.leaf i).inclusion ((chart i z).symm v)⟩,
      ⟨i, z, (chart i z).symm v, rfl, rfl, hqdist⟩, ?_⟩
    have hKq := hchartK i z ((chart i z).symm v) hqdist
    rw [(chart i z).right_inv hvt] at hKq
    simp only [hKq.symm]
  have hEvaluationIterate (x : X) (v : S.toDistribution x) (n : ℕ) :
      evaluation ((f : X → X)^[n] x) (derivative n x v) =
        (f : X → X)^[n] (evaluation x v) := by
    obtain ⟨i, z, rfl⟩ := F.partition.cover x
    obtain ⟨j, b, hb⟩ := hnativeTransport i z n
    let w : S.toDistribution ((F.partition.leaf j).inclusion (b z)) :=
      ⟨(derivative n ((F.partition.leaf i).inclusion z) v).val,
        by rw [hb z]; exact (derivative n ((F.partition.leaf i).inclusion z) v).property⟩
    have hw : φ j (b z) (b ((φ i z).symm v)) = w := by
      apply Subtype.ext
      rw [hφtransport i j z n b hb, (φ i z).apply_symm_apply]
      exact (hderivative n ((F.partition.leaf i).inclusion z) v).symm
    have hvalue : evaluation ((F.partition.leaf j).inclusion (b z)) w =
        (F.partition.leaf j).inclusion (b ((φ i z).symm v)) := by
      rw [hEvaluation, ← hw, (φ j (b z)).symm_apply_apply]
    have hleft : evaluation ((F.partition.leaf j).inclusion (b z)) w =
        evaluation ((f : X → X)^[n] ((F.partition.leaf i).inclusion z))
          (derivative n ((F.partition.leaf i).inclusion z) v) := by
      have htransport (x y : X) (he : x = y) (v : S.toDistribution y)
          (w : S.toDistribution x) (hw : w.val = v.val) : evaluation x w = evaluation y v := by
        subst y
        have : w = v := Subtype.ext hw
        subst w
        rfl
      exact htransport _ _ (hb z) _ w rfl
    rw [← hleft, hvalue, hb, hEvaluation]
  have hEvaluationFormula (x : X) (v : S.toDistribution x) (n : ℕ)
      (hv : Real.sqrt ((h ((f : X → X)^[n] x)).inner
        (derivative n x v).val (derivative n x v).val).re < ε) :
      evaluation x v = (hermitianBoundsIterate f n).symm
        (inverse ⟨(f : X → X)^[n] x, derivative n x v⟩) := by
    rw [← hEvaluationSmall _ _ hv, hEvaluationIterate]
    exact ((hermitianBoundsIterate f n).symm_apply_apply (evaluation x v)).symm
  let totalDerivative (n : ℕ)
      (v : {v : TangentBundle (complexModel d) X // v.snd ∈ S.toDistribution v.proj}) :
      Bundle.TotalSpace (ComplexModel d) (fun x ↦ ↥(S.toDistribution x)) :=
    ⟨(f : X → X)^[n] v.val.proj, derivative n v.val.proj ⟨v.val.snd, v.property⟩⟩
  have hTotalDerivative (n : ℕ) : Continuous (totalDerivative n) := by
    apply continuous_induced_rng.mpr
    apply ((NativeOperatorPreparation.continuous_iterate_derivative_total f n).comp
      continuous_subtype_val).congr
    intro v
    exact congrArg (fun w : TangentSpace (complexModel d) ((f : X → X)^[n] v.val.proj) ↦
      (⟨(f : X → X)^[n] v.val.proj, w⟩ : TangentBundle (complexModel d) X))
        (hderivative n v.val.proj ⟨v.val.snd, v.property⟩).symm
  let totalNorm (n : ℕ)
      (v : {v : TangentBundle (complexModel d) X // v.snd ∈ S.toDistribution v.proj}) : ℝ :=
    Real.sqrt ((h (totalDerivative n v).proj).inner
      (totalDerivative n v).snd.val (totalDerivative n v).snd.val).re
  have hTotalNorm (n : ℕ) : Continuous (totalNorm n) := by
    exact (Preparation.continuous_hermitian_tangent_norm h hh).comp
      (continuous_induced_dom.comp (hTotalDerivative n))
  have hEvaluationContinuous : Continuous
      (fun v : {v : TangentBundle (complexModel d) X // v.snd ∈ S.toDistribution v.proj} ↦
        evaluation v.val.proj ⟨v.val.snd, v.property⟩) := by
    rw [continuous_iff_continuousAt]
    intro v
    have hsmall : Filter.Tendsto (fun n : ℕ ↦ C * rate ^ n *
        Real.sqrt ((h v.val.proj).inner v.val.snd v.val.snd).re)
        Filter.atTop (𝓝 0) := by
      simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hrate.1.le hrate.2).const_mul C).mul_const
        (Real.sqrt ((h v.val.proj).inner v.val.snd v.val.snd).re)
    obtain ⟨n, hn⟩ := (hsmall.eventually_lt_const hε).exists
    have hv : totalNorm n v < ε :=
      (hderivativeBound n v.val.proj ⟨v.val.snd, v.property⟩).trans_lt hn
    have hmem : totalDerivative n v ∈ O := hSmallInO _ _ hv
    have hcont : ContinuousAt (fun w ↦ (hermitianBoundsIterate f n).symm
        (inverse (totalDerivative n w))) v :=
      (hermitianBoundsIterate f n).symm.continuous.continuousAt.comp
        ((hInvCont.continuousAt (hOopen.mem_nhds hmem)).comp
          (hTotalDerivative n).continuousAt)
    apply hcont.congr_of_eventuallyEq
    filter_upwards [(hTotalNorm n).continuousAt.eventually (gt_mem_nhds hv)] with w hw
    exact hEvaluationFormula _ _ n hw
  choose pairV hPairCenter pairσ pairt hpσ hpnz hppar hpt hpsub hpformula using
    fun x : X ↦ transverse_parallel_coordinates hd X f a hstable U hunstable hU
      nabla hcontinuous hcompatible hinvariant x
  have hPairCover : (Set.univ : Set X) ⊆ ⋃ x, (pairV x : Set X) := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, hPairCenter x⟩
  obtain ⟨δ, hδ, hδcover⟩ := lebesgue_number_lemma_of_metric isCompact_univ
    (fun x ↦ (pairV x).isOpen) hPairCover
  choose selected hSelected using fun x ↦ hδcover x (Set.mem_univ x)
  let Dsmall : Set (X × X) := {xp | xp ∈ D ∧
    Real.sqrt ((h xp.1).inner (K xp.1 xp.2).val (K xp.1 xp.2).val).re < ε}
  let radial (q : (X × X) × Set.Icc (0 : ℝ) 1) :
      Bundle.TotalSpace (ComplexModel d) (fun x ↦ ↥(S.toDistribution x)) :=
    ⟨q.1.1, ((q.2.val : ℂ) • K q.1.1 q.1.2)⟩
  have hRadialSmall (q : (X × X) × Set.Icc (0 : ℝ) 1) (hq : q.1 ∈ Dsmall) :
      Real.sqrt ((h (radial q).proj).inner (radial q).snd.val (radial q).snd.val).re < ε := by
    have hconvex : Convex ℝ {v : S.toDistribution q.1.1 |
        Real.sqrt ((h q.1.1).inner v.val v.val).re < ε} :=
      (hermitian_core_ball_convex (h q.1.1) ε).linear_preimage
        ((S.toDistribution q.1.1).subtype.restrictScalars ℝ)
    have hzero : (0 : S.toDistribution q.1.1) ∈
        {v | Real.sqrt ((h q.1.1).inner v.val v.val).re < ε} := by
      simpa only [Set.mem_ofPred_eq, Submodule.coe_zero,
        InnerProductSpace.Core.inner_zero_left, Complex.zero_re, Real.sqrt_zero] using hε
    exact hconvex.smul_mem_of_zero_mem hzero hq.2 q.2.property
  have hRadialContinuous : ContinuousOn radial (Dsmall ×ˢ Set.univ) := by
    let incl := fun w : Bundle.TotalSpace (ComplexModel d)
      (fun x ↦ ↥(S.toDistribution x)) ↦
        (⟨w.proj, w.snd.val⟩ : TangentBundle (complexModel d) X)
    have hind : Topology.IsInducing incl := ⟨rfl⟩
    apply hind.continuousOn_iff.mpr
    have hK : ContinuousOn
        (fun q : (X × X) × Set.Icc (0 : ℝ) 1 ↦
          incl ⟨q.1.1, K q.1.1 q.1.2⟩) (Dsmall ×ˢ Set.univ) :=
      (continuous_induced_dom.comp_continuousOn hKcont).comp
        continuous_fst.continuousOn (fun q hq ↦ hq.1.1)
    have ht : Continuous (fun q : (X × X) × Set.Icc (0 : ℝ) 1 ↦ (q.2.val : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_snd)
    exact continuous_tangent_scale.comp_continuousOn (hK.prodMk ht.continuousOn)
  have hRadialDistance : ContinuousOn
      (fun q : (X × X) × Set.Icc (0 : ℝ) 1 ↦ dist (inverse (radial q)) q.1.1)
      (Dsmall ×ˢ Set.univ) :=
    continuous_dist.comp_continuousOn
      ((hInvCont.comp hRadialContinuous
        (fun q hq ↦ hSmallInO _ _ (hRadialSmall q hq.1))).prodMk
          continuous_fst.fst.continuousOn)
  have hRadialZero (x : X) (t : Set.Icc (0 : ℝ) 1) :
      inverse (radial ((x, x), t)) = x := by
    have hF := hForward (x, x) (hDdiag x)
    simpa only [radial, hcenter, smul_zero] using hF
  have hRadialEntry (i : ι) (z p : L i) :
      ∀ᶠ n in Filter.atTop, ∀ t : Set.Icc (0 : ℝ) 1,
        dist (inverse (radial
          (((f : X → X)^[n] ((F.partition.leaf i).inclusion z),
            (f : X → X)^[n] ((F.partition.leaf i).inclusion p)), t)))
          ((f : X → X)^[n] ((F.partition.leaf i).inclusion z)) < δ := by
    apply compact_diagonal_family_eventually_small Dsmall _ hRadialDistance
      (fun x ↦ ⟨hDdiag x, by simpa [hcenter, InnerProductSpace.Core.inner_zero_left] using hε⟩)
      (fun x t ↦ by rw [hRadialZero]; exact dist_self x)
      _ _ ((hOriginalDomainEntry i z p).and (hActualCoordinateEntry i z p ε hε)) _ hδ
    have hp : (F.partition.leaf i).inclusion p ∈ Set.range (F.partition.leaf i).inclusion :=
      ⟨p, rfl⟩
    rw [F.asymptotic i z] at hp
    change Filter.Tendsto (fun n : ℕ ↦ dist
      ((f : X → X)^[n] ((F.partition.leaf i).inclusion p))
      ((f : X → X)^[n] ((F.partition.leaf i).inclusion z))) Filter.atTop (𝓝 0) at hp
    convert hp using 1
    funext n
    exact dist_comm _ _
  let chosenDomain (i : ι) (z : L i) : Set (L i) :=
    connectedComponentIn ((chart i z).source ∩
      (F.partition.leaf i).inclusion ⁻¹' (pairV (selected ((F.partition.leaf i).inclusion z)))) z
  have hChosenSourceOpen (i : ι) (z : L i) :
      IsOpen ((chart i z).source ∩ (F.partition.leaf i).inclusion ⁻¹'
        (pairV (selected ((F.partition.leaf i).inclusion z)))) :=
    (chart i z).open_source.inter
      ((pairV _).isOpen.preimage (F.partition.leaf i).immersion.contMDiff.continuous)
  have hChosenCenter (i : ι) (z : L i) : z ∈ chosenDomain i z := by
    apply mem_connectedComponentIn
    exact ⟨by rw [hchartsource]; exact hself i z,
      hSelected _ (Metric.mem_ball_self hδ)⟩
  have hChosenOpen (i : ι) (z : L i) : IsOpen (chosenDomain i z) := by
    letI : LocallyConnectedSpace (L i) :=
      ChartedSpace.locallyConnectedSpace (ComplexModel 1) (L i)
    exact (hChosenSourceOpen i z).connectedComponentIn
  have hChosenComponent (i : ι) (z : L i) : chosenDomain i z ⊆ component i z := by
    exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (hChosenCenter i z) (fun p hp ↦ (connectedComponentIn_subset _ _ hp).1)
  set_option backward.isDefEq.respectTransparency false in
  have hφpairOn (i : ι) (z : L i) (V : Opens X) (t : X → ℂ)
      (ht : ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞ t V)
      (W : Set (L i)) (hWo : IsOpen W) (hWc : IsPreconnected W) (hzW : z ∈ W)
      (hWV : W ⊆ (F.partition.leaf i).inclusion ⁻¹' (V : Set X))
      (hg : ∀ᶠ p in 𝓝 z, φ i z p = normalizedLocalStableCoordinate S.toDistribution
        t ((F.partition.leaf i).inclusion z) ((F.partition.leaf i).inclusion p)) :
      Set.EqOn (φ i z) (fun p ↦ normalizedLocalStableCoordinate S.toDistribution
        t ((F.partition.leaf i).inclusion z) ((F.partition.leaf i).inclusion p)) W := by
    apply line_holomorphic_eqOn_of_germ
      ((scalar i z).trans (ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ).symm)
      _ _ hWo hWc hzW (φ i z).contMDiff.contMDiffOn _ hg
    apply (localStableCoordinateDerivative S.toDistribution t
      ((F.partition.leaf i).inclusion z)).inverse.contDiff.contMDiff.comp_contMDiffOn
    exact (ht.comp (F.complexUpgrade i).inclusion_holomorphic.contMDiffOn hWV).sub_const _
  have hChosenPair (i : ι) (z : L i) :
      Set.EqOn (φ i z) (fun p ↦ normalizedLocalStableCoordinate S.toDistribution
        (pairt (selected ((F.partition.leaf i).inclusion z)))
        ((F.partition.leaf i).inclusion z) ((F.partition.leaf i).inclusion p))
      (chosenDomain i z) := by
    let k := selected ((F.partition.leaf i).inclusion z)
    have hzV : (F.partition.leaf i).inclusion z ∈ pairV k :=
      hSelected _ (Metric.mem_ball_self hδ)
    have hg : ∀ᶠ p in 𝓝 z, φ i z p = normalizedLocalStableCoordinate S.toDistribution
        (pairt k) ((F.partition.leaf i).inclusion z) ((F.partition.leaf i).inclusion p) := by
      obtain ⟨W, hWo, hzW, hWV, hKeq⟩ :=
        hgerm (pairV k) (pairσ k) (pairt k) (hpσ k) (hpnz k) (hppar k) (hpt k)
          (fun x hx v ↦ (hpformula k x hx).1 v) i z hzV
      filter_upwards [hφgerm i z, hWo.mem_nhds hzW] with p hp hpW
      exact hp.trans (hKeq p hpW)
    exact hφpairOn i z (pairV k) (pairt k) (hpt k) (chosenDomain i z)
      (hChosenOpen i z) isPreconnected_connectedComponentIn (hChosenCenter i z)
      (fun p hp ↦ (connectedComponentIn_subset _ _ hp).2) hg
  have hChosenEntry (i : ι) (z p : L i) :
      ∀ᶠ n in Filter.atTop,
        ∃ (j : ι) (b : Diffeomorph (complexModel 1) (complexModel 1) (L i) (L j) ∞),
          (∀ q, (F.partition.leaf j).inclusion (b q) =
            (f : X → X)^[n] ((F.partition.leaf i).inclusion q)) ∧
          b p ∈ chosenDomain j (b z) := by
    filter_upwards [nativeStableLeaf_eventual_coordinate_domain_entry
        f a S hS h hh F i z p r hr, hActualCoordinateEntry i z p ε hε,
      hRadialEntry i z p] with n hn hsmall hrad
    obtain ⟨j, b, hb, hdist⟩ := hn
    have hxy : ((F.partition.leaf j).inclusion (b z),
        (F.partition.leaf j).inclusion (b p)) ∈ Dsmall := by
      refine ⟨⟨j, b z, b p, rfl, rfl, hdist⟩, ?_⟩
      let normK : X → X → ℝ := fun x y ↦ Real.sqrt ((h x).inner
        (K x y).val (K x y).val).re
      change normK ((F.partition.leaf j).inclusion (b z))
        ((F.partition.leaf j).inclusion (b p)) < ε
      rw [hb z, hb p]
      exact hsmall
    let v := K ((F.partition.leaf j).inclusion (b z)) ((F.partition.leaf j).inclusion (b p))
    let γ : Set.Icc (0 : ℝ) 1 → L j := fun t ↦ (chart j (b z)).symm ((t.val : ℂ) • v)
    have hvtarget (t : Set.Icc (0 : ℝ) 1) : (t.val : ℂ) • v ∈ (chart j (b z)).target := by
      apply hcharttarget j (b z) ((t.val : ℂ) • v)
      exact hRadialSmall
        (((F.partition.leaf j).inclusion (b z), (F.partition.leaf j).inclusion (b p)), t) hxy
    have hγ : Continuous γ := (chart j (b z)).symm.continuousOn.comp_continuous
      ((Complex.continuous_ofReal.comp continuous_subtype_val).smul continuous_const)
      hvtarget
    have hγambient (t : Set.Icc (0 : ℝ) 1) :
        (F.partition.leaf j).inclusion (γ t) = inverse
          (radial (((F.partition.leaf j).inclusion (b z),
            (F.partition.leaf j).inclusion (b p)), t)) := by
      have hsrc := (chart j (b z)).map_target (hvtarget t)
      rw [hchartsource] at hsrc
      have hKγ := hchartK j (b z) (γ t) hsrc
      change (chart j (b z)) ((chart j (b z)).symm ((t.val : ℂ) • v)) = _ at hKγ
      rw [(chart j (b z)).right_inv (hvtarget t)] at hKγ
      have hF := hForward ((F.partition.leaf j).inclusion (b z),
        (F.partition.leaf j).inclusion (γ t)) ⟨j, b z, γ t, rfl, rfl, hsrc⟩
      dsimp only at hF
      rw [← hKγ] at hF
      exact hF.symm
    let t0 : Set.Icc (0 : ℝ) 1 := ⟨0, by norm_num⟩
    let t1 : Set.Icc (0 : ℝ) 1 := ⟨1, by norm_num⟩
    have hγ0 : γ t0 = b z := by
      change (chart j (b z)).symm ((0 : ℂ) • v) = _
      rw [zero_smul, ← hchartcenter j (b z)]
      exact (chart j (b z)).left_inv (by rw [hchartsource]; exact hself j (b z))
    have hγ1 : γ t1 = b p := by
      change (chart j (b z)).symm ((1 : ℂ) • v) = _
      rw [one_smul]
      calc
        (chart j (b z)).symm v = (chart j (b z)).symm (chart j (b z) (b p)) :=
          congrArg (chart j (b z)).symm (hchartK j (b z) (b p) hdist).symm
        _ = b p := (chart j (b z)).left_inv (by rwa [hchartsource])
    have himg : IsPreconnected (Set.range γ) := isPreconnected_range hγ
    have hsubset : Set.range γ ⊆ (chart j (b z)).source ∩
        (F.partition.leaf j).inclusion ⁻¹'
          (pairV (selected ((F.partition.leaf j).inclusion (b z)))) := by
      rintro _ ⟨t, rfl⟩
      refine ⟨(chart j (b z)).map_target (hvtarget t), hSelected _ ?_⟩
      rw [Metric.mem_ball, hγambient]
      let Q : X → X → Set.Icc (0 : ℝ) 1 → ℝ := fun x y t ↦
        dist (inverse (radial ((x, y), t))) x
      change Q ((F.partition.leaf j).inclusion (b z))
        ((F.partition.leaf j).inclusion (b p)) t < δ
      rw [hb z, hb p]
      exact hrad t
    exact ⟨j, b, hb, himg.subset_connectedComponentIn ⟨t0, hγ0⟩ hsubset ⟨t1, hγ1⟩⟩
  refine ⟨φ, K, chosenDomain, evaluation, hφcenter, ?_, ?_, ?_, ?_, ?_,
    hEvaluation, hEvaluationContinuous, ?_⟩
  · intro i z v
    exact hφnormalization i z v
  · intro V σ t hvalid i z hzV
    obtain ⟨W, hWo, hzW, hWV, hKeq⟩ :=
      hgerm V σ t hvalid.1 hvalid.2.1 hvalid.2.2.1 hvalid.2.2.2.1
        hvalid.2.2.2.2.1 i z hzV
    filter_upwards [hφgerm i z, hWo.mem_nhds hzW] with p hp hpW
    exact ⟨hWV hpW, hp.trans (hKeq p hpW)⟩
  · intro i z
    let k := selected ((F.partition.leaf i).inclusion z)
    refine ⟨hChosenOpen i z, hChosenCenter i z, pairV k, pairσ k, pairt k,
      hSelected _ (Metric.mem_ball_self hδ),
      ⟨hpσ k, hpnz k, hppar k, hpt k,
        fun x hx v ↦ (hpformula k x hx).1 v, fun x hx ↦ (hpformula k x hx).2⟩, ?_⟩
    intro p hp
    have hsrc := (connectedComponentIn_subset _ _ hp).1
    have hKeq := hchartK i z p (by rwa [← hchartsource])
    have hφK := (hφchart i z (hChosenComponent i z hp)).trans hKeq
    exact ⟨(connectedComponentIn_subset _ _ hp).2,
      hφK.symm.trans (hChosenPair i z hp), hφK⟩
  · intro i z p
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hChosenEntry i z p)
    refine ⟨N, fun n hn ↦ ?_⟩
    obtain ⟨j, b, hb, hp⟩ := hN n hn
    refine ⟨j, b z, b p, hb z, hb p, hp, ?_⟩
    have hsrc := (connectedComponentIn_subset _ _ hp).1
    have hφK := (hφchart j (b z) (hChosenComponent j (b z) hp)).trans
      (hchartK j (b z) (b p) (by rwa [← hchartsource]))
    rw [← hφK]
    exact hφtransport i j z n b hb p
  · intro i j z p w q hw hq
    obtain ⟨k, b, hb⟩ := hnativeTransport i z 1
    have hb' : ∀ p, (F.partition.leaf k).inclusion (b p) =
        f ((F.partition.leaf i).inclusion p) := by simpa using hb
    have hkj : k = j := F.partition.disjoint k j (b z) w ((hb' z).trans hw.symm)
    subst k
    have hw' : b z = w := (F.partition.leaf j).injective ((hb' z).trans hw.symm)
    have hq' : b p = q := (F.partition.leaf j).injective ((hb' p).trans hq.symm)
    subst w
    subst q
    have ht := hφtransport i j z 1 b hb p
    change (φ j (b z) (b p)).val =
      mfderiv (complexModel d) (complexModel d) f
        ((F.partition.leaf i).inclusion z) (φ i z p).val at ht
    exact ht
  · intro box
    apply native_complete_chart_family_continuous S f.toHomeomorph F φ scalar ?_ box
    intro x
    refine ⟨pairV x, pairt x, hPairCenter x, hpt x, ?_, ?_⟩
    · intro y hy
      exact localLinearization_stable_coordinate_derivative_invertible
        f a S hS U hunstable (pairt x) y (F.finrank y) (hpformula x y hy).2
    · intro i z hz
      obtain ⟨W, hWo, hzW, hWV, hKeq⟩ :=
        hgerm (pairV x) (pairσ x) (pairt x) (hpσ x) (hpnz x) (hppar x) (hpt x)
          (fun y hy v ↦ (hpformula x y hy).1 v) i z hz
      filter_upwards [hφgerm i z, hWo.mem_nhds hzW] with p hp hpW
      exact hp.trans (hKeq p hpW)


end

end HolomorphicAnosov.Paper.Zhang
