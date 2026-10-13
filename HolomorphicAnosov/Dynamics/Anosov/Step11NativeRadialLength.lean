import HolomorphicAnosov.Geometry.HPSNativePlaqueFamilyData
import HolomorphicAnosov.Geometry.ContinuousOriginalNorm
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap

noncomputable section
open Set Filter MeasureTheory Manifold Bundle
open scoped ContDiff Manifold Bundle ENNReal _root_.Topology
namespace HolomorphicAnosov

variable {E V M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {D : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ,E) x)} {center : M}

/-- The actual parameter derivative of a native finite-C1 family is continuous
in the original tangent bundle. In its fixed receiving tangent trivialization
the chain rule identifies it with the stipulated jointly continuous coordinate
derivative. The tangent trivialization is a homeomorphism on its actual source.
Source: HPS (5.5), pp.61–63, actual first-jet continuity. -/
theorem NativePlaqueFamily.continuous_tangent_w04
    (P : NativePlaqueFamily 𝓘(ℝ,E) (V := V) D center) :
    Continuous (fun q : (P.centerDomain × Metric.ball (0 : V) P.radius) × V ↦
      (⟨(P.plaque q.1.1).param q.1.2.val,
        mfderiv 𝓘(ℝ,V) 𝓘(ℝ,E) (P.plaque q.1.1).param q.1.2.val q.2⟩ :
          TangentBundle 𝓘(ℝ,E) M)) := by
  let F := fun q : (P.centerDomain × Metric.ball (0 : V) P.radius) × V ↦
    (⟨(P.plaque q.1.1).param q.1.2.val,
      mfderiv 𝓘(ℝ,V) 𝓘(ℝ,E) (P.plaque q.1.1).param q.1.2.val q.2⟩ :
        TangentBundle 𝓘(ℝ,E) M)
  let e := trivializationAt E (TangentSpace 𝓘(ℝ,E) : M → Type _) P.receivingAnchor
  have hrange : F ⁻¹' e.source = univ := by
    apply eq_univ_of_forall
    intro q
    change (P.plaque q.1.1).param q.1.2.val ∈ (chartAt E P.receivingAnchor).source
    simpa only [extChartAt_source] using P.receiving_domain q.1.1 _ q.1.2.property
  apply (e.toOpenPartialHomeomorph.continuous_iff_continuous_comp_left hrange).mpr
  have hc := (P.jointly_continuous.comp continuous_fst).prodMk
    ((P.jointly_continuous_derivative.comp continuous_fst).clm_apply continuous_snd)
  apply hc.congr
  intro q
  apply Prod.ext
  · rfl
  · have hp : MDifferentiableAt 𝓘(ℝ,V) 𝓘(ℝ,E) (P.plaque q.1.1).param q.1.2.val :=
      (((P.plaque q.1.1).smooth q.1.2.val (by rw [P.domain_eq]; exact q.1.2.property)).contMDiffAt
        ((P.plaque q.1.1).domain_open.mem_nhds (by rw [P.domain_eq]; exact q.1.2.property))).mdifferentiableAt (by simp)
    have hchart : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E) (chartAt E P.receivingAnchor)
        ((P.plaque q.1.1).param q.1.2.val) :=
      (mdifferentiable_chart (I := 𝓘(ℝ,E)) P.receivingAnchor).mdifferentiableAt
        (by simpa only [extChartAt_source] using P.receiving_domain q.1.1 _ q.1.2.property)
    have hchain := congrArg (fun A ↦ A q.2) (mfderiv_comp q.1.2.val hchart hp)
    rw [mfderiv_eq_fderiv] at hchain
    change _ = (e (F q)).2
    rw [TangentBundle.trivializationAt_apply]
    change _ = tangentCoordChange 𝓘(ℝ,E) ((P.plaque q.1.1).param q.1.2.val)
      P.receivingAnchor ((P.plaque q.1.1).param q.1.2.val) (F q).snd
    rw [← mfderiv_chartAt_eq_tangentCoordChange (I := 𝓘(ℝ,E))
      (by simpa only [extChartAt_source] using P.receiving_domain q.1.1 _ q.1.2.property)]
    exact hchain

/-- On a compact center core and a closed inner parameter ball, the original
metric speeds of all bounded parameter vectors have one finite bound. The
native tangent continuity above, followed by the original bundle norm, is
continuous on the compact product of centers, points, and vectors. -/
theorem NativePlaqueFamily.uniform_tangent_bound_on_compact_w04 [FiniteDimensional ℝ V]
    (P : NativePlaqueFamily 𝓘(ℝ,E) (V := V) D center)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E
      (fun x : M ↦ TangentSpace 𝓘(ℝ,E) x))
    (K : Set P.centerDomain) (hK : IsCompact K) {r : ℝ} (hr : r < P.radius) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ,E) x) := ⟨g.toRiemannianMetric⟩
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p ∈ K, ∀ u ∈ Metric.closedBall (0 : V) r,
      ∀ v ∈ Metric.closedBall (0 : V) r,
        ‖mfderiv 𝓘(ℝ,V) 𝓘(ℝ,E) (P.plaque p).param u v‖ ≤ B := by
  let : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ,E) x) := ⟨g.toRiemannianMetric⟩
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let R := Metric.closedBall (0 : V) r
  let : CompactSpace R := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  have hR : R ⊆ Metric.ball (0 : V) P.radius := Metric.closedBall_subset_ball hr
  let input : (K × (R × R)) → (P.centerDomain × Metric.ball (0 : V) P.radius) × V :=
    fun q ↦ ((q.1.val, ⟨q.2.1.val,hR q.2.1.property⟩),q.2.2.val)
  have hi : Continuous input := by fun_prop
  have hc := FixedBlockEstimates.Native.continuous_original_norm g
    (fun q : K × (R × R) ↦ (P.plaque q.1.val).param q.2.1.val)
    (fun q ↦ mfderiv 𝓘(ℝ,V) 𝓘(ℝ,E) (P.plaque q.1.val).param q.2.1.val q.2.2.val)
    (P.continuous_tangent_w04.comp hi)
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro p hp u hu v hv
  have hb := hB (⟨p,hp⟩,(⟨u,hu⟩,⟨v,hv⟩)) (mem_univ _)
  have hb' : ‖mfderiv 𝓘(ℝ,V) 𝓘(ℝ,E) (P.plaque p).param u v‖ ≤ B := by
    simpa only [Real.norm_eq_abs, abs_norm] using hb
  exact hb'.trans (le_max_left B 0)

/-- Every radial connector in a compact core of a native finite-C1 plaque
family has uniformly bounded length in the supplied original smooth metric.
It is a C1 path with velocity in the original distribution. The segment lies
in the closed inner ball; the chain rule gives DΦ(t v)v, whose original norm
has the compact-product bound above. Integrating over the unit interval gives
that same bound. Zero-dimensional plaques and empty center cores are included.
Source: Lee §11 pp.275–279, applied to the HPS finite-C1 plaque data. -/
theorem NativePlaqueFamily.uniform_radial_length_w04 [FiniteDimensional ℝ V]
    (P : NativePlaqueFamily 𝓘(ℝ,E) (V := V) D center)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E
      (fun x : M ↦ TangentSpace 𝓘(ℝ,E) x))
    (K : Set P.centerDomain) (hK : IsCompact K) {r : ℝ} (hr0 : 0 < r) (hr : r < P.radius) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ,E) x) := ⟨g.toRiemannianMetric⟩
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p ∈ K, ∀ v ∈ Metric.closedBall (0 : V) r,
      let γ := (P.plaque p).param ∘ AffineMap.lineMap (0 : V) v
      ContMDiffOn 𝓘(ℝ) 𝓘(ℝ,E) 1 γ (Icc 0 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        mfderivWithin 𝓘(ℝ) 𝓘(ℝ,E) γ (Icc 0 1) t 1 ∈ D (γ t)) ∧
      pathELength 𝓘(ℝ,E) γ 0 1 ≤ ENNReal.ofReal B := by
  let : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ,E) x) := ⟨g.toRiemannianMetric⟩
  obtain ⟨B,hB0,hB⟩ := P.uniform_tangent_bound_on_compact_w04 g K hK hr
  refine ⟨B,hB0,?_⟩
  intro p hp v hv
  let η : ℝ →ᵃ[ℝ] V := AffineMap.lineMap 0 v
  have hη : ContMDiff 𝓘(ℝ) 𝓘(ℝ,V) ∞ η :=
    contMDiff_iff_contDiff.mpr (AffineMap.contDiff_lineMap _ _)
  have hmem (t : ℝ) (ht : t ∈ Icc 0 1) : η t ∈ Metric.closedBall (0 : V) r :=
    (convex_closedBall (0 : V) r).mapsTo_lineMap (Metric.mem_closedBall_self hr0.le) hv ht
  have hdomain (t : ℝ) (ht : t ∈ Icc 0 1) : η t ∈ (P.plaque p).domain := by
    rw [P.domain_eq]
    exact Metric.closedBall_subset_ball hr (hmem t ht)
  have hγ : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ,E) ∞ ((P.plaque p).param ∘ η) (Icc 0 1) :=
    (P.plaque p).smooth.comp hη.contMDiffOn (fun t ht ↦ hdomain t ht)
  have hvelocity (t : ℝ) (ht : t ∈ Icc 0 1) :
      mfderivWithin 𝓘(ℝ) 𝓘(ℝ,E) ((P.plaque p).param ∘ η) (Icc 0 1) t 1 =
        mfderiv 𝓘(ℝ,V) 𝓘(ℝ,E) (P.plaque p).param (η t) v := by
    have hd := mfderiv_comp_mfderivWithin t
      (((P.plaque p).smooth _ (hdomain t ht)).contMDiffAt
        ((P.plaque p).domain_open.mem_nhds (hdomain t ht)) |>.mdifferentiableAt (by simp))
      (hη.contMDiffOn.mdifferentiableOn (by simp) t ht)
      ((uniqueDiffOn_Icc zero_lt_one t ht).uniqueMDiffWithinAt)
    rw [hd]
    have hvη : mfderivWithin 𝓘(ℝ) 𝓘(ℝ,V) η (Icc 0 1) t 1 = v := by
      rw [mfderivWithin_eq_fderivWithin,
        AffineMap.hasDerivWithinAt_lineMap.hasFDerivWithinAt.fderivWithin
          (uniqueDiffOn_Icc zero_lt_one t ht)]
      change (1 : ℝ) • (v - 0) = v
      simp only [sub_zero, one_smul]
    exact congrArg (mfderiv 𝓘(ℝ,V) 𝓘(ℝ,E) (P.plaque p).param (η t)) hvη
  refine ⟨hγ.of_le (by simp), ?_, ?_⟩
  · intro t ht
    rw [hvelocity t ht]
    have hm : mfderiv 𝓘(ℝ,V) 𝓘(ℝ,E) (P.plaque p).param (η t) v ∈
        (mfderiv 𝓘(ℝ,V) 𝓘(ℝ,E) (P.plaque p).param (η t)).range := ⟨v,rfl⟩
    rw [(P.plaque p).tangent _ (hdomain t ht)] at hm
    exact hm
  · rw [pathELength_eq_lintegral_mfderivWithin_Icc]
    calc
      _ ≤ ∫⁻ _t in Icc (0 : ℝ) 1, ENNReal.ofReal B := by
        apply setLIntegral_mono' measurableSet_Icc
        intro t ht
        rw [hvelocity t ht, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hB p hp _ (hmem t ht) v hv)
      _ = _ := by simp

end HolomorphicAnosov
