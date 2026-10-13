import HolomorphicAnosov.Dynamics.ExponentialCutoffExtension.Base

noncomputable section
namespace HolomorphicAnosov.ExponentialCutoff
open Bundle Set ExponentialLift
open scoped Manifold ContDiff Topology _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- Metric pairing on an open coordinate domain. Source: the smooth metric
evaluation in HPS (1977), proof of Theorem 5.5, p.62. It
accepts the actual smooth tangent section supplied by a frame; no smoothness of
an arbitrary compact parameter set is inferred. -/
theorem contMDiffOn_metric_pairing_of_tangent_section
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (D : Set (M × E)) (_hD : IsOpen D)
    (v : ∀ z : M × E, TangentSpace 𝓘(ℝ, E) z.1)
    (hv : ContMDiffOn ((𝓘(ℝ, E)).prod 𝓘(ℝ, E))
      (𝓘(ℝ, E)).tangent ∞
      (fun z : M × E => (⟨z.1, v z⟩ : TangentBundle 𝓘(ℝ, E) M)) D) :
    ContMDiffOn ((𝓘(ℝ, E)).prod 𝓘(ℝ, E)) 𝓘(ℝ) ∞
      (fun z : M × E => g.inner z.1 (v z) (v z)) D := by
  let b : M × E → M := Prod.fst
  have hb : ContMDiffOn ((𝓘(ℝ, E)).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ b D :=
    contMDiffOn_fst
  have hpair := (g.contMDiff.comp_contMDiffOn hb).clm_bundle_apply₂
    (F₃ := ℝ) (E₃ := Bundle.Trivial M ℝ) hv hv
  intro z hz
  have hz' := hpair z hz
  exact (contMDiffWithinAt_totalSpace.mp hz').2

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- Source: HPS (1977), proof of Theorem 5.5, p.62. The preceding pairing
adapter composes with the scalar bump on any open
coordinate domain where the frame tangent section is smooth. -/
theorem contMDiffOn_metric_cutoff_of_tangent_section
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (δ : ℝ) (D : Set (M × E)) (hD : IsOpen D)
    (v : ∀ z : M × E, TangentSpace 𝓘(ℝ, E) z.1)
    (hv : ContMDiffOn ((𝓘(ℝ, E)).prod 𝓘(ℝ, E))
      (𝓘(ℝ, E)).tangent ∞
      (fun z : M × E => (⟨z.1, v z⟩ : TangentBundle 𝓘(ℝ, E) M)) D) :
    ContMDiffOn ((𝓘(ℝ, E)).prod 𝓘(ℝ, E)) 𝓘(ℝ) ∞
      (fun z : M × E => scalarBump
        (g.inner z.1 (v z) (v z) / δ ^ 2)) D := by
  have hq := contMDiffOn_metric_pairing_of_tangent_section g D hD v hv
  have hdiv : ContMDiffOn ((𝓘(ℝ, E)).prod 𝓘(ℝ, E)) 𝓘(ℝ) ∞
      (fun z : M × E => g.inner z.1 (v z) (v z) / δ ^ 2) D :=
    hq.div_const (δ ^ 2)
  exact scalarBump.contDiff.contMDiff.comp_contMDiffOn hdiv

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- The actual metric cutoff is smooth on the ambient preferred tangent frame.
Source: HPS p. 62; evaluate the smooth metric twice on the smooth inverse frame,
scale its squared value, and compose with the fixed smooth bump. -/
theorem contMDiffOn_fibreCutoff_frame
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (δ : ℝ) (s : M) :
    let e := trivializationAt E (TangentSpace 𝓘(ℝ, E)) s
    ContMDiffOn ((𝓘(ℝ, E)).prod 𝓘(ℝ, E)) 𝓘(ℝ) ∞
      (fun z : M × E ↦ fibreCutoff g δ z.1 (e.symmL ℝ z.1 z.2))
      {z : M × E | z.1 ∈ e.baseSet} := by
  dsimp only
  let e := trivializationAt E (TangentSpace 𝓘(ℝ, E)) s
  let D : Set (M × E) := {z | z.1 ∈ e.baseSet}
  let v := fun z : M × E ↦ e.symmL ℝ z.1 z.2
  have hD : IsOpen D := e.open_baseSet.preimage continuous_fst
  have hv : ContMDiffOn ((𝓘(ℝ, E)).prod 𝓘(ℝ, E)) (𝓘(ℝ, E)).tangent ∞
      (fun z : M × E ↦ (⟨z.1, v z⟩ : TangentBundle 𝓘(ℝ, E) M)) D := by
    refine e.contMDiffOn_symm.comp contMDiffOn_id ?_ |>.congr ?_
    · intro z hz
      exact e.mem_target.mpr hz
    · intro z hz
      change z.1 ∈ e.baseSet at hz
      change (⟨z.1, v z⟩ : TangentBundle 𝓘(ℝ, E) M) =
        e.toOpenPartialHomeomorph.symm (z.1, z.2)
      rw [e.symm_apply_eq_mk_continuousLinearEquivAt_symm (R := ℝ) z.1 hz]
      simp only [v, Trivialization.symmL_apply, hz,
        Trivialization.continuousLinearEquivAt_symm_apply]
  exact contMDiffOn_metric_cutoff_of_tangent_section g δ D hD v hv


omit [FiniteDimensional ℝ E] [T2Space M] in
/-- Source: HPS (1977), proof of Theorem 5.5, p.62. Ambient joint vertical
jets of the frame cutoff. This is the exact
manifold-parameter consequence before pulling back along `A ↪ M`. -/
theorem continuousOn_fibreCutoff_frame_vertical_jets
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (δ : ℝ) (s : M) (j : ℕ) :
    let e := trivializationAt E (TangentSpace 𝓘(ℝ, E)) s
    ContinuousOn (fun z : M × E ↦
      iteratedFDeriv ℝ j
        (fun u : E ↦ fibreCutoff g δ z.1 (e.symmL ℝ z.1 u)) z.2)
      {z : M × E | z.1 ∈ e.baseSet} := by
  dsimp only
  let e := trivializationAt E (TangentSpace 𝓘(ℝ, E)) s
  let D : Set (M × E) := {z | z.1 ∈ e.baseSet}
  let Q : M × E → ℝ := fun z ↦ fibreCutoff g δ z.1 (e.symmL ℝ z.1 z.2)
  have hD : IsOpen D := e.open_baseSet.preimage continuous_fst
  have hQ : ContMDiffOn ((𝓘(ℝ, E)).prod 𝓘(ℝ, E)) 𝓘(ℝ) (⊤ : ℕ∞) Q D := by
    simpa only [Q, D] using contMDiffOn_fibreCutoff_frame g δ s
  simpa only [Q, D] using
    continuousOn_manifold_vertical_jets Q D hD (⊤ : ℕ∞) hQ j (by simp)


omit [FiniteDimensional ℝ E] [T2Space M] in
/-- Source: HPS (1977), proof of Theorem 5.5, p.62. Restriction of the ambient
frame cutoff jets to an arbitrary parameter subset.
The subtype parameter receives the induced topology; no manifold structure on A is
used. -/
theorem continuousOn_fibreCutoff_frame_vertical_jets_restrict
    (A : Set M)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (δ : ℝ) (s : M) (j : ℕ) :
    let e := trivializationAt E (TangentSpace 𝓘(ℝ, E)) s
    ContinuousOn (fun z : A × E ↦
      iteratedFDeriv ℝ j
        (fun u : E ↦ fibreCutoff g δ (z.1 : M) (e.symmL ℝ (z.1 : M) u)) z.2)
      {z : A × E | (z.1 : M) ∈ e.baseSet} := by
  dsimp only
  let e := trivializationAt E (TangentSpace 𝓘(ℝ, E)) s
  let D : Set (M × E) := {z | z.1 ∈ e.baseSet}
  let c : A × E → M × E := fun z ↦ ((z.1 : M), z.2)
  have hc : Continuous c :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hjet := continuousOn_fibreCutoff_frame_vertical_jets g δ s j
  have hpull := hjet.comp hc.continuousOn (by
    intro z hz
    exact hz)
  convert hpull using 1; rfl

end HolomorphicAnosov.ExponentialCutoff

