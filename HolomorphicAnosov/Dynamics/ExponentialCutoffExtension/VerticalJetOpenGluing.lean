import HolomorphicAnosov.Dynamics.ExponentialCutoffExtension.Base

noncomputable section
namespace HolomorphicAnosov.ExponentialCutoff
open Bundle Set ExponentialLift
open scoped Manifold ContDiff Topology _root_.Topology

/-- Ordinary vertical derivatives are local in the fibre variable, so continuous
families glue across an open cover without any differentiability in the parameter.
Source: the open-cover step of HPS p.62, implemented using Mathlib locality of
`iteratedFDeriv` and `ContinuousOn.union_of_isOpen`. -/
theorem continuous_vertical_jet_glue
    {X E F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G H L : X → E → F) (U V : Set (X × E))
    (hU : IsOpen U) (hV : IsOpen V)
    (hGU : EqOn (fun z : X × E ↦ G z.1 z.2) (fun z ↦ H z.1 z.2) U)
    (hGV : EqOn (fun z : X × E ↦ G z.1 z.2) (fun z ↦ L z.1 z.2) V)
    (j : ℕ)
    (hH : ContinuousOn (fun z : X × E ↦ iteratedFDeriv ℝ j (H z.1) z.2) U)
    (hL : ContinuousOn (fun z : X × E ↦ iteratedFDeriv ℝ j (L z.1) z.2) V) :
    ContinuousOn (fun z : X × E ↦ iteratedFDeriv ℝ j (G z.1) z.2) (U ∪ V) := by
  have localJet (P : X → E → F) (W : Set (X × E)) (hW : IsOpen W)
      (hGP : EqOn (fun z : X × E ↦ G z.1 z.2) (fun z ↦ P z.1 z.2) W)
      (z : X × E) (hz : z ∈ W) :
      iteratedFDeriv ℝ j (G z.1) z.2 = iteratedFDeriv ℝ j (P z.1) z.2 := by
    have hslice : {u : E | (z.1, u) ∈ W} ∈ 𝓝 z.2 :=
      (hW.preimage (continuous_const.prodMk continuous_id)).mem_nhds hz
    have heq : G z.1 =ᶠ[𝓝 z.2] P z.1 := by
      filter_upwards [hslice] with u hu
      exact hGP hu
    exact (heq.iteratedFDeriv ℝ j).self_of_nhds
  exact (hH.congr (fun z hz ↦ (localJet H U hU hGU z hz))).union_of_isOpen
    (hL.congr (fun z hz ↦ (localJet L V hV hGV z hz))) hU hV

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- In any fixed paired tangent frame, the extension equals the actual local
cutoff product on the inner metric region. No regularity of off-domain H is used. -/
theorem extension_frame_inner_eq
    (A : Set M) (f : M → M)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (H : ∀ p : A, TangentSpace 𝓘(ℝ, E) (p : M) → TangentSpace 𝓘(ℝ, E) (f p))
    (s t : M) (p : A) (u : E) (R δ : ℝ)
    (hu : metricNorm g p
      ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) s).symmL ℝ (p : M) u) < R) :
    fibreExpression A f (extension A f g H R δ) s t p u =
      fibreExpression A f (fun p ↦ mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M)) s t p u +
      fibreCutoff g δ p
        ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) s).symmL ℝ (p : M) u) •
        (fibreExpression A f H s t p u -
          fibreExpression A f (fun p ↦ mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M)) s t p u) := by
  simp only [fibreExpression, extension, ite_eq_left hu, map_add, map_sub, map_smul]

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- On the outer metric region the paired frame expression is exactly linear. -/
theorem extension_frame_outer_eq
    (A : Set M) (f : M → M)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (H : ∀ p : A, TangentSpace 𝓘(ℝ, E) (p : M) → TangentSpace 𝓘(ℝ, E) (f p))
    (s t : M) (p : A) (u : E) (R δ : ℝ) (hδ : 0 < δ)
    (hu : δ < metricNorm g p
      ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) s).symmL ℝ (p : M) u)) :
    fibreExpression A f (extension A f g H R δ) s t p u =
      fibreExpression A f (fun p ↦ mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M)) s t p u := by
  unfold fibreExpression
  rw [extension_eq_derivative A f g H hδ p _ hu.le]


omit [FiniteDimensional ℝ E] [T2Space M] in
/-- Conditional assembly component for the parent's exact jet target. The two
explicit jet hypotheses are the remaining local product and linear coefficient
calculations; this lemma adds no assumption to the parent theorem.
Source: HPS p.62 open-overlap gluing. The fibrewise regularity comes from the
existing fixed-fibre theorem; joint jets glue by their ordinary locality. -/
theorem extension_vertical_jets_of_product_and_linear
    (A : Set M) (f : M → M) (hf : Continuous f)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (H : ∀ p : A, TangentSpace 𝓘(ℝ, E) (p : M) → TangentSpace 𝓘(ℝ, E) (f p))
    (r : ℕ∞) {R δ : ℝ} (hδ : 0 < δ) (hδR : δ < R)
    (hH : HasContinuousVerticalJetsOn A f r H
      (fun p ↦ {v | metricNorm g p v < R}))
    (hproduct : HasContinuousVerticalJetsOn A f r
      (fun p v ↦ mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M) v +
        fibreCutoff g δ p v • (H p v - mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M) v))
      (fun p ↦ {v | metricNorm g p v < R}))
    (hlinear : HasContinuousVerticalJets A f r
      (fun p ↦ mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M))) :
    HasContinuousVerticalJets A f r (extension A f g H R δ) := by
  refine ⟨?_, ?_⟩
  · intro p
    exact (contDiff_extension_fibre A f g H hδ hδR p r (hH.1 p)).contDiffOn
  · intro s t j hj
    let es := trivializationAt E (TangentSpace 𝓘(ℝ, E)) s
    let W : Set (A × E) := {z | (z.1 : M) ∈ (chartAt E s).source ∧
      f z.1 ∈ (chartAt E t).source}
    let n : A × E → ℝ := fun z ↦ metricNorm g z.1 (es.symmL ℝ (z.1 : M) z.2)
    let U : Set (A × E) := W ∩ n ⁻¹' Set.Iio R
    let V : Set (A × E) := W ∩ n ⁻¹' Set.Ioi δ
    let P := fun (p : A) v ↦ mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M) v +
      fibreCutoff g δ p v • (H p v - mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M) v)
    let L := fun (p : A) v ↦ mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M) v
    have hW : IsOpen W :=
      ((chartAt E s).open_source.preimage
        (continuous_subtype_val.comp continuous_fst)).inter
      ((chartAt E t).open_source.preimage
        (hf.comp (continuous_subtype_val.comp continuous_fst)))
    have hn : ContinuousOn n W := by
      have hc : Continuous (fun z : A × E ↦ ((z.1 : M), z.2)) :=
        (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
      have hsymm : ContinuousOn (fun z : A × E ↦
          (⟨(z.1 : M), es.symm (z.1 : M) z.2⟩ : TangentBundle 𝓘(ℝ, E) M)) W :=
        es.continuousOn_symm.comp hc.continuousOn
          (fun z hz ↦ ⟨hz.1, mem_univ _⟩)
      have h := (ExponentialLift.continuous_metricNorm g).comp_continuousOn hsymm
      apply h.congr
      intro z hz
      change metricNorm g z.1 (es.symmL ℝ (z.1 : M) z.2) = _
      rw [es.symmL_apply (R := ℝ) hz.1]
      rfl
    have hU : IsOpen U := hn.isOpen_inter_preimage hW isOpen_Iio
    have hV : IsOpen V := hn.isOpen_inter_preimage hW isOpen_Ioi
    have hcov : W = U ∪ V := by
      ext z
      constructor
      · intro hz
        by_cases hnR : n z < R
        · exact Or.inl ⟨hz, hnR⟩
        · exact Or.inr ⟨hz, lt_of_lt_of_le hδR (le_of_not_gt hnR)⟩
      · rintro (hz | hz) <;> exact hz.1
    have hGU : EqOn (fun z : A × E ↦
        fibreExpression A f (extension A f g H R δ) s t z.1 z.2)
        (fun z ↦ fibreExpression A f P s t z.1 z.2) U := by
      intro z hz
      have hzn : metricNorm g z.1 (es.symmL ℝ (z.1 : M) z.2) < R := hz.2
      simp only [fibreExpression, extension, ite_eq_left hzn, P, es]
    have hGV : EqOn (fun z : A × E ↦
        fibreExpression A f (extension A f g H R δ) s t z.1 z.2)
        (fun z ↦ fibreExpression A f L s t z.1 z.2) V := by
      intro z hz
      exact extension_frame_outer_eq A f g H s t z.1 z.2 R δ hδ hz.2
    have hPJ : ContinuousOn (fun z : A × E ↦
        iteratedFDeriv ℝ j (fibreExpression A f P s t z.1) z.2) U := by
      apply (hproduct.2 s t j hj).mono
      intro z hz
      exact ⟨hz.1.1, hz.1.2, hz.2⟩
    have hLJ : ContinuousOn (fun z : A × E ↦
        iteratedFDeriv ℝ j (fibreExpression A f L s t z.1) z.2) V := by
      apply (hlinear.2 s t j hj).mono
      intro z hz
      exact ⟨hz.1.1, hz.1.2, mem_univ _⟩
    have hglue := continuous_vertical_jet_glue
      (fibreExpression A f (extension A f g H R δ) s t)
      (fibreExpression A f P s t) (fibreExpression A f L s t)
      U V hU hV hGU hGV j hPJ hLJ
    rw [← hcov] at hglue
    apply hglue.mono
    intro z hz
    exact ⟨hz.1, hz.2.1⟩

end HolomorphicAnosov.ExponentialCutoff

