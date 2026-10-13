import HolomorphicAnosov.Dynamics.ExponentialCutoffExtension.Base

noncomputable section
namespace HolomorphicAnosov.ExponentialCutoff
open Bundle Set ExponentialLift
open scoped Manifold ContDiff Topology _root_.Topology

/-- Source: the linear term in HPS (1977), proof of Theorem 5.5, p.62.
A continuous family of linear operators has jointly continuous vertical jets
of every order. Smoothness is used only for evaluation on the operator space;
the parameter is merely topological. -/
theorem continuousOn_linear_family_vertical_jets
    {X E F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : X → E →L[ℝ] F) (S : Set X) (hL : ContinuousOn L S) (j : ℕ) :
    ContinuousOn (fun z : X × E ↦ iteratedFDeriv ℝ j (L z.1) z.2)
      {z | z.1 ∈ S} := by
  let Q : (E →L[ℝ] F) × E → F := fun z ↦ z.1 z.2
  have hQ : ContDiff ℝ ∞ Q := contDiff_fst.clm_apply contDiff_snd
  have hJ := continuousOn_vertical_jets Q Set.univ isOpen_univ ∞ hQ.contDiffOn j
    (by simp)
  have hcoords : ContinuousOn (fun z : X × E ↦ (L z.1, z.2)) {z | z.1 ∈ S} :=
    (hL.comp continuous_fst.continuousOn (fun _ hz ↦ hz)).prodMk
      continuous_snd.continuousOn
  exact hJ.comp hcoords (fun _ _ ↦ mem_univ _)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

omit [T2Space M] in
/-- For a C^r base map with r≥1, the actual tangent map has continuous vertical
jets of every order. In particular it has all orders required by the same r.
The argument uses only continuity of the total tangent map, not ambient C^r
regularity of its derivative. Source: HPS p.62, linear term in the cutoff. -/
theorem hasContinuousVerticalJets_mfderiv
    (A : Set M) (f : M → M) (r : ℕ∞) (hr : 1 ≤ r)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) r f) :
    HasContinuousVerticalJets A f r
      (fun p ↦ mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M)) := by
  refine ⟨?_, ?_⟩
  · intro p
    exact (modelDerivative (E := E) f p).contDiff.contDiffOn
  · intro s t j hj
    let es := trivializationAt E (TangentSpace 𝓘(ℝ, E)) s
    let et := trivializationAt E (TangentSpace 𝓘(ℝ, E)) t
    let S : Set A := {p | (p : M) ∈ (chartAt E s).source ∧
      f p ∈ (chartAt E t).source}
    let C : A → E →L[ℝ] E := fun p ↦
      (et.continuousLinearMapAt ℝ (f p)).comp
        ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M)).comp (es.symmL ℝ (p : M)))
    have hC : ContinuousOn C S := by
      apply continuousOn_clm_apply.mpr
      intro u
      have hsymm : ContinuousOn (fun p : A ↦
          (⟨(p : M), es.symm (p : M) u⟩ : TangentBundle 𝓘(ℝ, E) M)) S :=
        es.continuousOn_symm.comp
          (continuous_subtype_val.prodMk continuous_const).continuousOn
          (fun p hp ↦ ⟨hp.1, mem_univ _⟩)
      have hTf := hf.continuous_tangentMap (show 1 ≤ (r : ℕ∞ω) by exact_mod_cast hr)
      have htotal := hTf.comp_continuousOn hsymm
      have hout := et.continuousOn.comp htotal (fun p hp ↦ et.mem_source.mpr hp.2)
      have heval := continuous_snd.comp_continuousOn hout
      apply heval.congr
      intro p hp
      change et.continuousLinearMapAt ℝ (f p)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M) (es.symmL ℝ (p : M) u)) = _
      rw [es.symmL_apply (R := ℝ) hp.1,
        et.continuousLinearMapAt_apply_of_mem ℝ hp.2]
      rfl
    exact (continuousOn_linear_family_vertical_jets C S hC j).mono
      (fun z hz ↦ ⟨hz.1, hz.2.1⟩)

end HolomorphicAnosov.ExponentialCutoff
