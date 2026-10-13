import HolomorphicAnosov.Dynamics.HirschPughRestrictedSplitting

/-!
# Original derivative operators on bounded hyperbolic sections

Shub, *Global Stability of Dynamical Systems* (1987), pp.72–74. The stable derivative
transport and inverse unstable derivative transport are assembled on the actual bounded
section subspaces over Λ. Their operator norms inherit the supplied adapted fibre bounds.
DAG node: `dynamics.hirsch_pugh_section_transport_g9`.
-/

noncomputable section
open scoped ContDiff Manifold Topology _root_.Topology Bundle
namespace HolomorphicAnosov.HirschRestrictedCoordinates

/-- A uniformly bounded fibre transport, with arbitrary base reindexing, induces a bounded
linear endomorphism of the original subspace of bounded sections. Source: Shub pp.72–74,
`f#` on the stable and unstable section factors; the proof is the dependent supremum estimate. -/
theorem exists_bounded_section_transport
    {A : Type*} {V : A → Type*}
    [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
    (S : ∀ x, Submodule ℝ (V x)) (b : A → A)
    (T : ∀ x, V (b x) →ₗ[ℝ] V x) (a : ℝ) (ha : 0 ≤ a)
    (hmem : ∀ x v, v ∈ S (b x) → T x v ∈ S x)
    (hbound : ∀ x v, v ∈ S (b x) → ‖T x v‖ ≤ a * ‖v‖) :
    ∃ L : boundedSectionSubmodule S →L[ℝ] boundedSectionSubmodule S,
      (∀ s x, (L s).val x = T x (s.val (b x))) ∧ ‖L‖ ≤ a := by
  let B : Type _ := boundedSectionSubmodule S
  let Lfun : B → B := fun s ↦
    ⟨⟨fun x ↦ T x (s.val (b x)), memℓp_infty ⟨a * ‖s‖, by
      rintro _ ⟨x, rfl⟩
      exact (hbound x _ (s.property (b x))).trans
        (mul_le_mul_of_nonneg_left
          (lp.norm_apply_le_norm ENNReal.top_ne_zero s.val (b x)) ha)⟩⟩,
      fun x ↦ hmem x _ (s.property (b x))⟩
  let L : B →ₗ[ℝ] B :=
    { toFun := Lfun
      map_add' := by
        intro s t
        apply Subtype.ext
        ext x
        exact (T x).map_add _ _
      map_smul' := by
        intro c s
        apply Subtype.ext
        ext x
        exact (T x).map_smul c _ }
  have hL (s : B) : ‖L s‖ ≤ a * ‖s‖ :=
    lp.norm_le_of_forall_le (mul_nonneg ha (norm_nonneg s)) (fun x ↦
      (hbound x _ (s.property (b x))).trans
        (mul_le_mul_of_nonneg_left
          (lp.norm_apply_le_norm ENNReal.top_ne_zero s.val (b x)) ha))
  refine ⟨L.mkContinuous a hL, fun _ _ ↦ rfl, ?_⟩
  exact LinearMap.mkContinuous_norm_le _ ha _

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The original derivative transport on bounded stable sections has operator norm at most
the adapted one-step bound. Source: Shub pp.72–74, the stable block of the original f#.
Only reindexing by f⁻¹ and the original stable derivative estimate enter the supremum bound. -/
theorem exists_stable_derivative_section_transport
    (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (Λ : Set M)
    (H : HyperbolicSetFactOneDatum f Λ)
    (h : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _)) (a : ℝ) (ha : 0 ≤ a)
    (hs : ∀ (x : Λ) (v : TangentSpace 𝓘(ℝ, E) (x : M)), v ∈ H.stable.fibre x →
      hyperbolicRiemannianNorm h (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x v) ≤
        a * hyperbolicRiemannianNorm h v) :
    letI : Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
      ⟨h.toRiemannianMetric⟩
    ∃ L : boundedSectionSubmodule H.stable.fibre →L[ℝ]
        boundedSectionSubmodule H.stable.fibre,
      (∀ s x, (L s).val x = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (f.symm x)
        (s.val ⟨f.symm x, H.backward_mem x.property⟩)) ∧ ‖L‖ ≤ a := by
  let : Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨h.toRiemannianMetric⟩
  let b : Λ → Λ := fun x ↦ ⟨f.symm x, H.backward_mem x.property⟩
  let T (x : Λ) : TangentSpace 𝓘(ℝ, E) (b x : M) →ₗ[ℝ] TangentSpace 𝓘(ℝ, E) (x : M) :=
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (f.symm x)).toLinearMap
  have hm (x : Λ) (v : TangentSpace 𝓘(ℝ, E) (b x : M))
      (hv : v ∈ H.stable.fibre (b x)) : T x v ∈ H.stable.fibre x := by
    have hh : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (b x) v) ∈
        H.stable.fibre ⟨f (b x), H.forward_mem (b x).property⟩ := by
      rw [← H.stable_invariant (b x)]
      exact ⟨v, hv, rfl⟩
    have he : (⟨f (b x), H.forward_mem (b x).property⟩ : Λ) = x :=
      Subtype.ext (f.apply_symm_apply x)
    change T x v ∈ H.stable.fibre ⟨f (b x), H.forward_mem (b x).property⟩ at hh
    rwa [he] at hh
  have hb (x : Λ) (v : TangentSpace 𝓘(ℝ, E) (b x : M))
      (hv : v ∈ H.stable.fibre (b x)) : ‖T x v‖ ≤ a * ‖v‖ := by
    have hh := hs (b x) v hv
    change Real.sqrt (h.inner (f (b x)) (T x v) (T x v)) ≤ a * ‖v‖ at hh
    have he : f (b x) = (x : M) := f.apply_symm_apply x
    rw [he] at hh
    exact hh
  exact exists_bounded_section_transport H.stable.fibre b T a ha hm hb

/-- The original inverse derivative transport on bounded unstable sections has norm at
most the adapted inverse bound. Source: Shub pp.72–74. Forward invariance and the original
chain rule imply backward preservation of the unstable fibres; the supremum estimate then
uses only the supplied inverse derivative contraction. -/
theorem exists_unstable_inverse_section_transport
    (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (Λ : Set M)
    (H : HyperbolicSetFactOneDatum f Λ)
    (h : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _)) (a : ℝ) (ha : 0 ≤ a)
    (hu : ∀ (x : Λ) (v : TangentSpace 𝓘(ℝ, E) (x : M)), v ∈ H.unstable.fibre x →
      hyperbolicRiemannianNorm h (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f.symm x v) ≤
        a * hyperbolicRiemannianNorm h v) :
    letI : Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
      ⟨h.toRiemannianMetric⟩
    ∃ L : boundedSectionSubmodule H.unstable.fibre →L[ℝ]
        boundedSectionSubmodule H.unstable.fibre,
      (∀ s x, (L s).val x = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f.symm (f x)
        (s.val ⟨f x, H.forward_mem x.property⟩)) ∧ ‖L‖ ≤ a := by
  let : Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨h.toRiemannianMetric⟩
  let b : Λ → Λ := fun x ↦ ⟨f x, H.forward_mem x.property⟩
  let T (x : Λ) : TangentSpace 𝓘(ℝ, E) (b x : M) →ₗ[ℝ] TangentSpace 𝓘(ℝ, E) (x : M) :=
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f.symm (f x)).toLinearMap
  have hm (x : Λ) (v : TangentSpace 𝓘(ℝ, E) (b x : M))
      (hv : v ∈ H.unstable.fibre (b x)) : T x v ∈ H.unstable.fibre x := by
    have hpre : v ∈ (H.unstable.fibre x).map
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x).toLinearMap := by
      rw [H.unstable_invariant]
      exact hv
    obtain ⟨w, hw, hwv⟩ := hpre
    rw [← hwv]
    have hchain := mfderiv_comp (x : M)
      (f.symm.contMDiff.mdifferentiableAt (by simp))
      (f.contMDiff.mdifferentiableAt (by simp))
    have hid : (f.symm : M → M) ∘ f = id := by
      funext y
      exact f.symm_apply_apply y
    rw [hid, mfderiv_id] at hchain
    have he : T x ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x) w) = w :=
      (congrArg (fun L ↦ L w) hchain).symm
    change T x ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x) w) ∈ H.unstable.fibre x
    rw [he]
    exact hw
  have hb (x : Λ) (v : TangentSpace 𝓘(ℝ, E) (b x : M))
      (hv : v ∈ H.unstable.fibre (b x)) : ‖T x v‖ ≤ a * ‖v‖ := by
    have hh := hu (b x) v hv
    change Real.sqrt (h.inner (f.symm (b x)) (T x v) (T x v)) ≤ a * ‖v‖ at hh
    have he : f.symm (b x) = (x : M) := f.symm_apply_apply x
    rw [he] at hh
    exact hh
  exact exists_bounded_section_transport H.unstable.fibre b T a ha hm hb

end HolomorphicAnosov.HirschRestrictedCoordinates
