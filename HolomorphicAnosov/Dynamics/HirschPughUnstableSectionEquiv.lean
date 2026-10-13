import HolomorphicAnosov.Dynamics.HirschPughSectionTransport
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Original unstable derivative section isomorphism

Shub, *Global Stability of Dynamical Systems* (1987), pp.72–74. Compactness bounds the
actual forward derivative, and the original derivative transport is inverse to the already
constructed inverse transport. This supplies the unstable linear isomorphism required by
the local strong graph theorem, without a hypothesis asserting its existence.
DAG node: `dynamics.hirsch_pugh_unstable_section_equiv_g9`.
-/

noncomputable section
open Set Bundle
open scoped ContDiff Manifold Topology _root_.Topology
namespace HolomorphicAnosov.HirschRestrictedCoordinates

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- A smooth map's derivative is uniformly bounded over a compact base set in a fixed
smooth Riemannian norm. Source: Shub p.72, boundedness of the original derivative-section
operator; compact metric-tube argument of HPS pp.61–62 and homogeneity. -/
theorem exists_uniform_mfderiv_bound {Λ : Set M} (hΛ : IsCompact Λ)
    (g : M → M) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ g)
    (h : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : Λ) (v : TangentSpace 𝓘(ℝ, E) (x : M)),
      hyperbolicRiemannianNorm h (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) g x v) ≤
        C * hyperbolicRiemannianNorm h v := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨h.toRiemannianMetric⟩
  have hn (x : M) (v : TangentSpace 𝓘(ℝ, E) x) :
      hyperbolicRiemannianNorm h v = ‖v‖ := by rfl
  let F : TangentBundle 𝓘(ℝ, E) M → ℝ := fun z ↦
    hyperbolicRiemannianNorm h (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) g z.proj z.snd)
  have hF : Continuous F :=
    (ExponentialLift.continuous_metricNorm h).comp (hg.continuous_tangentMap (by simp))
  let Ω := F ⁻¹' Iio 1
  have hΩ : IsOpen Ω := isOpen_Iio.preimage hF
  have hzero : ∀ p ∈ Λ, (⟨p, 0⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ Ω := by
    intro p _
    change F ⟨p, 0⟩ < 1
    simp [F, hn]
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
  have hsmall : ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) g x (c • v)‖ < 1 := hcv
  rw [map_smul, norm_smul, Real.norm_of_nonneg hcpos.le] at hsmall
  have hbound : ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) g x v‖ < 1 / c :=
    (lt_div_iff₀ hcpos).mpr (by simpa only [mul_comm] using hsmall)
  have he : 1 / c = (2 / ε) * ‖v‖ := by dsimp [c]; field_simp
  rw [he] at hbound
  exact hbound.le

/-- The original forward derivative transport on the unstable bounded-section space is a
continuous linear equivalence, with inverse bounded by the adapted inverse contraction.
Source: Shub pp.72–74. Compactness bounds the forward derivative; the two inverse identities
are the original chain rules, with the base reindexings cancelled. -/
theorem exists_unstable_section_equiv
    (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (Λ : Set M)
    (H : HyperbolicSetFactOneDatum f Λ)
    (h : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (a : ℝ) (ha : 0 ≤ a)
    (hu : ∀ (x : Λ) (v : TangentSpace 𝓘(ℝ, E) (x : M)), v ∈ H.unstable.fibre x →
      hyperbolicRiemannianNorm h (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f.symm x v) ≤
        a * hyperbolicRiemannianNorm h v) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨h.toRiemannianMetric⟩
    ∃ L : boundedSectionSubmodule H.unstable.fibre ≃L[ℝ]
        boundedSectionSubmodule H.unstable.fibre,
      (∀ s x, (L s).val x = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (f.symm x)
        (s.val ⟨f.symm x, H.backward_mem x.property⟩)) ∧
      ‖L.symm.toContinuousLinearMap‖ ≤ a := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨h.toRiemannianMetric⟩
  let B : Type _ := boundedSectionSubmodule H.unstable.fibre
  obtain ⟨C, hC, hbound⟩ := exists_uniform_mfderiv_bound H.compact f f.contMDiff h
  let b : Λ → Λ := fun x ↦ ⟨f.symm x, H.backward_mem x.property⟩
  let T (x : Λ) : TangentSpace 𝓘(ℝ, E) (b x : M) →ₗ[ℝ] TangentSpace 𝓘(ℝ, E) (x : M) :=
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (f.symm x)).toLinearMap
  have hm (x : Λ) (v : TangentSpace 𝓘(ℝ, E) (b x : M))
      (hv : v ∈ H.unstable.fibre (b x)) : T x v ∈ H.unstable.fibre x := by
    have hh : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (b x) v) ∈
        H.unstable.fibre ⟨f (b x), H.forward_mem (b x).property⟩ := by
      rw [← H.unstable_invariant (b x)]
      exact ⟨v, hv, rfl⟩
    have he : (⟨f (b x), H.forward_mem (b x).property⟩ : Λ) = x :=
      Subtype.ext (f.apply_symm_apply x)
    change T x v ∈ H.unstable.fibre ⟨f (b x), H.forward_mem (b x).property⟩ at hh
    rwa [he] at hh
  have hb (x : Λ) (v : TangentSpace 𝓘(ℝ, E) (b x : M))
      (_hv : v ∈ H.unstable.fibre (b x)) : ‖T x v‖ ≤ C * ‖v‖ := by
    have hh := hbound (b x) v
    change Real.sqrt (h.inner (f (b x)) (T x v) (T x v)) ≤ C * ‖v‖ at hh
    have he : f (b x) = (x : M) := f.apply_symm_apply x
    rw [he] at hh
    exact hh
  obtain ⟨Q, hQ, _⟩ := exists_bounded_section_transport H.unstable.fibre b T C hC.le hm hb
  obtain ⟨R, hR, hnR⟩ := exists_unstable_inverse_section_transport f Λ H h a ha hu
  have hRQ : Function.LeftInverse R Q := by
    intro s
    apply Subtype.ext
    ext x
    change (R (Q s)).val x = s.val x
    rw [hR, hQ]
    dsimp only [T, b]
    have he : (⟨f.symm (f x), H.backward_mem (H.forward_mem x.property)⟩ : Λ) = x :=
      Subtype.ext (f.symm_apply_apply x)
    rw [he]
    have hchain := mfderiv_comp (x : M)
      (f.symm.contMDiff.mdifferentiableAt (by simp))
      (f.contMDiff.mdifferentiableAt (by simp))
    have hid : (f.symm : M → M) ∘ f = id := by
      funext y
      exact f.symm_apply_apply y
    rw [hid, mfderiv_id] at hchain
    change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f.symm (f x)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (f.symm (f x)) (s.val x)) = s.val x
    rw [show f.symm (f x) = (x : M) from f.symm_apply_apply x]
    exact (congrArg (fun L ↦ L (s.val x)) hchain).symm
  have hQR : Function.RightInverse R Q := by
    intro s
    apply Subtype.ext
    ext x
    change (Q (R s)).val x = s.val x
    rw [hQ, hR]
    dsimp only [T, b]
    have he : (⟨f (f.symm x), H.forward_mem (H.backward_mem x.property)⟩ : Λ) = x :=
      Subtype.ext (f.apply_symm_apply x)
    rw [he]
    have hchain := mfderiv_comp (x : M)
      (f.contMDiff.mdifferentiableAt (by simp))
      (f.symm.contMDiff.mdifferentiableAt (by simp))
    have hid : (f : M → M) ∘ f.symm = id := by
      funext y
      exact f.apply_symm_apply y
    rw [hid, mfderiv_id] at hchain
    change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (f.symm x)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f.symm (f (f.symm x)) (s.val x)) = s.val x
    rw [show f (f.symm x) = (x : M) from f.apply_symm_apply x]
    exact (congrArg (fun L ↦ L (s.val x)) hchain).symm
  exact ⟨ContinuousLinearEquiv.equivOfInverse Q R hRQ hQR, hQ, hnR⟩

end HolomorphicAnosov.HirschRestrictedCoordinates
