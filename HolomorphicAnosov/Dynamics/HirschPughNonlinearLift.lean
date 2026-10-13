import HolomorphicAnosov.Dynamics.HirschPughRestrictedSplitting
import HolomorphicAnosov.Dynamics.ExponentialCutoffExtension

namespace HolomorphicAnosov
open Set
open scoped ContDiff Manifold Topology _root_.Topology Bundle
noncomputable section
universe u v
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type v} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The max splitting norm and its cutoff extension certificate over the original Λ.
Source: HPS pp.61--62, with the restricted projectors from the preceding splitting node. -/
theorem exists_hirsch_nonlinear_lift
    [FiniteDimensional ℝ E] [T2Space M]
    (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (Λ : Set M)
    (H : HyperbolicSetFactOneDatum f Λ)
    (h : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ν : ExponentialCutoff.ContinuousRestrictedTangentNorm (E := E) Λ,
      (∀ p v, ν.value p v = max
        (hyperbolicRiemannianNorm h
          ((H.stable.fibre p).projection (H.unstable.fibre p) (H.complementary p) v))
        (hyperbolicRiemannianNorm h
          ((H.unstable.fibre p).projection (H.stable.fibre p) (H.complementary p).symm v))) ∧
      ∃ (ρ R δ b : ℝ) (L : (q : M) → M → TangentSpace 𝓘(ℝ, E) q),
        0 < ρ ∧ 0 < R ∧ R ≤ ρ ∧ 0 < δ ∧ δ < R ∧ 0 < b ∧
        (∀ q ∈ Λ, ∀ v : TangentSpace 𝓘(ℝ, E) q, ExponentialLift.metricNorm h q v < ρ →
          (⟨q, v⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ ExponentialLift.riemannianExpDomain h ∧
          L q (ExponentialLift.riemannianExp h q v) = v) ∧
        let G := ExponentialCutoff.extension Λ (f : M → M) h
          (fun p ↦ ExponentialLift.centeredLift h (f : M → M) L p) R δ
        ExponentialCutoff.IsGlobalExtension Λ f H.forward_mem ⊤ ν ε G ∧
        ∀ (p : Λ) v, ν.value p v ≤ b →
          (⟨(p : M), v⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ ExponentialLift.riemannianExpDomain h ∧
          ExponentialLift.metricNorm h (f p) (G p v) < ρ ∧
          (⟨f p, G p v⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ ExponentialLift.riemannianExpDomain h ∧
          G p v = L (f p) (f (ExponentialLift.riemannianExp h p v)) ∧
          ExponentialLift.riemannianExp h (f p) (G p v) =
            f (ExponentialLift.riemannianExp h p v) := by
  let : Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨h.toContinuousRiemannianMetric.toRiemannianMetric⟩
  have hn (p : M) (v : TangentSpace 𝓘(ℝ, E) p) :
      hyperbolicRiemannianNorm h v = ‖v‖ := by rfl
  let P (x : Λ) := (H.stable.fibre x).projection (H.unstable.fibre x) (H.complementary x)
  let Q (x : Λ) := (H.unstable.fibre x).projection (H.stable.fibre x) (H.complementary x).symm
  let ν : ExponentialCutoff.ContinuousRestrictedTangentNorm (E := E) Λ :=
    { value := fun p v ↦ max (hyperbolicRiemannianNorm h (P p v))
        (hyperbolicRiemannianNorm h (Q p v))
      nonneg := by intro p v; exact le_max_of_le_left (Real.sqrt_nonneg _)
      eq_zero_iff := by
        intro p v
        constructor
        · intro hz
          have hp_le : hyperbolicRiemannianNorm h (P p v) ≤ 0 :=
            (le_max_left _ _).trans (le_of_eq hz)
          have hq_le : hyperbolicRiemannianNorm h (Q p v) ≤ 0 :=
            (le_max_right _ _).trans (le_of_eq hz)
          have hp : hyperbolicRiemannianNorm h (P p v) = 0 :=
            le_antisymm hp_le (Real.sqrt_nonneg _)
          have hq : hyperbolicRiemannianNorm h (Q p v) = 0 :=
            le_antisymm hq_le (Real.sqrt_nonneg _)
          have hp' : P p v = 0 := norm_eq_zero.mp (by simpa only [hn] using hp)
          have hq' : Q p v = 0 := norm_eq_zero.mp (by simpa only [hn] using hq)
          have hv : P p v + Q p v = v :=
            Submodule.projection_add_projection_eq_self (H.complementary p) v
          rw [hp', hq', zero_add] at hv
          exact hv.symm
        · intro hv
          subst v
          simp [P, Q, hn]
      add_le := by
        intro p v w
        rw [hn, hn, hn, hn, hn, hn]
        apply max_le
        · rw [(P p).map_add]
          exact (norm_add_le _ _).trans
            (add_le_add (le_max_left _ _) (le_max_left _ _))
        · rw [(Q p).map_add]
          exact (norm_add_le _ _).trans
            (add_le_add (le_max_right _ _) (le_max_right _ _))
      smul := by
        intro p a v
        rw [hn, hn, hn, hn, (P p).map_smul, (Q p).map_smul, norm_smul, norm_smul]
        exact (mul_max_of_nonneg _ _ (abs_nonneg a)).symm
      continuous := by
        let Z := {z : TangentBundle 𝓘(ℝ, E) M // z.proj ∈ Λ}
        have hP : Continuous (fun z : Z ↦ hyperbolicRiemannianNorm h
            (P ⟨z.val.proj, z.property⟩ z.val.snd)) := by
          exact (ExponentialLift.continuous_metricNorm h).comp
            (HirschRestrictedCoordinates.continuous_restricted_projection
              H.stable H.unstable H.complementary)
        have hQ : Continuous (fun z : Z ↦ hyperbolicRiemannianNorm h
            (Q ⟨z.val.proj, z.property⟩ z.val.snd)) := by
          exact (ExponentialLift.continuous_metricNorm h).comp
            (HirschRestrictedCoordinates.continuous_restricted_projection
              H.unstable H.stable fun x ↦ (H.complementary x).symm)
        exact hP.max hQ }
  let F : Λ → Λ := fun p ↦ ⟨f p, H.forward_mem p.property⟩
  let Ginv : Λ → Λ := fun p ↦ ⟨f.symm p, H.backward_mem p.property⟩
  have hFG : Function.LeftInverse Ginv F := by
    intro p
    apply Subtype.ext
    simp [F, Ginv]
  have hGF : Function.LeftInverse F Ginv := by
    intro p
    apply Subtype.ext
    simp [F, Ginv]
  have hFcont : Continuous F := by
    exact (f.continuous.comp continuous_subtype_val).subtype_mk
      (fun (p : Λ) ↦ H.forward_mem p.property)
  have hGcont : Continuous Ginv := by
    exact (f.symm.continuous.comp continuous_subtype_val).subtype_mk
      (fun (p : Λ) ↦ H.backward_mem p.property)
  have hFopen : IsOpenMap F := by
    intro s hs
    have heq : F '' s = Ginv ⁻¹' s := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        change Ginv (F x) ∈ s
        rw [hFG x]
        exact hx
      · intro hy
        refine ⟨Ginv y, hy, ?_⟩
        exact hGF y
    rw [heq]
    exact hs.preimage hGcont
  have hh : IsHomeomorph F := by
    exact IsHomeomorph.mk hFcont hFopen ⟨hFG.injective, hGF.surjective⟩
  exact ⟨ν, (by intros; rfl),
    ExponentialCutoff.exponential_cutoff_extension h Λ H.compact (f : M → M) ⊤
      (by simp) f.contMDiff H.forward_mem hh ν ε hε⟩
end
end HolomorphicAnosov

