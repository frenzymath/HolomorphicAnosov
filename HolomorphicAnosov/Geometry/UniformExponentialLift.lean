import HolomorphicAnosov.Geometry.UniformExponentialLift.base
import HolomorphicAnosov.Geometry.UniformExponentialLift.local_metric_tube
import HolomorphicAnosov.Geometry.UniformExponentialLift.compact_metric_tube
import HolomorphicAnosov.Geometry.UniformExponentialLift.continuous_metricNorm
import HolomorphicAnosov.Geometry.UniformExponentialLift.isOpen_normalTube
import HolomorphicAnosov.Geometry.UniformExponentialLift.uniform_inverse_tube
import HolomorphicAnosov.Geometry.UniformExponentialLift.glue_inverse_tube
import HolomorphicAnosov.Geometry.UniformExponentialLift.inverse_tube_laws
import HolomorphicAnosov.Geometry.UniformExponentialLift.contMDiffOn_inverse_totalSpace
import HolomorphicAnosov.Geometry.UniformExponentialLift.contMDiffOn_centered_totalSpace
import HolomorphicAnosov.Geometry.UniformExponentialLift.contMDiffOn_centered_frame
import HolomorphicAnosov.Geometry.UniformExponentialLift.isOpen_centered_frame_domain
import HolomorphicAnosov.Geometry.UniformExponentialLift.centered_radius
import HolomorphicAnosov.Geometry.UniformExponentialLift.vertical_jet_restriction
import HolomorphicAnosov.Geometry.UniformExponentialLift.continuousOn_vertical_jets
import HolomorphicAnosov.Geometry.UniformExponentialLift.continuousOn_manifold_vertical_jets
import HolomorphicAnosov.Geometry.UniformExponentialLift.tangent_frame_self
import HolomorphicAnosov.Geometry.UniformExponentialLift.centered_vertical_jets
import HolomorphicAnosov.Geometry.UniformExponentialLift.fixed_fibre_contMDiff
import HolomorphicAnosov.Geometry.UniformExponentialLift.inverse_fibre_contMDiffOn
import HolomorphicAnosov.Geometry.UniformExponentialLift.inverse_diagonal_derivative
import HolomorphicAnosov.Geometry.UniformExponentialLift.centered_derivative_zero

noncomputable section

namespace HolomorphicAnosov
namespace ExponentialLift

open Bundle Set TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

/-- A `C^r` map preserving a compact set admits uniform exponential charts and a centered lift with
continuous vertical jets through order `r`. The lift fixes zero and its derivative there is the
derivative of the map. (HPS, Thm. 5.5, pp. 61–62; Andrews, Props. 8.11.2, 8.11.4, 8.11.5 and
10.3.1) -/
theorem uniform_exponential_lift_on_compact_set
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (A : Set M) (hA : IsCompact A) (f : M → M) (r : ℕ∞)
    (hr : 1 ≤ r) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) r f)
    (hfA : MapsTo f A A) (emptyRadius : ℝ) :
    ∃ (U : Opens M) (ρ R : ℝ)
      (O : Opens (TangentBundle 𝓘(ℝ, E) M)) (B : Opens (M × M))
      (L : (q : M) → M → TangentSpace 𝓘(ℝ, E) q)
      (Φ : Diffeomorph (𝓘(ℝ, E)).tangent ((𝓘(ℝ, E)).prod 𝓘(ℝ, E)) O B ∞),
      A ⊆ U ∧ 0 < ρ ∧ 0 < R ∧ R ≤ ρ ∧
      (O : Set (TangentBundle 𝓘(ℝ, E) M)) = normalTube g U ρ ∧
      (O : Set (TangentBundle 𝓘(ℝ, E) M)) ⊆ riemannianExpDomain g ∧
      (∀ z : O, (Φ z : M × M) = (z.val.proj, riemannianExp g z.val.proj z.val.snd)) ∧
      (∀ y : B, ((Φ.symm y : O) : TangentBundle 𝓘(ℝ, E) M) =
        ⟨y.val.1, L y.val.1 y.val.2⟩) ∧
      (B : Set (M × M)) =
        (fun z : TangentBundle 𝓘(ℝ, E) M ↦
          (z.proj, riemannianExp g z.proj z.snd)) '' (O : Set _) ∧
      (∀ (q w : M), (q, w) ∈ B → riemannianExp g q (L q w) = w) ∧
      (∀ (q : M) (v : TangentSpace 𝓘(ℝ, E) q),
        (⟨q, v⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ O → L q (riemannianExp g q v) = v) ∧
      (∀ q ∈ U, riemannianExp g q 0 = q ∧ (q, q) ∈ B ∧ L q q = 0 ∧
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
          (fun w ↦ tangentSpaceCastModel 𝓘(ℝ, E) q (L q w)) q =
          (NormedSpace.fromTangentSpace
            (tangentSpaceCastModel 𝓘(ℝ, E) q (L q q))).symm.toContinuousLinearMap ∘L
            (tangentSpaceCastModel 𝓘(ℝ, E) q).toContinuousLinearMap) ∧
      (∀ p ∈ A, ∀ v : TangentSpace 𝓘(ℝ, E) p, metricNorm g p v < R →
        (⟨p, v⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ riemannianExpDomain g ∧
          (f p, f (riemannianExp g p v)) ∈ B) ∧
      (∀ p ∈ A, centeredLift g f L p 0 = 0 ∧
        HasFDerivAt
          (fun u : E ↦ tangentSpaceCastModel 𝓘(ℝ, E) (f p)
            (centeredLift g f L p ((tangentSpaceCastModel 𝓘(ℝ, E) p).symm u)))
          ((tangentSpaceCastModel 𝓘(ℝ, E) (f p)).toContinuousLinearMap ∘L
            mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f p ∘L
            (tangentSpaceCastModel 𝓘(ℝ, E) p).symm.toContinuousLinearMap) 0) ∧
      HasContinuousVerticalJetsOn A f r
        (fun p ↦ centeredLift g f L p)
        (fun p ↦ {v | metricNorm g p v < R}) ∧
      (A = ∅ → U = ⊥ ∧ O = ⊥ ∧ B = ⊥ ∧ (0 < emptyRadius → R = emptyRadius)) := by
  classical
  by_cases hEmpty : A = ∅
  · subst A
    let R : ℝ := if 0 < emptyRadius then emptyRadius else 1
    have hR : 0 < R := by
      by_cases h : 0 < emptyRadius
      · simpa only [R, ite_eq_left h] using h
      · simp [R, h]
    let O : Opens (TangentBundle 𝓘(ℝ, E) M) := ⊥
    let B : Opens (M × M) := ⊥
    have : IsEmpty O := ⟨fun x ↦ x.property⟩
    have : IsEmpty B := ⟨fun x ↦ x.property⟩
    let Φ : Diffeomorph (𝓘(ℝ, E)).tangent ((𝓘(ℝ, E)).prod 𝓘(ℝ, E)) O B ∞ :=
      { toEquiv := Equiv.equivOfIsEmpty O B
        contMDiff_toFun := fun x ↦ (IsEmpty.false x).elim
        contMDiff_invFun := fun x ↦ (IsEmpty.false x).elim }
    refine ⟨⊥, R, R, O, B, fun _ _ ↦ 0, Φ, ?_⟩
    simp [O, B, normalTube, hR, HasContinuousVerticalJetsOn]
    constructor
    · intro s t j hj z hz
      exact (z.1.property).elim
    · intro h
      simp only [R, ite_eq_left h]
  · obtain ⟨U, ρ, hAU, hρ, hOD, hinj, hloc⟩ := uniform_inverse_tube g A hA
    let O : Opens (TangentBundle 𝓘(ℝ, E) M) :=
      ⟨normalTube g U ρ, isOpen_normalTube g U ρ⟩
    obtain ⟨B, Φ, hB, hΦ⟩ := glue_inverse_tube g O hinj hloc
    obtain ⟨L, hinv, hexpL, hLexp⟩ := inverse_tube_laws g O B Φ hΦ
    have hezero (q : M) : riemannianExp g q 0 = q :=
      (riemannian_exponential_local_addition g).2.2.2.1 q
    have hzeroO (q : M) (hq : q ∈ U) :
        (⟨q, 0⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ O := by
      exact ⟨hq, by simpa [metricNorm] using hρ⟩
    have hdiag (q : M) (hq : q ∈ U) : (q, q) ∈ B := by
      change (q, q) ∈ (B : Set _)
      rw [hB]
      exact ⟨⟨q, 0⟩, hzeroO q hq, Prod.ext rfl (hezero q)⟩
    have hLzero (q : M) (hq : q ∈ U) : L q q = 0 := by
      simpa only [hezero q] using hLexp q 0 (hzeroO q hq)
    obtain ⟨R, hR, hRρ, hdomain⟩ := centered_radius g A hA f hf.continuous B
      (fun p hp ↦ hdiag (f p) (hAU (hfA hp))) ρ hρ
    refine ⟨U, ρ, R, O, B, L, Φ, hAU, hρ, hR, hRρ, rfl, hOD,
      hΦ, hinv, hB, hexpL, hLexp, ?_⟩
    refine ⟨?_, hdomain, ?_, centered_vertical_jets g A f r hf O B Φ L hinv R hdomain, ?_⟩
    · intro q hq
      exact ⟨hezero q, hdiag q hq, hLzero q hq,
        inverse_diagonal_derivative g O B Φ L hinv hLexp q (hzeroO q hq) (hdiag q hq)⟩
    · intro p hp
      refine ⟨?_, centered_derivative_zero g f r hr hf O B Φ L hinv hLexp p
        (hzeroO (f p) (hAU (hfA hp))) (hdiag (f p) (hAU (hfA hp)))⟩
      simpa only [centeredLift, hezero p] using hLzero (f p) (hAU (hfA hp))
    · exact fun h ↦ (hEmpty h).elim

end ExponentialLift
end HolomorphicAnosov
