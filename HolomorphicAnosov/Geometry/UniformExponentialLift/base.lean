import HolomorphicAnosov.Geometry.RiemannianExponentialLocalAddition
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

/-! Geodesic exponential maps, metric tubes, centered lifts, and continuous vertical jets
for exponential lifts over compact invariant sets.
(Hirsch–Pugh–Shub, Thm 5.5, pp. 61–62; Andrews, §8.11, pp. 83–86 and Prop. 10.3.1, pp. 96–98) -/

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

/-- The domain of the time-one geodesic exponential map. (Andrews, §8.11, pp. 83–85) -/
abbrev riemannianExpDomain
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _)) :
    Set (TangentBundle 𝓘(ℝ, E) M) :=
  riemannianExponentialDomain g

/-- The Riemannian exponential map at a basepoint, given by the time-one geodesic endpoint.
(Andrews, §8.11, p. 84) -/
def riemannianExp
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (p : M) (v : TangentSpace 𝓘(ℝ, E) p) : M :=
  riemannianExponential g ⟨p, v⟩

/-- The Riemannian norm of a tangent vector. (Hirsch–Pugh–Shub, p. 62) -/
def metricNorm
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (p : M) (v : TangentSpace 𝓘(ℝ, E) p) : ℝ :=
  Real.sqrt (g.inner p v v)

/-- The expression of a fiber map in fixed source and target tangent frames.
(Hirsch–Pugh–Shub, Thm 5.5, pp. 61–62) -/
def fibreExpression (A : Set M) (f : M → M)
    (G : ∀ p : A, TangentSpace 𝓘(ℝ, E) (p : M) → TangentSpace 𝓘(ℝ, E) (f p))
    (s t : M) (p : A) (u : E) : E :=
  (trivializationAt E (TangentSpace 𝓘(ℝ, E)) t).continuousLinearMapAt ℝ (f p)
    (G p ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) s).symmL ℝ (p : M) u))

/-- Fiberwise `C^r` regularity and joint continuity of vertical jets through order `r`
on specified fiber domains, with the subspace topology on the parameter set `A`.
(Hirsch–Pugh–Shub, Thm 5.5, pp. 61–62) -/
def HasContinuousVerticalJetsOn (A : Set M) (f : M → M) (r : ℕ∞)
    (G : ∀ p : A, TangentSpace 𝓘(ℝ, E) (p : M) → TangentSpace 𝓘(ℝ, E) (f p))
    (V : ∀ p : A, Set (TangentSpace 𝓘(ℝ, E) (p : M))) : Prop :=
  (∀ p : A, ContDiffOn ℝ r (fun u : E ↦
    tangentSpaceCastModel 𝓘(ℝ, E) (f p)
      (G p ((tangentSpaceCastModel 𝓘(ℝ, E) (p : M)).symm u)))
    ((tangentSpaceCastModel 𝓘(ℝ, E) (p : M)).symm ⁻¹' V p)) ∧
    ∀ (s t : M) (j : ℕ), (j : ℕ∞) ≤ r →
      ContinuousOn
        (fun z : A × E ↦ iteratedFDeriv ℝ j (fibreExpression A f G s t z.1) z.2)
        {z | (z.1 : M) ∈ (chartAt E s).source ∧ f z.1 ∈ (chartAt E t).source ∧
          (trivializationAt E (TangentSpace 𝓘(ℝ, E)) s).symmL ℝ (z.1 : M) z.2 ∈ V z.1}

/-- Fiberwise `C^r` regularity and joint continuity of vertical jets through order `r`
on whole fibers. (Hirsch–Pugh–Shub, Thm 5.5, pp. 61–62) -/
def HasContinuousVerticalJets (A : Set M) (f : M → M) (r : ℕ∞)
    (G : ∀ p : A, TangentSpace 𝓘(ℝ, E) (p : M) → TangentSpace 𝓘(ℝ, E) (f p)) : Prop :=
  HasContinuousVerticalJetsOn A f r G (fun _ ↦ univ)

/-- The tangent vectors of metric norm less than `ρ` over an open base set `U`.
(Hirsch–Pugh–Shub, p. 62) -/
def normalTube
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (U : Opens M) (ρ : ℝ) : Set (TangentBundle 𝓘(ℝ, E) M) :=
  {z | z.proj ∈ U ∧ metricNorm g z.proj z.snd < ρ}

/-- The centered lift `v ↦ L (f p) (f (riemannianExp g p v))` defined by a moving-base
inverse exponential map. (Hirsch–Pugh–Shub, Thm 5.5, p. 62) -/
def centeredLift
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (f : M → M) (L : (q : M) → M → TangentSpace 𝓘(ℝ, E) q)
    (p : M) (v : TangentSpace 𝓘(ℝ, E) p) : TangentSpace 𝓘(ℝ, E) (f p) :=
  L (f p) (f (riemannianExp g p v))


end ExponentialLift
end HolomorphicAnosov
