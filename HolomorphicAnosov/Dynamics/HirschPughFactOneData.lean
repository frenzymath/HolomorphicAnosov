import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Topology.MetricSpace.Defs

namespace HolomorphicAnosov

open Set
open scoped ContDiff Manifold Topology _root_.Topology

noncomputable section

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type v} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- A continuous tangent subbundle restricted to a set, with the topology induced
by the actual tangent inclusion. Shub (1987), pp.71–73, works over the compact
hyperbolic set, rather than assuming an extension over a neighborhood. Local
finite-dimensional linear trivializations express precisely this continuity. -/
structure ContinuousTangentSubbundleOn (Λ : Set M) where
  /-- The actual tangent subspace at each point of the given set. -/
  fibre : ∀ x : Λ, Submodule ℝ (TangentSpace 𝓘(ℝ, E) (x : M))
  /-- A local linear bundle chart in the tangent-inclusion-induced topology. -/
  locally_trivial : ∀ x : Λ, ∃ r : ℕ,
    letI : TopologicalSpace (Bundle.TotalSpace (Fin r → ℝ) (fun y : Λ ↦ ↥(fibre y))) :=
      TopologicalSpace.induced
        (fun z ↦ (⟨(z.proj : M), z.snd.val⟩ : TangentBundle 𝓘(ℝ, E) M)) inferInstance
    ∃ e : Bundle.Trivialization (Fin r → ℝ)
        (Bundle.TotalSpace.proj (F := Fin r → ℝ) (E := fun y : Λ ↦ ↥(fibre y))),
      x ∈ e.baseSet ∧ e.IsLinear ℝ

/-- The norm of an actual tangent vector in the supplied smooth positive tensor.
Hirsch–Pugh (1969), p.148, and Shub (1987), pp.21–22. -/
def hyperbolicRiemannianNorm
    (h : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
    {x : M} (v : TangentSpace 𝓘(ℝ, E) x) : ℝ :=
  Real.sqrt (h.inner x v v)

/-- Integer-time orbit of the original diffeomorphism, using the group of actual
self-homeomorphisms. Negative times are genuine inverse iterates. -/
def hyperbolicIntegerOrbit (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
    (n : ℤ) (x : M) : M :=
  (f.toHomeomorph ^ n) x

/-- The full original hyperbolic datum and local maximality hypothesis of Fact 1.

The estimates are vector inequalities in the original smooth metric, equivalent
to the corresponding restricted operator-norm estimates. No adapted metric,
local plaque, bracket, or conclusion of Fact 1 is part of the input. -/
structure HyperbolicSetFactOneDatum
    (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (Λ : Set M) where
  /-- The given nonempty invariant set. -/
  nonempty : Λ.Nonempty
  /-- Compactness of the original set. -/
  compact : IsCompact Λ
  /-- Forward invariance under the original map. -/
  forward_mem : MapsTo f Λ Λ
  /-- Backward invariance, so the restriction is onto. -/
  backward_mem : MapsTo f.symm Λ Λ
  /-- The original smooth Riemannian metric. -/
  originalMetric : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
    (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)
  /-- The stable bundle on the set, with its actual inclusion topology. -/
  stable : ContinuousTangentSubbundleOn (E := E) Λ
  /-- The unstable bundle on the set. -/
  unstable : ContinuousTangentSubbundleOn (E := E) Λ
  /-- Complementarity is only asserted at points of the original set. -/
  complementary : ∀ x : Λ, IsCompl (stable.fibre x) (unstable.fibre x)
  /-- Invariance uses the original forward derivative. -/
  stable_invariant : ∀ x : Λ,
    (stable.fibre x).map (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x).toLinearMap =
      stable.fibre ⟨f x, forward_mem x.property⟩
  /-- Invariance of the unstable subspace under the same original derivative. -/
  unstable_invariant : ∀ x : Λ,
    (unstable.fibre x).map (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x).toLinearMap =
      unstable.fibre ⟨f x, forward_mem x.property⟩
  /-- The original uniform hyperbolicity constant. -/
  C : ℝ
  /-- Its conventional lower bound. -/
  one_le_C : 1 ≤ C
  /-- The original exponential decay rate. -/
  rate : ℝ
  /-- Strict positivity of the decay rate. -/
  rate_pos : 0 < rate
  /-- Strict contraction of the decay rate. -/
  rate_lt_one : rate < 1
  /-- The stable estimate is for every natural iterate of the original map. -/
  stable_estimate : ∀ (n : ℕ) (x : Λ) (v : TangentSpace 𝓘(ℝ, E) (x : M)),
    v ∈ stable.fibre x →
      hyperbolicRiemannianNorm originalMetric
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ((f : M → M)^[n]) x v) ≤
        C * rate ^ n * hyperbolicRiemannianNorm originalMetric v
  /-- The unstable estimate uses actual backward iterates, including time zero. -/
  unstable_estimate : ∀ (n : ℕ) (x : Λ) (v : TangentSpace 𝓘(ℝ, E) (x : M)),
    v ∈ unstable.fibre x →
      hyperbolicRiemannianNorm originalMetric
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ((f.symm : M → M)^[n]) x v) ≤
        C * rate ^ n * hyperbolicRiemannianNorm originalMetric v
  /-- The original isolating open neighborhood. -/
  isolatingNeighborhood : Set M
  /-- This neighborhood is ambient open. -/
  isolating_open : IsOpen isolatingNeighborhood
  /-- It contains the original invariant set. -/
  subset_isolating : Λ ⊆ isolatingNeighborhood
  /-- Literal local maximality: every integer orbit stays in the neighborhood. -/
  locally_maximal : ∀ x : M,
    x ∈ Λ ↔ ∀ n : ℤ, hyperbolicIntegerOrbit f n x ∈ isolatingNeighborhood

/-- The literal closed stable orbit plaque in the original invariant set.
Bowen, Fact 1, pp.726–727; Shub, Theorem 6.2(3), p.72. -/
def hyperbolicClosedStablePlaque
    (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (Λ : Set M)
    (d : MetricSpace M) (γ : ℝ) (x : M) : Set M :=
  {y ∈ Λ | ∀ n : ℕ, d.dist ((f : M → M)^[n] y) ((f : M → M)^[n] x) ≤ γ}

/-- The literal closed unstable orbit plaque, using actual inverse iterates. -/
def hyperbolicClosedUnstablePlaque
    (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (Λ : Set M)
    (d : MetricSpace M) (γ : ℝ) (x : M) : Set M :=
  {y ∈ Λ | ∀ n : ℕ,
    d.dist ((f.symm : M → M)^[n] y) ((f.symm : M → M)^[n] x) ≤ γ}

/-- The closed close-pair domain in the original product topology, including
the threshold boundary. Compactness gives its closedness once metric compatibility
is proved; closedness is not an additional premise. -/
def hyperbolicClosedPairDomain (Λ : Set M) (d : MetricSpace M) (ε : ℝ) :
    Set (M × M) :=
  {p | p.1 ∈ Λ ∧ p.2 ∈ Λ ∧ d.dist p.1 p.2 ≤ ε}


end

end HolomorphicAnosov
