import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Topology.VectorBundle.Basic

/-!+# Hyperbolic basic sets with the original restricted tangent bundle

Sources: Smale, *Differentiable dynamical systems* (1967), I§6 p.776
(continuous invariant splitting of the tangent bundle restricted to the set,
with locally varying fibre rank), and I§9 (9.2) pp.785–786 (compactness,
invariance, transitivity and an isolating open neighborhood); Bowen,
*Markov partitions for Axiom A diffeomorphisms* (1970), pp.725–727.
This is a definition interface, not a hyperbolicity or Markov-partition theorem.
The base of each subbundle is the subset with its induced topology. It is not
assumed to be a manifold. The original smooth metric and original finite
distance are retained; their agreement is local, permitting disconnected M.
-/

namespace HolomorphicAnosov.Dynamics

open scoped Bundle ContDiff

variable {n : ℕ}
variable {M : Type*} [MetricSpace M]
variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
variable [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ M]

/-- Continuous tangent subbundle restricted to an arbitrary subset, in Smale
I§6 p.776. Local linear trivializations use the topology induced by inclusion
in the original tangent bundle. Rank may vary between relative neighborhoods.
No ambient extension or manifold structure on the subset is required. -/
structure RelativeContinuousTangentSubbundle (Λ : Set M) where
  distribution : ∀ x : Λ,
    Submodule ℝ (TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x.val)
  locally_trivial : ∀ x : Λ, ∃ r : ℕ,
    letI : TopologicalSpace
        (Bundle.TotalSpace (Fin r → ℝ) (fun y : Λ ↦ ↥(distribution y))) :=
      TopologicalSpace.induced
        (fun z ↦ (⟨z.proj.val, z.snd.val⟩ :
          TangentBundle (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) M))
        inferInstance
    ∃ e : Bundle.Trivialization (Fin r → ℝ)
        (Bundle.TotalSpace.proj (F := Fin r → ℝ)
          (E := fun y : Λ ↦ ↥(distribution y))),
      x ∈ e.baseSet ∧ e.IsLinear ℝ

/-- The original hyperbolic basic-set data used in Manning's signed trace
formula: nonempty compact invariant locally maximal transitive subset, with
continuous complementary invariant real tangent subbundles over that subset
and all-time exponential bounds in the supplied smooth Riemannian metric.

The inequalities include n=0, use the derivative of the actual iterate, and
evaluate the metric at its actual endpoint. The unstable estimate uses the
inverse iterate, without requiring the stable derivative to be invertible.
Distance agreement is imposed only locally, not between distinct components.
These are actual defining data and predicates; no existence theorem is used.
Smale I§6 p.776 and I§9 pp.785–786; Bowen1970 pp.725–727. -/
structure RelativeHyperbolicBasicSet
    (f : Diffeomorph
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) M M ∞)
    (Λ : Set M) where
  metric : Bundle.ContMDiffRiemannianMetric
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞
    (EuclideanSpace ℝ (Fin n))
    (fun x : M ↦ TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x)
  distance_local :
    letI : Bundle.RiemannianBundle
        (fun x : M ↦ TangentSpace
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x) :=
      ⟨metric.toRiemannianMetric⟩
    ∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, ∀ z ∈ U, edist y z = Manifold.riemannianEDist
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) y z
  nonempty : Λ.Nonempty
  compact : IsCompact Λ
  invariant : ∀ x : M, f x ∈ Λ ↔ x ∈ Λ
  locally_maximal : ∃ U : Set M, IsOpen U ∧ Λ ⊆ U ∧
    ∀ x : M, x ∈ Λ ↔ ∀ k : ℤ, (f.toEquiv ^ k) x ∈ U
  transitive : ∀ U V : Set Λ, IsOpen U → IsOpen V →
    U.Nonempty → V.Nonempty →
    ∃ k : ℕ, ∃ x ∈ U, ((f : M → M)^[k]) x.val ∈ Subtype.val '' V
  stable : RelativeContinuousTangentSubbundle (n := n) Λ
  unstable : RelativeContinuousTangentSubbundle (n := n) Λ
  isCompl : ∀ x : Λ, IsCompl (stable.distribution x) (unstable.distribution x)
  stable_map : ∀ x : Λ,
    (stable.distribution x).map (mfderiv
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) f x.val).toLinearMap =
      stable.distribution ⟨f x.val, (invariant x.val).mpr x.property⟩
  unstable_map : ∀ x : Λ,
    (unstable.distribution x).map (mfderiv
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) f x.val).toLinearMap =
      unstable.distribution ⟨f x.val, (invariant x.val).mpr x.property⟩
  C : ℝ
  one_le_C : 1 ≤ C
  rate : ℝ
  rate_pos : 0 < rate
  rate_lt_one : rate < 1
  stable_bound : ∀ (x : Λ) (v : stable.distribution x) (k : ℕ),
    Real.sqrt (metric.inner (((f : M → M)^[k]) x.val)
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        ((f : M → M)^[k]) x.val v.val)
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        ((f : M → M)^[k]) x.val v.val)) ≤
      C * rate ^ k * Real.sqrt (metric.inner x.val v.val v.val)
  unstable_bound : ∀ (x : Λ) (v : unstable.distribution x) (k : ℕ),
    Real.sqrt (metric.inner (((f.symm : M → M)^[k]) x.val)
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        ((f.symm : M → M)^[k]) x.val v.val)
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        ((f.symm : M → M)^[k]) x.val v.val)) ≤
      C * rate ^ k * Real.sqrt (metric.inner x.val v.val v.val)

end HolomorphicAnosov.Dynamics
