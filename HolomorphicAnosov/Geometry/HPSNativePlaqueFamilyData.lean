import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Geometry.Manifold.Diffeomorph
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.RealTangentDistribution

/-! Embedded smooth plaques tangent to a distribution are equipped with compatible intrinsic leaf
charts and local families continuous in the C¹ topology on compact parameter sets.
(Hirsch–Pugh–Shub, (5.4)–(5.5), pp.60–63; §6B, pp.111–114; (7.5)–(7.6), pp.127–129) -/

namespace HolomorphicAnosov

open Set Topology _root_.Topology
open scoped ContDiff Manifold ENNReal

universe u v w z t

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type v} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {V : Type z} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- An embedded smooth plaque parametrized on an open finite-dimensional domain, with injective
derivative whose image is the prescribed tangent distribution. (Hirsch–Pugh–Shub, (5.4)–(5.5),
pp.60–63; (6B.4), pp.111–114) -/
structure NativeEmbeddedPlaque
    (D : ∀ x : M, Submodule ℝ (TangentSpace I x)) (center : M) where
  /-- The plaque parameter model is finite-dimensional. -/
  [finiteDimensional : FiniteDimensional ℝ V]
  /-- The open parameter domain of the plaque. -/
  domain : Set V
  /-- The parameter domain is open. -/
  domain_open : IsOpen domain
  /-- The parameter domain contains zero. -/
  zero_mem : (0 : V) ∈ domain
  /-- The plaque parametrization. -/
  param : V → M
  /-- The zero parameter maps to the plaque center. -/
  centered : param 0 = center
  /-- The parametrization is smooth on its domain. -/
  smooth : ContMDiffOn 𝓘(ℝ, V) I ∞ param domain
  /-- The parametrization restricted to its domain is a topological embedding into the ambient
manifold. -/
  embedded : IsEmbedding (fun u : domain ↦ param u)
  /-- The derivative of the parametrization is injective at every point of its domain. -/
  immersed : ∀ u ∈ domain, Function.Injective (mfderiv 𝓘(ℝ, V) I param u)
  /-- The derivative image of the parametrization equals the prescribed tangent distribution. -/
  tangent : ∀ u ∈ domain, (mfderiv 𝓘(ℝ, V) I param u).range = D (param u)

namespace NativeEmbeddedPlaque

variable {I}
variable {D : ∀ x : M, Submodule ℝ (TangentSpace I x)} {center : M}

/-- The image of the plaque parameter domain under its parametrization. (Hirsch–Pugh–Shub, (5.5),
pp.61–63) -/
def image (P : NativeEmbeddedPlaque I (V := V) D center) : Set M :=
  P.param '' P.domain

end NativeEmbeddedPlaque

variable {W : Type z} [NormedAddCommGroup W] [NormedSpace ℝ W]
variable {L : Type t} [TopologicalSpace L] [ChartedSpace W L]
  [IsManifold 𝓘(ℝ, W) ∞ L]

/-- A smooth plaque chart into an intrinsic leaf whose smooth injective inclusion has the prescribed
tangent distribution and agrees with the ambient plaque parametrization. (Hirsch–Pugh–Shub, §6B,
(6B.4), pp.111–114; (7.5)–(7.6), pp.127–129) -/
structure NativePlaqueIntrinsicChart
    (D : ∀ x : M, Submodule ℝ (TangentSpace I x)) (center : M)
    (P : NativeEmbeddedPlaque I (V := V) D center) where
  /-- The inclusion of the intrinsic leaf into the ambient manifold. -/
  inclusion : L → M
  /-- The leaf inclusion is smooth. -/
  inclusion_smooth : ContMDiff 𝓘(ℝ, W) I ∞ inclusion
  /-- The leaf inclusion is injective. -/
  inclusion_injective : Function.Injective inclusion
  /-- The derivative of the leaf inclusion is injective at every point. -/
  inclusion_immersed : ∀ y : L,
    Function.Injective (mfderiv 𝓘(ℝ, W) I inclusion y)
  /-- The derivative image of the leaf inclusion equals the prescribed tangent distribution. -/
  inclusion_tangent : ∀ y : L,
    (mfderiv 𝓘(ℝ, W) I inclusion y).range = D (inclusion y)
  /-- The plaque parameter map into the intrinsic leaf. -/
  toLeaf : V → L
  /-- The plaque image is open in the intrinsic leaf. -/
  leafImage_open : IsOpen (toLeaf '' P.domain)
  /-- The plaque parameter map into the leaf is smooth on its domain. -/
  toLeaf_smooth : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, W) ∞ toLeaf P.domain
  /-- The inverse plaque coordinate map on the intrinsic leaf. -/
  inverse : L → V
  /-- The inverse coordinate map is smooth on the intrinsic plaque image. -/
  inverse_smooth : ContMDiffOn 𝓘(ℝ, W) 𝓘(ℝ, V) ∞ inverse (toLeaf '' P.domain)
  /-- The inverse coordinate map recovers every parameter in the plaque domain. -/
  inverse_toLeaf : ∀ u ∈ P.domain, inverse (toLeaf u) = u
  /-- The parameter map recovers every point in the intrinsic plaque image. -/
  toLeaf_inverse : ∀ y ∈ toLeaf '' P.domain, toLeaf (inverse y) = y
  /-- Composing the plaque parameter map with the leaf inclusion gives the ambient plaque
parametrization on its domain. -/
  inclusion_toLeaf : ∀ u ∈ P.domain, inclusion (toLeaf u) = P.param u

/-- A local family of embedded smooth plaques on a common open ball, with a continuous tangent frame
and C¹ continuity in fixed ambient coordinates on compact parameter sets. (Hirsch–Pugh–Shub,
(5.5), p.62; §6B) -/
structure NativePlaqueFamily
    (D : ∀ x : M, Submodule ℝ (TangentSpace I x)) (center : M) where
  /-- An open neighborhood of the reference center. -/
  centerDomain : Set M
  /-- The center domain is open. -/
  centerDomain_open : IsOpen centerDomain
  /-- The center domain contains the reference center. -/
  center_mem : center ∈ centerDomain
  /-- The radius of the common plaque parameter ball. -/
  radius : ℝ
  /-- The common parameter radius is positive. -/
  radius_pos : 0 < radius
  /-- An embedded plaque centered at each point of the center domain. -/
  plaque : ∀ p : centerDomain, NativeEmbeddedPlaque I (V := V) D p.1
  /-- Every plaque parameter domain is the common open ball. -/
  domain_eq : ∀ p, (plaque p).domain = Metric.ball (0 : V) radius
  /-- A linear frame identifying the parameter model with the tangent distribution at each center. -/
  frame : ∀ p : centerDomain, V ≃L[ℝ] ↥(D p.1)
  /-- The frame is jointly continuous in the center and vector parameter in the tangent-bundle
topology. -/
  frame_continuous : Continuous
    (fun z : centerDomain × V ↦
      (⟨z.1.1, (frame z.1 z.2).1⟩ : TangentBundle I M))
  /-- The anchor of the fixed ambient coordinate chart for the family. -/
  receivingAnchor : M
  /-- All plaque values on the common parameter ball lie in the fixed chart source. -/
  receiving_domain : ∀ (p : centerDomain) (u : V),
    u ∈ Metric.ball (0 : V) radius →
      (plaque p).param u ∈ (extChartAt I receivingAnchor).source
  /-- The plaque parametrizations are jointly continuous in the center and leaf parameter. -/
  jointly_continuous : Continuous
    (fun z : centerDomain × Metric.ball (0 : V) radius ↦ (plaque z.1).param z.2.1)
  /-- Each plaque parametrization expressed in the fixed ambient chart is smooth on the common ball. -/
  coordinate_smooth : ∀ p : centerDomain,
    ContDiffOn ℝ ∞ (fun u : V ↦ extChartAt I receivingAnchor ((plaque p).param u))
      (Metric.ball (0 : V) radius)
  /-- The coordinate derivative in the leaf parameter is jointly continuous in the center and leaf
parameter. -/
  jointly_continuous_derivative : Continuous
    (fun z : centerDomain × Metric.ball (0 : V) radius ↦
      fderiv ℝ (fun u : V ↦ extChartAt I receivingAnchor ((plaque z.1).param u)) z.2.1)
  /-- Plaque coordinate maps and their leaf-parameter derivatives depend continuously on the center,
uniformly on each compact subset of the common parameter ball. (Hirsch–Pugh–Shub, (5.5), p.62) -/
  compact_C1 : ∀ K : Set V, IsCompact K → K ⊆ Metric.ball (0 : V) radius →
    ∀ p₀ : centerDomain, ∀ η : ℝ, 0 < η →
      ∃ N : Set centerDomain, IsOpen N ∧ p₀ ∈ N ∧ ∀ p ∈ N, ∀ u ∈ K,
        ‖extChartAt I receivingAnchor ((plaque p).param u) -
          extChartAt I receivingAnchor ((plaque p₀).param u)‖ < η ∧
        ‖fderiv ℝ (fun v : V ↦ extChartAt I receivingAnchor ((plaque p).param v)) u -
          fderiv ℝ (fun v : V ↦ extChartAt I receivingAnchor ((plaque p₀).param v)) u‖ < η

end HolomorphicAnosov
