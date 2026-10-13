import HolomorphicAnosov.Dynamics.Anosov.FiniteC1NativePlaqueFamily
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Finite-order coherence of supplied native plaque families

Source: Hirsch--Pugh--Shub, *Invariant Manifolds*, LNM 583 (1977),
the continuous `C^r` embedding-section definition and first proof of (5.5),
printed pp.61--63; the strong-manifold regularity in (5.4), pp.60--61;
and the `C^r` unbranched-lamination convention on p.115. The same-source-germ
finite-order selection is used in GL10 of `g9.hps_anosov_global_lamination`.
DAG node: `geometry.hps_finite_order_native_plaque_coherence_g8`.

These are data definitions, not a claim that an arbitrary native partition
admits coherent plaque families. The supplied finite-C¹ family already gives
actual open-disc embeddings, their fixed ambient receiving chart, and their
factorization through the original intrinsic leaves. The additional coordinate
functions equal those SAME embeddings in that chart on their entire open disc.

The jets are Mathlib's actual `iteratedFDerivWithin`, with values in continuous
multilinear maps; no separately chosen jet arrays or derivative bounds replace
them. Smoothness on the open disc ensures these are the genuine derivatives
there. The order-zero derivative is the original value, including in rank zero.
The center is only a continuity parameter. Different finite orders can use
different local ranks, neighborhoods, frames and radii, all in the same partition.
No all-order common radius, ambient metric, center derivative or existence
certificate is assumed or asserted.
-/

noncomputable section

open scoped ContDiff Manifold Topology _root_.Topology

universe u

namespace HolomorphicAnosov.HPS

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ, E) ∞ M]
variable {D : RealTangentDistribution 𝓘(ℝ, E) M}
variable {ι : Type u} {L : ι → Type u} {r : ι → ℕ}
variable [∀ i, TopologicalSpace (L i)]
variable [∀ i, ChartedSpace (Fin (r i) → ℝ) (L i)]
variable [∀ i, IsManifold 𝓘(ℝ, Fin (r i) → ℝ) ∞ (L i)]

/-- Finite-order joint continuity for one supplied native finite-C¹ plaque family.

Source: HPS pp.61--63, continuity into `Emb^r`, and p.115, continuity of the
`r`-th tangent multiplane; Mathlib `ContDiff/FTaylorSeries.lean`, definition
`iteratedFDerivWithin`, gives the actual multilinear coordinate derivatives.

Each coordinate representative is specified as data and equals the fixed
receiving-chart coordinate of the original plaque throughout its open disc.
Values outside that disc are unrestricted. Smoothness and openness make the
within-disc derivatives independent of those exterior values. For every
`j ≤ N`, joint continuity is on the product of the original center neighborhood
and the original open model disc, in the operator topology of the continuous
`j`-multilinear maps. For `j = 0`, evaluation on the empty tuple gives the
coordinate value itself. No differentiation in the center is requested.
-/
structure FiniteOrderNativePlaqueCoherence
    {F : LeafPartition D ι L r} {center : M} {d : ℕ}
    (Φ : FiniteC1NativePlaqueFamily F center d) (N : ℕ) where
  coordinate : Φ.family.centerDomain → (Fin d → ℝ) → E
  coordinate_eq : ∀ p, Set.EqOn (coordinate p)
    (fun v ↦ extChartAt 𝓘(ℝ, E) Φ.family.receivingAnchor ((Φ.family.plaque p).param v))
    (Metric.ball (0 : Fin d → ℝ) Φ.family.radius)
  coordinate_smooth : ∀ p, ContDiffOn ℝ ∞ (coordinate p)
    (Metric.ball (0 : Fin d → ℝ) Φ.family.radius)
  jointly_continuous_derivatives : ∀ j : ℕ, j ≤ N → Continuous
    (fun z : Φ.family.centerDomain × Metric.ball (0 : Fin d → ℝ) Φ.family.radius ↦
      iteratedFDerivWithin ℝ j (coordinate z.1)
        (Metric.ball (0 : Fin d → ℝ) Φ.family.radius) z.2.1)

/-- A selection of coherent local families at every finite order and ambient center.

Source: HPS (5.4)--(5.5), pp.60--63, and the same-germ finite-order construction
in GL10 of `g9.hps_anosov_global_lamination`. This definition stores the selected
data; existence and same-germ source uniqueness belong to that theorem.

The order and center index the local dimension and actual finite-C¹ family.
Each family retains its own open center neighborhood, positive radius, frame,
fixed receiving chart and original-leaf factorization through the SAME `F`.
Thus this stores precisely a separately local finite-order selection, rather
than a global fixed-rank family with a common radius for infinitely many orders.
An empty ambient manifold has no centers to supply. Rank-zero models and order
zero are allowed; no auxiliary nonemptiness or positive-rank premise is imposed.
-/
structure SelectedFiniteOrderNativePlaqueFamilies (F : LeafPartition D ι L r) where
  dimension : ℕ → M → ℕ
  family : ∀ (N : ℕ) (center : M), FiniteC1NativePlaqueFamily F center (dimension N center)
  coherence : ∀ (N : ℕ) (center : M), FiniteOrderNativePlaqueCoherence (family N center) N

end HolomorphicAnosov.HPS
