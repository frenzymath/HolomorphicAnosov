import HolomorphicAnosov.Dynamics.Anosov.NativeSmoothLamination
import HolomorphicAnosov.Geometry.HPSNativePlaqueFamilyData
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousRealTangentSubbundle
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Finite C¹ families of plaques in a supplied native partition

Source: Hirsch--Pugh--Shub, *Invariant Manifolds*, LNM583 (1977), printed
pp.61--63, the continuous embedding-section definition and first proof of (5.5);
pp.111--114, native continuation (6B.1)--(6B.4). The selected finite-C¹ local
family and compact-core clauses are those used in GL2/GL4/GL10 of
`g9.hps_anosov_global_lamination`.

The basic `NativePlaqueFamily` already records the actual enlarged open-domain
embedded smooth plaques, continuous finite frames, common receiving chart,
joint values and actual first derivatives in the leaf variable. This module
adds their literal factorization through a specified `HPS.LeafPartition` and
the closed-inner-disc continuous-map-valued first-jet data. It does not assert
existence, choose an ambient metric or impose a global rank on the partition.
All supplied function data have their exact evaluation laws; no opaque or
postponed data occurs. This is local finite-C¹ regularity, not differentiability
in the center parameter and not a common radius for all derivative orders.
-/

noncomputable section
open scoped ContDiff Manifold Topology _root_.Topology
open Set Topology _root_.Topology

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

/-- One local finite-C¹ family of actual native plaques, with a local finite rank.

Source: HPS pp.61--63 and pp.111--114. `family` is the already defined
enlarged-open-domain family with continuous local frame and actual leaf-variable
derivatives. Each open-disc embedding factors through the supplied native leaf
immersion and a genuine diffeomorphism onto an intrinsically open plaque. The
labels may vary with the center and different centers may label the same leaf.

For each `0 < a < family.radius`, `closedJet a` is the literal restriction of
that SAME enlarged family, paired with its actual coordinate derivative, on the
closed inner disc. It is continuous into Mathlib's compact-source continuous-map
space. Its norm is the supremum of the product norm, which is the maximum of
the coordinate-value norm and operator-derivative norm; this is exactly the
finite-C¹ norm, not a pointwise topology or a separately chosen bound. Compact
center cores have compact images in that same function space. The closed disc
has compact topology from its finite-dimensional real coordinate model, also
in rank zero; no metric on the ambient manifold is used.
-/
structure FiniteC1NativePlaqueFamily
    (F : LeafPartition D ι L r) (center : M) (d : ℕ) where
  family : NativePlaqueFamily 𝓘(ℝ, E) (V := Fin d → ℝ) D center
  label : family.centerDomain → ι
  receivingPlaque : ∀ p, TopologicalSpace.Opens (L (label p))
  chart : ∀ p, Diffeomorph 𝓘(ℝ, Fin d → ℝ)
    𝓘(ℝ, Fin (r (label p)) → ℝ)
    (⟨Metric.ball (0 : Fin d → ℝ) family.radius, Metric.isOpen_ball⟩ :
      TopologicalSpace.Opens (Fin d → ℝ)) (receivingPlaque p) ∞
  factorization : ∀ p (v : Metric.ball (0 : Fin d → ℝ) family.radius),
    (family.plaque p).param v = (F.leaf (label p)).inclusion (chart p v)
  closedJet : ∀ a : ℝ, 0 < a → a < family.radius →
    family.centerDomain →
      C(↥(Metric.closedBall (0 : Fin d → ℝ) a), E × ((Fin d → ℝ) →L[ℝ] E))
  closedJet_eval : ∀ (a : ℝ) (ha : 0 < a) (haR : a < family.radius)
    (p : family.centerDomain) (v : Metric.closedBall (0 : Fin d → ℝ) a),
    closedJet a ha haR p v =
      (extChartAt 𝓘(ℝ, E) family.receivingAnchor ((family.plaque p).param v),
        fderiv ℝ (fun w : Fin d → ℝ ↦
          extChartAt 𝓘(ℝ, E) family.receivingAnchor ((family.plaque p).param w)) v)
  closedJet_continuous : ∀ (a : ℝ) (ha : 0 < a) (haR : a < family.radius),
    Continuous (closedJet a ha haR)
  compact_center_image : ∀ (a : ℝ) (ha : 0 < a) (haR : a < family.radius)
    (K : Set family.centerDomain), IsCompact K → IsCompact (closedJet a ha haR '' K)

/-- A selected native finite-C¹ plaque family at each original ambient center.

Source: HPS (5.5), printed pp.61--63, continuous local embedding sections, and
native continuation pp.111--114. Each center has its own dimension, neighborhood,
frame, enlarged radius and family in the supplied partition. Thus no single
rank or uniform global radius is imposed. This stores families as data and
does not assert their existence for an arbitrary smooth partition. On an empty
ambient manifold the selection is the empty dependent function.
-/
structure SelectedFiniteC1NativePlaqueFamilies (F : LeafPartition D ι L r) where
  dimension : M → ℕ
  family : ∀ center : M, FiniteC1NativePlaqueFamily F center (dimension center)

end HolomorphicAnosov.HPS
