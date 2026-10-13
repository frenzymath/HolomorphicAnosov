import HolomorphicAnosov.Topology.Homology.ModTwoSingularSupportHomology
import Mathlib.Geometry.Manifold.Instances.Real

/-!
# Locally compatible mod-two local homology families

Source: Hatcher, Algebraic Topology, local sections and consistency on
printed pp.234–235 and Lemma3.27(a), p.236.
DAG node: `topo.def_mod2_local_homology_compatible_family_g4`.

These definitions reuse the actual ordinary mod-two relative singular homology.
A local family is compatible precisely when supported classes on coordinate
balls realize all its point values. No compact-support extension, orientation,
nonzero class, vanishing statement, or postponed proof is part of this data.
-/

noncomputable section

namespace HolomorphicAnosov.HatcherCompactSupport

universe u

open Set

/-- Short carrier alias of the existing ordinary mod-two support homology.
Source: Hatcher pp.115,153,233; the original shared definition is unchanged. -/
abbrev SupportHomology {M : Type u} [TopologicalSpace M] (A : Set M) (i : ℕ) :=
  (HolomorphicAnosov.Topology.Homology.modTwoSupportHomology M A i : Type u)

/-- The linear-map carrier of the existing canonical support restriction.
Source: Hatcher pp.118,233–235; no new homology map is constructed. -/
abbrev supportRestriction {M : Type u} [TopologicalSpace M] {A B : Set M}
    (h : B ⊆ A) (i : ℕ) : SupportHomology A i →ₗ[ZMod 2] SupportHomology B i :=
  (HolomorphicAnosov.Topology.Homology.modTwoSupportRestriction M A B h i).hom

/-- The restriction from a support to the local homology of one of its points.
Source: Hatcher Lemma3.27(a), p.236. -/
def supportToPoint {M : Type u} [TopologicalSpace M] (A : Set M) (i : ℕ) (x : A) :
    SupportHomology A i →ₗ[ZMod 2] SupportHomology ({x.val} : Set M) i :=
  supportRestriction (singleton_subset_iff.mpr x.property) i

/-- An actual coordinate ball, as an open subset in the original manifold topology.
Source: Hatcher local compatibility on chart balls, pp.234–235. -/
def chartBall {M : Type u} [TopologicalSpace M] {n : ℕ}
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (v : EuclideanSpace ℝ (Fin n)) (r : ℝ) : Set M :=
  c.source ∩ c ⁻¹' Metric.ball v r

/-- A family of actual local top-homology elements is locally compatible when it
comes from a supported class on some coordinate ball around every point.
This is Hatcher's section condition, written without a new covering-space topology.
The coordinate map need not be the atlas's preferred chart. The support class is
an element of the genuine relative homology above; it is not an assumed compact
extension. Source: Hatcher pp.234–235 and Lemma3.27(a), p.236. -/
def LocallyCompatible {M : Type u} [TopologicalSpace M] (n : ℕ)
    (s : ∀ x : M, SupportHomology ({x} : Set M) n) : Prop :=
  ∀ x : M, ∃ (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (r : ℝ),
    x ∈ c.source ∧ 0 < r ∧ Metric.ball (c x) r ⊆ c.target ∧
    ∃ b : SupportHomology (chartBall c (c x) r) n,
      ∀ y : chartBall c (c x) r, supportToPoint (chartBall c (c x) r) n y b = s y.val

end HolomorphicAnosov.HatcherCompactSupport
