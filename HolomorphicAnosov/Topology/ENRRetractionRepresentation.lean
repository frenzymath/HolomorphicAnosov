import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.ContinuousMap.Basic

/-!
# Euclidean neighborhood-retract representation data

Source: Dold, *Fixed point index and fixed point theorem for Euclidean neighborhood retracts*,
Topology 4 (1965), definition (2.1) and construction (2.3), printed p.3.
DAG node: `topo.enr_retraction_representation`.

These are pure data definitions. The Euclidean domain, section and retraction are the original
ones; only the identity `r ∘ s = id` is a certificate field. No index, orientation, homology,
excision or independence axiom is a field. The maps on inverse-image domains are literal
compositions. In particular an isolating set need not be invariant under the continuous map,
and its closure need not be compact to define this data. All definitions allow dimension zero.
The integer index will use the separately produced standard-positive Euclidean index.
-/

namespace HolomorphicAnosov.FixedPointIndexInterface

universe u

/-- Dold's real Euclidean model, with its usual L2 topology and ordered coordinates. -/
abbrev Euclidean (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Literal Euclidean neighborhood-retract data, Dold (2.1), p.3.
The metrizable/compact assumptions on a particular space belong to theorems using this data.
They are not replaced by a supplied index function or index axioms. -/
structure ENRRepresentation (X : Type u) [TopologicalSpace X] where
  dimension : ℕ
  domain : Set (Euclidean dimension)
  domain_open : IsOpen domain
  sectionMap : C(X, domain)
  retraction : C(domain, X)
  retraction_section : Function.LeftInverse retraction sectionMap

/-- Existence of the actual representation data, not an output predicate about fixed points. -/
def HasENRRepresentation (X : Type u) [TopologicalSpace X] : Prop :=
  Nonempty (ENRRepresentation X)

/-- The original Euclidean inverse-image domain `r⁻¹(W)`, Dold (2.3), p.3. -/
def retractedDomain {X : Type u} [TopologicalSpace X] (e : ENRRepresentation X)
    (W : Set X) : Set (Euclidean e.dimension) :=
  {v | ∃ hv : v ∈ e.domain, e.retraction ⟨v, hv⟩ ∈ W}

/-- The inclusion of the inverse-image domain into the original representation domain. -/
def retractedDomainInclusion {X : Type u} [TopologicalSpace X]
    (e : ENRRepresentation X) (W : Set X) : C(retractedDomain e W, e.domain) where
  toFun v := ⟨v.val, v.property.choose⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The literal map `s ∘ f ∘ r` on `r⁻¹(W)`, Dold (2.3), p.3.
No condition `f(W) ⊆ W` is part of the construction. -/
def retractedMap {X : Type u} [TopologicalSpace X] (e : ENRRepresentation X)
    (f : C(X, X)) (W : Set X) : C(retractedDomain e W, Euclidean e.dimension) :=
  (⟨Subtype.val, continuous_subtype_val⟩ : C(e.domain, Euclidean e.dimension)).comp
    (e.sectionMap.comp (f.comp (e.retraction.comp (retractedDomainInclusion e W))))

/-- The domain point `r(v)` belongs to the given local map domain whenever `W ⊆ U`. -/
def retractedDomainToLocalDomain {X : Type u} [TopologicalSpace X]
    (e : ENRRepresentation X) (U W : Set X) (hWU : W ⊆ U) :
    C(retractedDomain e W, U) where
  toFun v := ⟨e.retraction (retractedDomainInclusion e W v), hWU v.property.choose_spec⟩
  continuous_toFun :=
    (e.retraction.continuous.comp (retractedDomainInclusion e W).continuous).subtype_mk _

/-- The same retraction construction for a map defined only on an open part of X.
Source: Dold (2.3), p.3, and Granas (10.1.1), p.223. The map's domain membership is
proved from `W ⊆ U`; no extension of the local map outside U is chosen. -/
def retractedLocalMap {X : Type u} [TopologicalSpace X]
    (e : ENRRepresentation X) (U W : Set X) (hWU : W ⊆ U) (f : C(U, X)) :
    C(retractedDomain e W, Euclidean e.dimension) :=
  (⟨Subtype.val, continuous_subtype_val⟩ : C(e.domain, Euclidean e.dimension)).comp
    (e.sectionMap.comp (f.comp (retractedDomainToLocalDomain e U W hWU)))

/-- An actual isolating open neighborhood: its only fixed point is the marked point.
This contains no index data. Source: Dold (1.3), p.1, and the finite isolation step D10
of `topo.compact_enr_lefschetz_local_index_sum_g7`. -/
def IsolatingNeighborhood {X : Type u} [TopologicalSpace X]
    (f : C(X, X)) (x : X) (W : Set X) : Prop :=
  IsOpen W ∧ x ∈ W ∧ ∀ y ∈ W, f y = y ↔ y = x

/-- When the fixed set is finite, this is the canonical set excluding all other fixed points.
Its openness and isolation certificate are theorem obligations, not supplied index axioms.
Source: the finite fixed-set isolation step D10 of the compact ENR Lefschetz node. -/
def finiteLocalDomain {X : Type u} [TopologicalSpace X] (f : C(X, X)) (x : X) : Set X :=
  ({y : X | f y = y} \ {x})ᶜ

end HolomorphicAnosov.FixedPointIndexInterface
