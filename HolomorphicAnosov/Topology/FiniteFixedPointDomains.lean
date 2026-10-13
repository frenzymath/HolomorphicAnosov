import HolomorphicAnosov.Topology.ENRLocalFixedPointIndexConjugacy

/-!
# Canonical domains and local indices for finite fixed sets

Source: Dold, *Fixed point index and fixed point theorem for Euclidean neighborhood
retracts* (1965), (1.3), (1.5), pp.1–2 and (2.3), p.3. Remove all fixed points
other than the marked point and use the original retracted displacement index.
-/

noncomputable section
open TopologicalSpace
namespace HolomorphicAnosov.FixedPointIndexInterface
universe u

/-- The actual canonical open domain obtained by excluding all other fixed points.
Source: Dold finite localization (1.5), pp.1–2. The removed set is finite, hence closed
in a T1 space. No radius, compact closure or invariant-domain assumption is introduced. -/
def finiteFixedPointOpenDomain {X : Type u} [TopologicalSpace X] [T1Space X]
    (f : C(X, X)) (hfinite : {y : X | f y = y}.Finite) (x : X) : Opens X :=
  ⟨finiteLocalDomain f x, (hfinite.sdiff).isClosed.isOpen_compl⟩

/-- The original map on its canonical isolating domain, not an extension or new witness. -/
def finiteFixedPointLocalMap {X : Type u} [TopologicalSpace X] [T1Space X]
    (f : C(X, X)) (hfinite : {y : X | f y = y}.Finite) (x : X) :
    C(finiteFixedPointOpenDomain f hfinite x, X) :=
  f.comp ⟨Subtype.val, continuous_subtype_val⟩

/-- The source local integer computed by the canonical retracted displacement construction.
Source: Dold (1.3),(1.5),(2.3), pp.1–3. Compactness is a finite-set certificate;
the ENR theorem makes the retracted Euclidean map admissible and proves independence of
this isolating domain. No index data are supplied by the caller. -/
def finiteFixedPointLocalIndex {X : Type u} [TopologicalSpace X] [T1Space X]
    (e : ENRRepresentation X) (f : C(X, X))
    (hfinite : {y : X | f y = y}.Finite) (x : X) : ℤ :=
  enrLocalFixedPointIndex e (finiteFixedPointOpenDomain f hfinite x)
    (finiteFixedPointLocalMap f hfinite x) (by
      change IsCompact ((Subtype.val : finiteFixedPointOpenDomain f hfinite x → X) ⁻¹'
        {y : X | f y = y})
      exact (hfinite.preimage Subtype.val_injective.injOn).isCompact)

/-- The canonical domain isolates a marked fixed point of a map with finite fixed set.

Source: Dold (1.3), (1.5), pp.1–2, finite localization. The domain removes exactly
the other fixed points, so it contains the marked point and no other fixed point. -/
theorem finiteFixedPointOpenDomain_isolating
    {X : Type u} [TopologicalSpace X] [T1Space X]
    (f : C(X, X)) (hfinite : {y : X | f y = y}.Finite) (x : X) (hx : f x = x) :
    IsolatingNeighborhood f x (finiteFixedPointOpenDomain f hfinite x : Set X) := by
  refine ⟨(finiteFixedPointOpenDomain f hfinite x).isOpen, ?_, ?_⟩
  · simp [finiteFixedPointOpenDomain, finiteLocalDomain, hx]
  · intro y hy
    constructor
    · intro hfy
      by_contra hyx
      exact hy (by simp [hfy, hyx])
    · intro hyx
      simpa [hyx] using hx

/-- The fixed-point set inside the canonical local domain is exactly the
marked singleton. This is the set-level form of Dold's finite localization
used when decomposing the global index into local indices. -/
theorem finiteFixedPointOpenDomain_fixed_inter_eq_singleton
    {X : Type u} [TopologicalSpace X] [T1Space X]
    (f : C(X, X)) (hfinite : {y : X | f y = y}.Finite) (x : X) (hx : f x = x) :
    (finiteFixedPointOpenDomain f hfinite x : Set X) ∩ {y : X | f y = y} = {x} := by
  have hiso := finiteFixedPointOpenDomain_isolating f hfinite x hx
  ext y
  constructor
  · intro hy
    exact (hiso.2.2 y hy.1).mp hy.2
  · intro hy
    have hyx : y = x := by simpa using hy
    subst y
    exact ⟨hiso.2.1, hx⟩


end HolomorphicAnosov.FixedPointIndexInterface
