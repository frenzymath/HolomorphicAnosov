import HolomorphicAnosov.Topology.GoodPairCollapse
import HolomorphicAnosov.Topology.Homotopy.StrongDeformationRetract
import Mathlib.Topology.Homotopy.Contractible

/-! Descent of a strong deformation retraction to a collapse quotient. -/

noncomputable section

open Set unitInterval
open HolomorphicAnosov.Topology.Homotopy

namespace HolomorphicAnosov.GoodPair

universe u
variable {X : Type u} [TopologicalSpace X]

/-- The intrinsic collapse of the copy of A inside the original subspace V. (Hatcher) -/
abbrev NeighborhoodCollapsed (A V : Set X) := Collapsed {x : V | x.val ∈ A}

namespace StrongDeformationRetract

variable {A V : Set X} {hAV : A ⊆ V}

/-- Well-definedness of the representative map at each time. (Hatcher) -/
theorem quotientHomotopy_respects
    (D : HolomorphicAnosov.Topology.Homotopy.StrongDeformationRetract A V hAV)
    (t : I) (x y : V)
    (hxy : (collapseSetoid {v : V | v.val ∈ A}).r x y) :
    collapse {v : V | v.val ∈ A} (D.homotopy (t, x)) =
      collapse {v : V | v.val ∈ A} (D.homotopy (t, y)) := by
  rcases hxy with hxy | ⟨hx, hy⟩
  · subst y
    rfl
  · apply Quotient.eq.mpr
    right
    constructor
    · rw [D.homotopy.eq_fst t hx]
      exact hx
    · rw [D.homotopy.eq_fst t hy]
      exact hy

/-- The descended value [x]↦[H(t,x)], defined by Quotient.lift. (Hatcher) -/
def quotientHomotopyValue
    (D : HolomorphicAnosov.Topology.Homotopy.StrongDeformationRetract A V hAV)
    (t : I) : NeighborhoodCollapsed A V → NeighborhoodCollapsed A V :=
  Quotient.lift
    (fun x : V ↦ collapse {v : V | v.val ∈ A} (D.homotopy (t, x)))
    ((quotientHomotopy_respects D) t)

/-- Joint continuity of the quotient lift, including the collapsed part. (Hatcher) -/
theorem continuous_quotientHomotopyValue
    (D : HolomorphicAnosov.Topology.Homotopy.StrongDeformationRetract A V hAV) :
    Continuous (fun z : I × NeighborhoodCollapsed A V ↦
      (quotientHomotopyValue D) z.1 z.2) := by
  apply
    (isQuotientMap_quotient_mk' (s := collapseSetoid {v : V | v.val ∈ A})).continuous_lift_prod_right
  exact (collapse {v : V | v.val ∈ A}).continuous.comp D.homotopy.continuous

/-- The original zero endpoint, retraction endpoint, and relative fixed-set equations. (Hatcher) -/
theorem quotientHomotopy_laws
    (D : HolomorphicAnosov.Topology.Homotopy.StrongDeformationRetract A V hAV) :
    (∀ z : NeighborhoodCollapsed A V, (quotientHomotopyValue D) 0 z = z) ∧
    (∀ x : V,
      (quotientHomotopyValue D) 1 (collapse {v : V | v.val ∈ A} x) =
        collapse {v : V | v.val ∈ A}
          ((ContinuousMap.inclusion hAV) (D.retraction x))) ∧
    (∀ t : I, ∀ z ∈ collapsedPart {v : V | v.val ∈ A},
      (quotientHomotopyValue D) t z = z) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z
    induction z using Quotient.inductionOn with
    | h x =>
      change collapse _ (D.homotopy (0, x)) = collapse _ x
      rw [D.homotopy.apply_zero]
      rfl
  · intro x
    change collapse _ (D.homotopy (1, x)) = _
    rw [D.homotopy.apply_one]
    rfl
  · intro t z hz
    obtain ⟨x, hx, rfl⟩ := hz
    change collapse _ (D.homotopy (t, x)) = collapse _ x
    rw [D.homotopy.eq_fst t hx]
    rfl

/-- The time-one quotient map is continuous. (Hatcher) -/
def quotientEndpoint
    (D : HolomorphicAnosov.Topology.Homotopy.StrongDeformationRetract A V hAV) :
    C(NeighborhoodCollapsed A V, NeighborhoodCollapsed A V) :=
  ⟨(quotientHomotopyValue D) 1,
    (continuous_quotientHomotopyValue D).comp (continuous_const.prodMk continuous_id)⟩

/-- The relative quotient deformation before choosing any point of A. (Hatcher) -/
def quotientHomotopy
    (D : HolomorphicAnosov.Topology.Homotopy.StrongDeformationRetract A V hAV) :
    ContinuousMap.HomotopyRel (ContinuousMap.id (NeighborhoodCollapsed A V))
      (quotientEndpoint D) (collapsedPart {v : V | v.val ∈ A}) where
  toFun z := (quotientHomotopyValue D) z.1 z.2
  continuous_toFun := (continuous_quotientHomotopyValue D)
  map_zero_left := (quotientHomotopy_laws D).1
  map_one_left := fun _ ↦ rfl
  prop' := (quotientHomotopy_laws D).2.2

/-- Any supplied point of A identifies the time-one map with its constant quotient class. (Hatcher) -/
theorem quotientHomotopy_one
    (D : HolomorphicAnosov.Topology.Homotopy.StrongDeformationRetract A V hAV)
    (a : A) (z : NeighborhoodCollapsed A V) :
    (quotientHomotopyValue D) 1 z =
      collapse {v : V | v.val ∈ A} ((ContinuousMap.inclusion hAV) a) := by
  induction z using Quotient.inductionOn with
  | h x =>
    change quotientHomotopyValue D 1 (collapse _ x) = _
    rw [(quotientHomotopy_laws D).2.1]
    exact Quotient.eq.mpr (Or.inr ⟨(D.retraction x).property, a.property⟩)

/-- The relative contraction to the class of a supplied point of A. (Hatcher) -/
def quotientContraction
    (D : HolomorphicAnosov.Topology.Homotopy.StrongDeformationRetract A V hAV)
    (a : A) :
    ContinuousMap.HomotopyRel (ContinuousMap.id (NeighborhoodCollapsed A V))
      (ContinuousMap.const (NeighborhoodCollapsed A V)
        (collapse {v : V | v.val ∈ A} ((ContinuousMap.inclusion hAV) a)))
      (collapsedPart {v : V | v.val ∈ A}) where
  toFun z := (quotientHomotopyValue D) z.1 z.2
  continuous_toFun := (continuous_quotientHomotopyValue D)
  map_zero_left := (quotientHomotopy_laws D).1
  map_one_left := (quotientHomotopy_one D) a
  prop' := (quotientHomotopy_laws D).2.2

/-- A nonempty retract makes its intrinsic collapse contractible. (Hatcher) -/
theorem contractible_neighborhoodCollapsed
    (D : HolomorphicAnosov.Topology.Homotopy.StrongDeformationRetract A V hAV)
    (hA : A.Nonempty) : ContractibleSpace (NeighborhoodCollapsed A V) := by
  obtain ⟨a, ha⟩ := hA
  apply (contractible_iff_id_nullhomotopic (NeighborhoodCollapsed A V)).mpr
  exact ⟨collapse _ ((ContinuousMap.inclusion hAV) ⟨a, ha⟩),
    ⟨(quotientContraction D ⟨a, ha⟩).toHomotopy⟩⟩

/-- If A is empty, the supplied retraction forces V and its quotient empty. (Hatcher) -/
theorem isEmpty_neighborhoodCollapsed
    (D : HolomorphicAnosov.Topology.Homotopy.StrongDeformationRetract A V hAV)
    (hA : ¬ A.Nonempty) : IsEmpty (NeighborhoodCollapsed A V) := by
  constructor
  intro z
  induction z using Quotient.inductionOn with
  | h x => exact hA ⟨D.retraction x, (D.retraction x).property⟩

end StrongDeformationRetract
end HolomorphicAnosov.GoodPair
