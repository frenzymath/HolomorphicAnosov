import HolomorphicAnosov.Topology.FiniteFixedPointDomains

/-!
# Disjoint canonical neighborhoods of a finite fixed set

Source: Dold (1965), (1.5), pp.1–2. Finite Hausdorff separation gives disjoint
open neighborhoods, each restricted to its canonical isolating domain.
-/

noncomputable section
open TopologicalSpace
namespace HolomorphicAnosov.FixedPointIndexInterface
universe u

/--
Finite fixed points admit a `Fin`-indexed pairwise-disjoint open family, each member
contained in the corresponding canonical isolating domain.  This is the constructive
Dold (1.5), pp.1–2, neighborhood-selection step: `Set.Finite.t2_separation` separates the
finite fixed set, and intersecting with `finiteFixedPointOpenDomain` preserves openness,
disjointness, and fixed-point coverage.
-/
theorem finite_fixed_set_disjoint_canonical_domains
    {X : Type u} [TopologicalSpace X] [MetrizableSpace X]
    (f : C(X, X)) (hfinite : {y : X | f y = y}.Finite) :
    ∃ (k : ℕ) (V : Fin k → Opens X) (x₀ : Fin k → X),
      (∀ i, x₀ i ∈ V i) ∧
      Function.Injective x₀ ∧
      Set.range x₀ = {x : X | f x = x} ∧
      (∀ i, f (x₀ i) = x₀ i) ∧
      (∀ i, V i ≤ (⊤ : Opens X)) ∧
      (∀ i, V i ≤ finiteFixedPointOpenDomain f hfinite (x₀ i)) ∧
      Pairwise (fun i j ↦ Disjoint (V i : Set X) (V j : Set X)) ∧
      (∀ x : (⊤ : Opens X),
        (f.comp ⟨Subtype.val, continuous_subtype_val⟩) x = x.1 →
          ∃ i, x.1 ∈ V i) := by
  let K : Type u := {x : X // f x = x}
  let : Finite K := hfinite.to_subtype
  let eK : K ≃ Fin (Nat.card K) := Finite.equivFin K
  let U : X → Set X := Classical.choose (hfinite.t2_separation)
  have hU : ∀ x, x ∈ U x ∧ IsOpen (U x) :=
    (Classical.choose_spec (hfinite.t2_separation)).1
  have hp : ({y : X | f y = y}).PairwiseDisjoint U :=
    (Classical.choose_spec (hfinite.t2_separation)).2
  let x₀ : Fin (Nat.card K) → X := fun i ↦ (eK.symm i).val
  let V : Fin (Nat.card K) → Opens X := fun i ↦
    ⟨U (x₀ i) ∩ (finiteFixedPointOpenDomain f hfinite (x₀ i) : Set X),
      (hU _).2.inter (finiteFixedPointOpenDomain f hfinite _).isOpen⟩
  have hx₀ : ∀ i, f (x₀ i) = x₀ i := by
    intro i
    exact (eK.symm i).property
  have hmarked : ∀ i, x₀ i ∈ V i := by
    intro i
    refine ⟨(hU _).1, ?_⟩
    simp [finiteFixedPointOpenDomain, finiteLocalDomain]
  have hinj : Function.Injective x₀ := by
    intro i j hij
    exact eK.symm.injective (Subtype.ext hij)
  have hrange : Set.range x₀ = {x : X | f x = x} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact hx₀ i
    · intro hx
      exact ⟨eK ⟨x, hx⟩, by simp [x₀]⟩
  have htop : ∀ i, V i ≤ (⊤ : Opens X) := fun _ ↦ le_top
  have hdom : ∀ i, V i ≤ finiteFixedPointOpenDomain f hfinite (x₀ i) := by
    intro i z hz
    exact hz.2
  have hpair : Pairwise (fun i j ↦ Disjoint (V i : Set X) (V j : Set X)) := by
    intro i j hij
    have hi : x₀ i ∈ ({y : X | f y = y} : Set X) := hx₀ i
    have hj : x₀ j ∈ ({y : X | f y = y} : Set X) := hx₀ j
    have hne : x₀ i ≠ x₀ j := by
      intro heq
      apply hij
      simpa using congrArg eK (Subtype.ext heq)
    exact (hp hi hj hne).mono Set.inter_subset_left Set.inter_subset_left
  have hcover : ∀ x : (⊤ : Opens X),
      (f.comp ⟨Subtype.val, continuous_subtype_val⟩) x = x.1 →
        ∃ i, x.1 ∈ V i := by
    intro x hx
    let xk : K := ⟨x.1, by simpa using hx⟩
    have hmem : x.1 ∈ U x.1 ∩
        (finiteFixedPointOpenDomain f hfinite x.1 : Set X) := by
      refine ⟨(hU x.1).1, ?_⟩
      simp [finiteFixedPointOpenDomain, finiteLocalDomain]
    refine ⟨eK xk, ?_⟩
    simpa [V, x₀] using hmem
  exact ⟨Nat.card K, V, x₀, hmarked, hinj, hrange, hx₀, htop, hdom, hpair, hcover⟩


end HolomorphicAnosov.FixedPointIndexInterface
