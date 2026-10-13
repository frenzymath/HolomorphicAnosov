import HolomorphicAnosov.Dynamics.Bowen.BowenBasicSetMarkovCoding
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PeriodicZpowRemainder
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.HomeomorphZpowEquiv
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.HomeomorphPowCoe
import Mathlib.Tactic

open Set Matrix
open scoped _root_.Topology BigOperators

namespace HolomorphicAnosov
open BowenBasicSetCoding

/-- Dense periodic points turn a dense two-sided orbit into forward topological
transitivity. Source: Bowen, Markov partitions for Axiom A diffeomorphisms
(1970), pp.740–742, symbolic transition construction; elementary orbit argument.
A dense integer orbit meets nonempty open U and V at times a and b. Thus
W=U∩F^{-(b-a)}(V) is nonempty open. Choose a periodic point y in W using
density of periodic points, with positive period r. Replacing b-a by its
nonnegative residue modulo r preserves F^{b-a}(y), so a nonnegative iterate
of a point of U belongs to V. No separation or Baire hypothesis is needed. -/
theorem forward_transitive_of_dense_integer_orbit_and_periodic
    {X : Type*} [TopologicalSpace X] (F : X ≃ₜ X) (x : X)
    (hx : Dense (Set.range (fun k : ℤ ↦ (F^k) x)))
    (hp : Dense (Function.periodicPts (F : X → X))) :
    ∀ U V : Set X, IsOpen U → U.Nonempty → IsOpen V → V.Nonempty →
      ∃ n : ℕ, (((F^n : X ≃ₜ X) : X → X) '' U ∩ V).Nonempty := by
  intro U V hU hUne hV hVne
  obtain ⟨_,ha,⟨a,rfl⟩⟩ := hx.inter_open_nonempty U hU hUne
  obtain ⟨_,hb,⟨b,rfl⟩⟩ := hx.inter_open_nonempty V hV hVne
  have hba : (F^(b-a)) ((F^a) x) = (F^b) x := by
    rw [← Homeomorph.mul_apply, ← _root_.zpow_add, sub_add_cancel]
  let W := U ∩ (F^(b-a)) ⁻¹' V
  have hW : IsOpen W := hU.inter ((F^(b-a)).continuous.isOpen_preimage _ hV)
  obtain ⟨y,⟨hyU,hyV⟩,hyp⟩ := hp.inter_open_nonempty W hW ⟨(F^a) x,ha,by simpa [hba] using hb⟩
  obtain ⟨r,hr,hyr⟩ := Function.mem_periodicPts.mp hyp
  let k := ((b-a) % (r:ℤ)).toNat
  have hz : (F^(b-a)) y = (F^k) y := by
    have hh := Dynamics.ManningOriginalBasicSetSignedTraceG7.periodic_zpow_remainder
      F.toEquiv hr hyr (b-a)
    have hcoe : (F^(b-a)) y = (F.toEquiv^(b-a)) y :=
      congrArg (fun g : Equiv.Perm X ↦ g y)
        (Dynamics.ManningOriginalBasicSetSignedTraceG7.CarrierAdapter.homeomorph_zpow_equiv F (b-a))
    rw [hcoe,hh]
    exact congrFun (Dynamics.ManningOriginalBasicSetSignedTraceG7.CarrierAdapter.homeomorph_pow_coe F k).symm y
  exact ⟨k,(F^k) y,⟨y,hyU,rfl⟩,hz ▸ hyV⟩

/-- A transitive homeomorphism has an irreducible transition matrix for a finite
proper partition. Source: Bowen (1970), pp.740–742, symbolic transition
construction; the boundary-avoidance argument is expanded here. The finite
union Y of partition interiors is open and dense: finite closure commutes
with their union, regular closedness identifies each closure with its cell,
and the cells cover X. Baire makes Z=⋂_{k≥0}F^{-k}(Y) dense. Every cell has
nonempty interior by regular closedness and nonemptiness. For cells i,j,
apply forward transitivity to int(R_i) and F^{-1}(int(R_j)), obtaining a
nonempty open transition of positive length m+1. Choose z from that open
set intersect Z. Its iterates have interior labels a(k); disjoint interiors
force a(0)=i and a(m+1)=j. Each adjacent label is a witnessed transition,
so its matrix entry is one. Induction in the matrix multiplication formula
bounds the corresponding power entry below by the positive path product;
all remaining terms are nonnegative. Thus some positive power connects
each ordered pair of indices, which is Mathlib's irreducibility criterion.
For an empty index type the conclusion is vacuous; nonempty cells in all
other cases ensure the open sets used above are nonempty. -/
theorem transitive_partition_irreducible
    {X : Type*} [TopologicalSpace X] [BaireSpace X]
    (F : X ≃ₜ X) {N : ℕ} (R : Fin N → Set X)
    [DecidableRel (transition F R)]
    (hne : ∀ i, (R i).Nonempty) (hproper : ∀ i, R i = closure (interior (R i)))
    (hcover : (⋃ i, R i) = univ)
    (hdisj : ∀ i j, i ≠ j → Disjoint (interior (R i)) (interior (R j)))
    (htrans : ∀ U V : Set X, IsOpen U → U.Nonempty → IsOpen V → V.Nonempty →
      ∃ n : ℕ, (((F^n : X ≃ₜ X) : X → X) '' U ∩ V).Nonempty) :
    (Matrix.of (fun i j ↦ if transition F R i j then (1:ℝ) else 0)).IsIrreducible := by
  classical
  let A : Matrix (Fin N) (Fin N) ℝ := Matrix.of (fun i j ↦ if transition F R i j then (1:ℝ) else 0)
  have hA : ∀ i j, 0 ≤ A i j := by intro i j; dsimp [A]; split_ifs <;> norm_num
  apply (Matrix.isIrreducible_iff_exists_pow_pos hA).mpr
  let Y := ⋃ i, interior (R i)
  have hYopen : IsOpen Y := isOpen_iUnion fun i ↦ isOpen_interior
  have hYdense : Dense Y := by
    rw [dense_iff_closure_eq]
    change closure (⋃ i, interior (R i)) = univ
    rw [closure_iUnion_of_finite]
    simpa only [← hproper] using hcover
  let Z := ⋂ k : ℕ, (F^k) ⁻¹' Y
  have hZdense : Dense Z := dense_iInter_of_isOpen
    (fun k ↦ (F^k).continuous.isOpen_preimage Y hYopen)
    (fun k ↦ hYdense.preimage (F^k).isOpenMap)
  have hint (i) : (interior (R i)).Nonempty := by
    by_contra h
    have hh : R i = ∅ := by rw [hproper, Set.not_nonempty_iff_eq_empty.mp h, closure_empty]
    simpa only [hh, Set.not_nonempty_empty] using hne i
  intro i j
  have hv : (F ⁻¹' interior (R j)).Nonempty := F.surjective.nonempty_preimage.mpr (hint j)
  obtain ⟨m,y,⟨x,hxi,rfl⟩,hyj⟩ := htrans (interior (R i)) (F ⁻¹' interior (R j))
    isOpen_interior (hint i) (F.continuous.isOpen_preimage _ isOpen_interior) hv
  have hxj : (F^(m+1)) x ∈ interior (R j) := by
    simpa only [pow_succ', Homeomorph.mul_apply, Set.mem_preimage] using hyj
  let W := interior (R i) ∩ (F^(m+1)) ⁻¹' interior (R j)
  have hWopen : IsOpen W := isOpen_interior.inter ((F^(m+1)).continuous.isOpen_preimage _ isOpen_interior)
  obtain ⟨z,⟨hzi,hzj⟩,hz⟩ := hZdense.inter_open_nonempty W hWopen ⟨x,hxi,hxj⟩
  have hlabels (k : ℕ) : ∃ a, (F^k) z ∈ interior (R a) := mem_iUnion.mp (mem_iInter.mp hz k)
  choose a ha using hlabels
  have hunique {p q : Fin N} {x : X} (hp : x ∈ interior (R p))
      (hq : x ∈ interior (R q)) : p=q := by
    by_contra h
    exact Set.disjoint_left.mp (hdisj p q h) hp hq
  have ha0 : a 0 = i := hunique (by simpa using ha 0) hzi
  have ham : a (m+1) = j := hunique (ha (m+1)) hzj
  have hedge (k : ℕ) : A (a k) (a (k+1)) = 1 := by
    have ht : transition F R (a k) (a (k+1)) := by
      refine ⟨F ((F^k) z), ⟨(F^k) z,ha k,rfl⟩,?_⟩
      simpa only [pow_succ',Homeomorph.mul_apply] using ha (k+1)
    simp [A,ht]
  have hpath (k : ℕ) : 0 < (A^k) (a 0) (a k) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ,Matrix.mul_apply]
      have hterm : 0 < (A^k) (a 0) (a k) * A (a k) (a (k+1)) := by rw [hedge,mul_one]; exact ih
      exact hterm.trans_le (Finset.single_le_sum
        (fun l _ ↦ mul_nonneg (Matrix.pow_apply_nonneg hA k _ l) (hA l _)) (Finset.mem_univ (a k)))
  exact ⟨m+1,by omega,by simpa only [ha0,ham] using hpath (m+1)⟩

end HolomorphicAnosov


