import HolomorphicAnosov.Topology.Homotopy.MappingTelescopeHomotopyComparisons
import Mathlib.Topology.Category.TopCat.Basic

/-!
# Domination telescope comparison

Source: Hatcher, *Algebraic Topology*, Proposition A.11, pp.528–529. Form the
alternating sequence P,M,P,M,…, compare it with its tail, and pair the two
sequences. This gives Tel(j ∘ q) ≃ Tel(q ∘ j); the supplied homotopy then
identifies the latter with the identity telescope and hence with M.

Bundled topological spaces keep the dependent topology transports explicit.
Universe lifts put the two spaces in one sequence; lifting cylinder coordinates
induces a homeomorphism of the genuine quotient telescopes, so the conclusion
uses the original unlifted carrier.
-/

namespace HolomorphicAnosov

open ContinuousMap MappingTelescope.Sequence
universe u v

/-- Transport of composition across equal bundled spaces. Proof: eliminate the three space
equalities and the map equalities, then use reflexivity. -/
private theorem comp_heq {A B C A' B' C' : TopCat.{u}}
  (ha : A = A') (hb : B = B') (hc : C = C')
  (f : C(B,C)) (g : C(A,B)) (f' : C(B',C')) (g' : C(A',B'))
  (hf : HEq f f') (hg : HEq g g') : HEq (f.comp g) (f'.comp g') := by
  cases ha; cases hb; cases hc
  cases hf; cases hg
  rfl
/-- Transport a sequence telescope across equality of the bundled family. Proof: eliminate
the family equality and apply function extensionality to the bonding maps. -/
private theorem telescope_congr {X Y : ℕ → TopCat.{u}} (h : X = Y)
  (f : ∀ n, C(X n, X (n+1))) (g : ∀ n, C(Y n, Y (n+1)))
  (hf : ∀ n, HEq (f n) (g n)) :
  Nonempty (telescope f ≃ₕ telescope g) := by
  cases h
  have he : f = g := funext fun n => eq_of_heq (hf n)
  subst g
  exact ⟨HomotopyEquiv.refl _⟩


namespace DominationTelescopeTransport
variable {P : Type u} [TopologicalSpace P]
/-- Universe lifting of the self-map, with the induced topology. -/
private def liftBond (g : C(P,P)) : C(ULift.{v} P, ULift.{v} P) :=
  ⟨fun x => ULift.up (g x.down), continuous_uliftUp.comp (g.continuous.comp continuous_uliftDown)⟩
/-- Lift the space coordinate in each labelled cylinder; the inverse lowers it. -/
private def liftCylinder : Cylinder (fun _ : ℕ => P) ≃ₜ Cylinder (fun _ : ℕ => ULift.{v} P) where
  toFun a := ⟨a.1, (ULift.up a.2.1, a.2.2)⟩
  invFun a := ⟨a.1, (ULift.down a.2.1, a.2.2)⟩
  left_inv a := by cases a; rfl
  right_inv a := by cases a; rfl
  continuous_toFun := by
    apply continuous_sigma
    intro n
    exact continuous_sigmaMk.comp ((continuous_uliftUp.comp continuous_fst).prodMk continuous_snd)
  continuous_invFun := by
    apply continuous_sigma
    intro n
    exact continuous_sigmaMk.comp ((continuous_uliftDown.comp continuous_fst).prodMk continuous_snd)
/-- Lifting preserves the endpoint-generated relation. Proof: each seam lifts to the seam
with the lifted point. Induct on reflexivity, symmetry and transitivity in both directions. -/
private theorem liftRelation (g : C(P,P)) (a b : Cylinder (fun _ : ℕ => P)) :
    setoid (fun _ => g) a b ↔
    setoid (fun _ => liftBond.{u,v} g) (liftCylinder.{u,v} a) (liftCylinder.{u,v} b) := by
  constructor
  · intro h
    change Relation.EqvGen (edge (fun _ => g)) a b at h
    change Relation.EqvGen (edge (fun _ => liftBond.{u,v} g)) (liftCylinder a) (liftCylinder b)
    induction h with
    | refl => exact .refl _
    | symm a b h ih => exact .symm _ _ ih
    | trans a b c hab hbc ihab ihbc => exact .trans _ _ _ ihab ihbc
    | rel a b h =>
      rcases h with ⟨n, x, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact .rel _ _ ⟨n, ULift.up x, Or.inl ⟨rfl, rfl⟩⟩
      · exact .rel _ _ ⟨n, ULift.up x, Or.inr ⟨rfl, rfl⟩⟩
  · have back : ∀ (c d : Cylinder (fun _ : ℕ => ULift.{v} P)),
        Relation.EqvGen (edge (fun _ => liftBond.{u,v} g)) c d →
        Relation.EqvGen (edge (fun _ => g)) (liftCylinder.symm c) (liftCylinder.symm d) := by
      intro c d h
      induction h with
      | refl => exact .refl _
      | symm a b h ih => exact .symm _ _ ih
      | trans a b c hab hbc ihab ihbc => exact .trans _ _ _ ihab ihbc
      | rel a b h =>
        rcases h with ⟨n, x, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
        · exact .rel _ _ ⟨n, x.down, Or.inl ⟨rfl, rfl⟩⟩
        · exact .rel _ _ ⟨n, x.down, Or.inr ⟨rfl, rfl⟩⟩
    exact back _ _
/-- The cylinder lift descends to the actual quotient topologies. Source: Mathlib
`Homeomorph.Quotient.congr`; its relation hypothesis is proved by `liftRelation`. -/
private def liftTelescope (g : C(P,P)) : telescope (fun _ => g) ≃ₜ
    telescope (fun _ => liftBond.{u,v} g : ℕ → C(ULift.{v} P,ULift.{v} P)) :=
  Homeomorph.Quotient.congr liftCylinder (liftRelation g)
end DominationTelescopeTransport

/-- The telescope comparison for a factorization `M --j→ P --q→ M` with `q ∘ j ≃ id`.

Source: Hatcher, Proposition A.11, pp.528–529. Pairing the alternating sequence
and its tail gives the telescopes of `j ∘ q` and `q ∘ j`. Tail deletion compares
them. Apply the supplied homotopy to each bond of the second telescope and use
the identity telescope equivalence. The auxiliary universe lift is removed by
the cylinderwise quotient homeomorphism. No CW, injectivity, or nonemptiness
assumptions enter this argument. -/
theorem domination_telescope_homotopy_equiv
    (M : Type u) [TopologicalSpace M]
    (P : Type v) [TopologicalSpace P]
    (j : ContinuousMap M P) (q : ContinuousMap P M)
    (H : ContinuousMap.Homotopy (q.comp j) (ContinuousMap.id M)) :
    Nonempty (ContinuousMap.HomotopyEquiv
      (HolomorphicAnosov.MappingTelescope.Sequence.telescope
        (fun _ : ℕ ↦ j.comp q)) M) := by
  let jm : C(TopCat.of (ULift.{v} M), TopCat.of (ULift.{u} P)) := (ContinuousMap.uliftEquiv M P).symm j
  let qm : C(TopCat.of (ULift.{u} P), TopCat.of (ULift.{v} M)) := (ContinuousMap.uliftEquiv P M).symm q
  let X : ℕ → TopCat.{max u v} := fun n => if n % 2 = 0 then TopCat.of (ULift.{u} P) else TopCat.of (ULift.{v} M)
  let f : ∀ n, C((X n : Type (max u v)), (X (n+1) : Type (max u v))) := fun n => by
    by_cases h : n % 2 = 0
    · have hn : (n+1) % 2 ≠ 0 := by omega
      have e0 : X n = TopCat.of (ULift.{u} P) := by simp [X,h]
      have e1 : X (n+1) = TopCat.of (ULift.{v} M) := by simp [X,hn]
      rw [e0,e1]; exact qm
    · have hn : (n+1) % 2 = 0 := by omega
      have e0 : X n = TopCat.of (ULift.{v} M) := by simp [X,h]
      have e1 : X (n+1) = TopCat.of (ULift.{u} P) := by simp [X,hn]
      rw [e0,e1]; exact jm
  let : ∀ n, TopologicalSpace (X n : Type (max u v)) := fun n => (X n).str
  let H' : Homotopy (qm.comp jm) (ContinuousMap.id (TopCat.of (ULift.{v} M))) := {
    toFun := fun z => ULift.up (H (z.1, ULift.down z.2))
    continuous_toFun := continuous_uliftUp.comp (H.continuous.comp (continuous_fst.prodMk (continuous_uliftDown.comp continuous_snd)))
    map_zero_left := by intro z; apply ULift.ext; simp [jm, qm, ContinuousMap.uliftEquiv]
    map_one_left := by intro z; apply ULift.ext; simp }
  let Cmp := HolomorphicAnosov.MappingTelescope.Sequence.mapping_telescope_homotopy_comparisons (fun n => X n) f (TopCat.of (ULift.{v} M))
  have hXeven : (fun n => X (2*n) : ℕ → TopCat) = (fun _ => TopCat.of (ULift.{u} P)) := by funext n; simp [X]
  have hpaired := Cmp.2.2.1
  let g : ∀ n : ℕ, C(TopCat.of (ULift.{u} P), TopCat.of (ULift.{u} P)) := fun _ => jm.comp qm
  have pairComposite (n : ℕ) : HEq ((f (2*n+1)).comp (f (2*n))) (jm.comp qm) := by
    have he : (2*n) % 2 = 0 := by omega
    have ho : (2*n+1) % 2 ≠ 0 := by omega
    simp only [f, dite_eq_left he, dite_eq_right ho]
    apply comp_heq (show X (2*n) = TopCat.of (ULift.{u} P) by simp [X])
      (show X (2*n+1) = TopCat.of (ULift.{v} M) by simp [X, Nat.add_mod])
      (show X (2*n+1+1) = TopCat.of (ULift.{u} P) by simp [X, Nat.add_mod])
    · exact (cast_heq _ _).trans (cast_heq _ _)
    · exact (cast_heq _ _).trans (cast_heq _ _)
  have pairOriginal : Nonempty (HolomorphicAnosov.MappingTelescope.Sequence.telescope f ≃ₕ HolomorphicAnosov.MappingTelescope.Sequence.telescope (fun _ : ℕ => g 0)) := by
    let paired : ∀ n, C(X (2*n), X (2*(n+1))) := fun n =>
      Eq.mp (congrArg (fun m => C(X (2*n), X m)) (Nat.mul_succ 2 n).symm)
        ((f (2*n+1)).comp (f (2*n)))
    obtain ⟨e⟩ := hpaired
    obtain ⟨e'⟩ := telescope_congr hXeven paired (fun _ => g 0)
      (fun n => (cast_heq (congrArg (fun m => C(X (2*n), X m)) (Nat.mul_succ 2 n).symm) _).trans (pairComposite n))
    exact ⟨e.trans e'⟩
  let Xs : ℕ → TopCat.{max u v} := fun n => X (n+1)
  let fs : ∀ n, C((Xs n : Type (max u v)), (Xs (n+1) : Type (max u v))) := fun n => f (n+1)
  let : ∀ n, TopologicalSpace (Xs n : Type (max u v)) := fun n => (Xs n).str
  let CmpS := HolomorphicAnosov.MappingTelescope.Sequence.mapping_telescope_homotopy_comparisons (fun n => Xs n) fs (TopCat.of (ULift.{v} M))
  have hpairS := CmpS.2.2.1
  let gM : ∀ n : ℕ, C(TopCat.of (ULift.{v} M), TopCat.of (ULift.{v} M)) := fun _ => qm.comp jm
  have pairShifted : Nonempty (HolomorphicAnosov.MappingTelescope.Sequence.telescope fs ≃ₕ HolomorphicAnosov.MappingTelescope.Sequence.telescope gM) := by
    have hXe : (fun n => Xs (2*n)) = (fun _ => TopCat.of (ULift.{v} M)) := by
      funext n; simp [Xs, X, Nat.add_mod]
    have hp (n : ℕ) : HEq ((fs (2*n+1)).comp (fs (2*n))) (qm.comp jm) := by
      have he : (2*n+1+1) % 2 = 0 := by omega
      have ho : (2*n+1) % 2 ≠ 0 := by omega
      dsimp [fs]
      simp only [f, dite_eq_left he, dite_eq_right ho]
      apply comp_heq (show X (2*n+1) = TopCat.of (ULift.{v} M) by simp [X, Nat.add_mod])
        (show X (2*n+1+1) = TopCat.of (ULift.{u} P) by simp [X, Nat.add_mod])
        (show X (2*n+1+1+1) = TopCat.of (ULift.{v} M) by simp [X, Nat.add_mod])
      · exact (cast_heq _ _).trans (cast_heq _ _)
      · exact (cast_heq _ _).trans (cast_heq _ _)
    let paired : ∀ n, C(Xs (2*n), Xs (2*(n+1))) := fun n =>
      Eq.mp (congrArg (fun m => C(Xs (2*n), Xs m)) (Nat.mul_succ 2 n).symm)
        ((fs (2*n+1)).comp (fs (2*n)))
    obtain ⟨e⟩ := hpairS
    obtain ⟨e'⟩ := telescope_congr hXe paired gM
      (fun n => (cast_heq (congrArg (fun m => C(Xs (2*n), Xs m)) (Nat.mul_succ 2 n).symm) _).trans (hp n))
    exact ⟨e.trans e'⟩
  let Xm : ℕ → Type (max u v) := fun _ => ULift.{v} M
  let fm : ∀ n, C(Xm n, Xm (n+1)) := fun _ => qm.comp jm
  let gm : ∀ n, C(Xm n, Xm (n+1)) := fun _ => ContinuousMap.id (ULift.{v} M)
  let CmpM := HolomorphicAnosov.MappingTelescope.Sequence.mapping_telescope_homotopy_comparisons Xm fm (TopCat.of (ULift.{v} M))
  have hidM : Nonempty (HolomorphicAnosov.MappingTelescope.Sequence.telescope fm ≃ₕ HolomorphicAnosov.MappingTelescope.Sequence.telescope gm) := by
    have hh : ∀ n, (fm n).Homotopic (gm n) := fun _ => ⟨H'⟩
    exact ⟨(CmpM.1 gm hh).choose⟩
  have hId : Nonempty (HolomorphicAnosov.MappingTelescope.Sequence.telescope gm ≃ₕ (TopCat.of (ULift.{v} M))) := CmpM.2.2.2.2
  obtain ⟨ep⟩ := pairOriginal
  obtain ⟨es⟩ := pairShifted
  obtain ⟨et⟩ := Cmp.2.1
  obtain ⟨em⟩ := hidM
  obtain ⟨ei⟩ := hId
  have result : Nonempty (telescope (fun _ : ℕ => g 0) ≃ₕ ULift.{v} M) :=
    ⟨ep.symm.trans (et.trans (es.trans (em.trans ei)))⟩
  obtain ⟨e⟩ := result
  let el : telescope (fun _ : ℕ => j.comp q) ≃ₜ telescope (fun _ : ℕ => g 0) :=
    DominationTelescopeTransport.liftTelescope.{v,u} (j.comp q)
  exact ⟨el.toHomotopyEquiv.trans (e.trans Homeomorph.ulift.toHomotopyEquiv)⟩

end HolomorphicAnosov

