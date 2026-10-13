import HolomorphicAnosov.Topology.Homotopy.MappingTelescopeSequence
import Mathlib.Topology.Homotopy.Equiv

/-!
# Removing the first cylinder of a mapping telescope

Source: Hatcher, *Algebraic Topology*, proof of Proposition A.11, p.528,
fact (2). The telescope retains the ordinary quotient topology.
-/

universe u
namespace HolomorphicAnosov.MappingTelescope.Sequence
open Set ContinuousMap

/-- Deleting the first level and cylinder preserves the homotopy type of an
ordinary mapping telescope.

Source: Hatcher, Proposition A.11 proof, p.528, fact (2).

Proof: Include the tail cylinders by shifting their labels. Collapse the first
cylinder to its top, namely the bottom of the first tail cylinder, and fix every
tail cylinder. Both formulas respect the generated seams and descend continuously.
The retraction after inclusion is the identity. On the first cylinder the map
`(v,x,t) ↦ [0,x,max t v]` and on the tail the identity give a homotopy from the
identity to inclusion after retraction, fixed on the tail. Currying into continuous
maps from the compact interval permits quotient descent; continuous evaluation
then gives joint continuity. No injectivity, separation or nonemptiness is used. -/
theorem mapping_telescope_tail_homotopy_equiv
    (X : ℕ → Type u) [∀ n, TopologicalSpace (X n)]
    (f : ∀ n, C(X n, X (n + 1))) :
    Nonempty (telescope f ≃ₕ
      telescope (X := fun n ↦ X (n + 1)) (fun n ↦ f (n + 1))) := by
  let ft : ∀ n, C(X (n + 1), X ((n + 1) + 1)) := fun n ↦ f (n + 1)
  let iraw : C(Cylinder (fun n ↦ X (n + 1)), telescope f) :=
    ⟨fun z ↦ cylinder f (z.1 + 1) z.2,
      continuous_sigma fun n ↦ (cylinder f (n + 1)).continuous⟩
  have hi : ∀ a b, setoid ft a b → iraw a = iraw b := by
    intro a b hab
    induction hab with
    | rel a b hab =>
      rcases hab with ⟨n, x, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact levelTop_eq f (n + 1) x
      · exact (levelTop_eq f (n + 1) x).symm
    | refl => rfl
    | symm _ _ _ h => exact h.symm
    | trans _ _ _ _ _ h k => exact h.trans k
  let i : C(telescope ft, telescope f) :=
    ⟨Quotient.lift iraw hi, iraw.continuous.quotient_lift hi⟩
  let rraw : C(Cylinder X, telescope ft) :=
    ⟨fun z ↦ match z with
      | ⟨0, x, t⟩ => level ft 0 (f 0 x)
      | ⟨n + 1, x, t⟩ => cylinder ft n (x, t),
     continuous_sigma fun n ↦ by
       cases n with
       | zero => exact ((level ft 0).continuous.comp (f 0).continuous).comp continuous_fst
       | succ n => exact (cylinder ft n).continuous⟩
  have hr : ∀ a b, setoid f a b → rraw a = rraw b := by
    intro a b hab
    induction hab with
    | rel a b hab =>
      rcases hab with ⟨n, x, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · cases n with
        | zero => rfl
        | succ n => exact levelTop_eq ft n x
      · cases n with
        | zero => rfl
        | succ n => exact (levelTop_eq ft n x).symm
    | refl => rfl
    | symm _ _ _ h => exact h.symm
    | trans _ _ _ _ _ h k => exact h.trans k
  let r : C(telescope f, telescope ft) :=
    ⟨Quotient.lift rraw hr, rraw.continuous.quotient_lift hr⟩
  have hri : r.comp i = ContinuousMap.id _ := by
    ext q
    induction q using Quotient.inductionOn with
    | h z => rfl
  let kraw : C(Cylinder X, C(unitInterval, telescope f)) :=
    ⟨fun z ↦ match z with
      | ⟨0, x, t⟩ =>
        ⟨fun v ↦ cylinder f 0 (x, max t v),
          (cylinder f 0).continuous.comp
            (continuous_const.prodMk (continuous_const.max continuous_id))⟩
      | ⟨n + 1, x, t⟩ => ContinuousMap.const _ (cylinder f (n + 1) (x, t)),
     continuous_sigma fun n ↦ by
       cases n with
       | zero =>
         apply ContinuousMap.continuous_of_continuous_uncurry
         exact (cylinder f 0).continuous.comp
           ((continuous_fst.fst).prodMk ((continuous_fst.snd).max continuous_snd))
       | succ n =>
         apply ContinuousMap.continuous_of_continuous_uncurry
         exact (cylinder f (n + 1)).continuous.comp continuous_fst⟩
  have hk : ∀ a b, setoid f a b → kraw a = kraw b := by
    intro a b hab
    induction hab with
    | rel a b hab =>
      rcases hab with ⟨n, x, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · ext v
        cases n with
        | zero => simpa [kraw, levelTop, level, max_eq_left (show v ≤ 1 from v.prop.2)] using
            levelTop_eq f 0 x
        | succ n => exact levelTop_eq f (n + 1) x
      · ext v
        cases n with
        | zero => simpa [kraw, levelTop, level, max_eq_left (show v ≤ 1 from v.prop.2)] using
            (levelTop_eq f 0 x).symm
        | succ n => exact (levelTop_eq f (n + 1) x).symm
    | refl => rfl
    | symm _ _ _ h => exact h.symm
    | trans _ _ _ _ _ h k => exact h.trans k
  let k : C(telescope f, C(unitInterval, telescope f)) :=
    ⟨Quotient.lift kraw hk, kraw.continuous.quotient_lift hk⟩
  have hK : (ContinuousMap.id (telescope f)).Homotopic (i.comp r) := by
    refine ⟨{ toFun := fun p ↦ k p.2 p.1
              continuous_toFun := k.uncurry.continuous.comp continuous_swap
              map_zero_left := ?_
              map_one_left := ?_ }⟩
    · intro q
      induction q using Quotient.inductionOn with
      | h z =>
        rcases z with ⟨n, x, t⟩
        cases n with
        | zero =>
          change cylinder f 0 (x, max t 0) = cylinder f 0 (x, t)
          rw [max_eq_left (show (0 : unitInterval) ≤ t from t.prop.1)]
        | succ n => rfl
    · intro q
      induction q using Quotient.inductionOn with
      | h z =>
        rcases z with ⟨n, x, t⟩
        cases n with
        | zero =>
          change cylinder f 0 (x, max t 1) = cylinder f 1 (f 0 x, 0)
          rw [max_eq_right (show t ≤ (1 : unitInterval) from t.prop.2)]
          exact levelTop_eq f 0 x
        | succ n => rfl
  exact ⟨{ toFun := r, invFun := i, left_inv := hK.symm, right_inv := by rw [hri] }⟩

end HolomorphicAnosov.MappingTelescope.Sequence

