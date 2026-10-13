import HolomorphicAnosov.Topology.GallierXuSurfacePresentation
import Mathlib.Topology.Homeomorph.Quotient

noncomputable section
open Set Topology _root_.Topology
namespace HolomorphicAnosov.Topology.GallierXu

/-- Bijective renaming and reversal of edge coordinates is realized by a
parameter-preserving homeomorphism. Face enumeration may change, while the
cyclic starting positions are held fixed.

Source: Gallier–Xu, Definitions 6.1–6.3, pp.79–86: edge labels and their
chosen directions are coordinates, and the same interval points are glued.
Map each original face disk identically to its newly enumerated face disk.
If an edge direction is reversed, replace its parameter t by 1-t. The two
sign reversals cancel in the side-point formula. A bijection of labels
preserves and reflects equality of labels, hence the generated quotient
relations. Quotient descent gives inverse continuous maps. The same
side-point calculation proves the exact surviving-parameter conclusion.
-/
theorem labelRenaming_realized {P Q : Presentation} (e : ℕ ≃ ℕ) (flip : ℕ → Bool)
    (f : Fin P.length ≃ Fin Q.length)
    (h : ∀ k, ((P.get k).map fun a ↦ (e a.1, if flip a.1 then !a.2 else a.2)) =
      Q.get (f k)) :
    ∃ H : Realization P ≃ₜ Realization Q,
      RespectsParameters
        (.rename e flip f (fun k ↦ (h k) ▸ List.IsRotated.refl _)) H ∧
      ∀ a, H '' edgeImage P a = edgeImage Q (e a) := by
  classical
  have hlen (k : Fin P.length) : (P.get k).length = (Q.get (f k)).length := by
    rw [← h k]
    exact (List.length_map ..).symm
  let pos (k : Fin P.length) : Fin (P.get k).length ≃ Fin (Q.get (f k)).length :=
    finCongr (hlen k)
  have hget (k : Fin P.length) (j : Fin (P.get k).length) :
      (Q.get (f k)).get (pos k j) =
        (e ((P.get k).get j).1,
          if flip ((P.get k).get j).1 then !((P.get k).get j).2
          else ((P.get k).get j).2) := by
    have hj : j.val < (Q.get (f k)).length := by rw [← hlen]; exact j.isLt
    have hh := congrArg (fun w : Word ↦ w[j.val]?) (h k)
    simp only [List.getElem?_map, List.getElem?_eq_getElem j.isLt,
      List.getElem?_eq_getElem hj, Option.map_some] at hh
    exact Option.some.inj hh.symm
  have hside (k : Fin P.length) (j : Fin (P.get k).length) (t : ℝ) :
      sidePoint Q (f k) (pos k j)
        (if flip ((P.get k).get j).1 then 1 - t else t) = sidePoint P k j t := by
    dsimp only [sidePoint]
    rw [hget]
    simp only [pos, finCongr_apply, Fin.val_cast]
    rw [← hlen]
    cases flip ((P.get k).get j).1 <;>
      cases ((P.get k).get j).2 <;> simp
  let rev (b : Bool) (t : ℝ) : ℝ := if b then 1 - t else t
  have rev_rev (b : Bool) (t : ℝ) : rev b (rev b t) = t := by
    cases b <;> simp [rev]
  have rev_mem (b : Bool) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
      rev b t ∈ Icc (0 : ℝ) 1 := by
    cases b
    · exact ht
    · dsimp [rev]
      constructor <;> linarith [ht.1, ht.2]
  have hpoint (k : Fin P.length) (j : Fin (P.get k).length) (s : ℝ) :
      sidePoint Q (f k) (pos k j) s =
        sidePoint P k j (rev (flip ((P.get k).get j).1) s) := by
    have hh := hside k j (rev (flip ((P.get k).get j).1) s)
    change sidePoint Q (f k) (pos k j)
      (rev (flip ((P.get k).get j).1) (rev (flip ((P.get k).get j).1) s)) = _ at hh
    simpa only [rev_rev] using hh
  let F : FaceDisks P ≃ₜ FaceDisks Q :=
    (f.toHomeomorphOfDiscrete).prodCongr (Homeomorph.refl Disk)
  have edge_iff (x y : FaceDisks P) :
      edgeIdentification P x y ↔ edgeIdentification Q (F x) (F y) := by
    constructor
    · rintro ⟨j, k, t, ht, hl, hx, hy⟩
      refine ⟨pos x.1 j, pos y.1 k, rev (flip ((P.get x.1).get j).1) t,
        rev_mem _ ht, ?_, ?_, ?_⟩
      · change ((Q.get (f x.1)).get (pos x.1 j)).1 =
          ((Q.get (f y.1)).get (pos y.1 k)).1
        simp only [hget]
        exact congrArg e hl
      · change (x.2 : ℂ) = sidePoint Q (f x.1) (pos x.1 j) _
        rw [hside]
        exact hx
      · change (y.2 : ℂ) = sidePoint Q (f y.1) (pos y.1 k) _
        rw [hl]
        rw [hside]
        exact hy
    · intro hxy
      change edgeIdentification Q (f x.1, x.2) (f y.1, y.2) at hxy
      rcases hxy with ⟨j, k, s, hs, hl, hx, hy⟩
      obtain ⟨j, rfl⟩ := (pos x.1).surjective j
      obtain ⟨k, rfl⟩ := (pos y.1).surjective k
      have hl' : ((P.get x.1).get j).1 = ((P.get y.1).get k).1 := by
        apply e.injective
        simpa only [hget] using hl
      refine ⟨j, k, rev (flip ((P.get x.1).get j).1) s, rev_mem _ hs, hl', ?_, ?_⟩
      · rw [hpoint] at hx
        exact hx
      · rw [hpoint] at hy
        rw [hl']
        exact hy
  have relation_iff (x y : FaceDisks P) :
      Relation.EqvGen (edgeIdentification P) x y ↔
        Relation.EqvGen (edgeIdentification Q) (F x) (F y) := by
    constructor
    · intro hxy
      induction hxy with
      | rel x y hxy => exact .rel _ _ ((edge_iff x y).mp hxy)
      | refl x => exact .refl _
      | symm _ _ _ h => exact h.symm
      | trans _ _ _ _ _ h k => exact .trans _ _ _ h k
    · intro hxy
      have hh : ∀ a b, Relation.EqvGen (edgeIdentification Q) a b →
          Relation.EqvGen (edgeIdentification P) (F.symm a) (F.symm b) := by
        intro a b hab
        induction hab with
        | rel a b hab =>
          apply Relation.EqvGen.rel
          apply (edge_iff _ _).mpr
          simpa only [F.apply_symm_apply] using hab
        | refl a => exact .refl _
        | symm _ _ _ h => exact h.symm
        | trans _ _ _ _ _ h k => exact .trans _ _ _ h k
      simpa only [F.symm_apply_apply] using hh _ _ hxy
  let H : Realization P ≃ₜ Realization Q := Homeomorph.Quotient.congr F relation_iff
  refine ⟨H, ?_, ?_⟩
  · intro x y j k t s ht hs hparam hx hy
    change e ((P.get x.1).get j).1 = ((Q.get y.1).get k).1 ∧
      s = rev (flip ((P.get x.1).get j).1) t at hparam
    change project Q (F x) = project Q y
    apply Quotient.sound
    apply Relation.EqvGen.rel
    refine ⟨pos x.1 j, k, s, hs, ?_, ?_, hy⟩
    · change ((Q.get (f x.1)).get (pos x.1 j)).1 = _
      simpa only [hget] using hparam.1
    · change (x.2 : ℂ) = sidePoint Q (f x.1) (pos x.1 j) s
      rw [hparam.2, hside]
      exact hx
  
  · intro a
    ext q
    constructor
    · rintro ⟨p, ⟨x, j, t, ht, ha, hx, hp⟩, rfl⟩
      rw [← hp]
      refine ⟨F x, pos x.1 j, rev (flip ((P.get x.1).get j).1) t,
        rev_mem _ ht, ?_, ?_, rfl⟩
      · change ((Q.get (f x.1)).get (pos x.1 j)).1 = e a
        simp only [hget]
        exact congrArg e ha
      · change (x.2 : ℂ) = sidePoint Q (f x.1) (pos x.1 j) _
        rw [hside]
        exact hx
    · rintro ⟨⟨k, z⟩, j, t, ht, ha, hz, hq⟩
      obtain ⟨k, rfl⟩ := f.surjective k
      obtain ⟨j, rfl⟩ := (pos k).surjective j
      have ha' : ((P.get k).get j).1 = a := by
        apply e.injective
        simpa only [hget] using ha
      refine ⟨project P (k, z), ?_, ?_⟩
      · refine ⟨(k, z), j, rev (flip ((P.get k).get j).1) t,
          rev_mem _ ht, ha', ?_, rfl⟩
        rw [hpoint] at hz
        exact hz
      · exact hq

end HolomorphicAnosov.Topology.GallierXu

