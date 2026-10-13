import HolomorphicAnosov.Topology.Pi1SurjectiveLoopCriterion
import Mathlib.CategoryTheory.Limits.Shapes.Preorder.TransfiniteCompositionOfShape

/-! Finite categorical iteration of based fundamental-group surjectivity.
This is an agent-written bridge for the finite-iteration step in Hatcher
Proposition 1.26, p.51, using Mathlib’s native diagram and colimit structure. -/

open CategoryTheory
namespace HolomorphicAnosov
universe u

/-- Finite categorical composition preserves path connectedness and surjectivity
of the actual based fundamental-group maps, when every successor stage does.
Agent-written proof: induct over the finite diagram; use the initial isomorphism,
composition of loop maps, and the terminal-stage colimit isomorphism. -/
theorem finite_composition_pi1_surjective
    {X Y : TopCat.{u}} [PathConnectedSpace X] (f : X ⟶ Y) (m : ℕ)
    (c : TransfiniteCompositionOfShape (Fin (m + 1)) f)
    (hstep : ∀ j : Fin m, PathConnectedSpace (c.F.obj j.castSucc) →
      PathConnectedSpace (c.F.obj j.succ) ∧
        ∀ x : c.F.obj j.castSucc, Function.Surjective
          (FundamentalGroup.map (c.F.map (homOfLE j.castSucc_le_succ)).hom x)) :
    PathConnectedSpace Y ∧ ∀ x : X, Function.Surjective (FundamentalGroup.map f.hom x) := by
  have hiso : ∀ {X Y : TopCat.{u}} (e : X ≅ Y) (x : X),
    Function.Surjective (FundamentalGroup.map e.hom.hom x) := by
    intro X Y e x
    apply (pi1_surjective_iff_loop_homotopic _ _).mpr
    intro γ
    let h : e.inv (e.hom x) = x := by
      have := congrArg (fun f : X ⟶ X => f x) e.hom_inv_id
      simp
    refine ⟨(γ.map e.inv.hom.continuous).cast h.symm h.symm, ?_⟩
    have he : ((γ.map e.inv.hom.continuous).cast h.symm h.symm).map
        e.hom.hom.continuous = γ := by
      ext t
      exact congrArg (fun f : Y ⟶ Y => f (γ t)) e.inv_hom_id
    rw [he]
  have hcomp : ∀ {A B C : TopCat.{u}} (i : A ⟶ B) (j : B ⟶ C),
      (∀ x, Function.Surjective (FundamentalGroup.map i.hom x)) →
      (∀ y, Function.Surjective (FundamentalGroup.map j.hom y)) →
      ∀ x, Function.Surjective (FundamentalGroup.map (i ≫ j).hom x) := by
    intro A B C i j hi hj x z
    obtain ⟨b, rfl⟩ := hj (i x) z
    obtain ⟨a, rfl⟩ := hi x b
    exact ⟨a, Path.Homotopic.Quotient.map_comp⟩
  have hstage : ∀ j : Fin (m + 1), PathConnectedSpace (c.F.obj j) ∧
      ∀ x : X, Function.Surjective (FundamentalGroup.map
        (c.isoBot.inv ≫ c.F.map (homOfLE (show (0 : Fin (m+1)) ≤ j from Fin.zero_le j))).hom x) := by
    intro j
    induction j using Fin.induction with
    | zero =>
      constructor
      · exact (TopCat.homeoOfIso c.isoBot.symm).surjective.pathConnectedSpace
          (TopCat.homeoOfIso c.isoBot.symm).continuous
      · have he : c.isoBot.inv ≫ c.F.map (homOfLE (Fin.zero_le (0 : Fin (m+1)))) =
            c.isoBot.inv := by simp
        exact (congrArg (fun g : X ⟶ c.F.obj 0 => ∀ x,
          Function.Surjective (FundamentalGroup.map g.hom x)) he).mpr (hiso c.isoBot.symm)
    | succ j ih =>
      obtain ⟨hpc, hp⟩ := hstep j ih.1
      refine ⟨hpc, ?_⟩
      have h := hcomp (c.isoBot.inv ≫ c.F.map (homOfLE (Fin.zero_le j.castSucc)))
        (c.F.map (homOfLE j.castSucc_le_succ)) ih.2 hp
      have he : (c.isoBot.inv ≫ c.F.map (homOfLE (Fin.zero_le j.castSucc))) ≫
          c.F.map (homOfLE j.castSucc_le_succ) =
          c.isoBot.inv ≫ c.F.map (homOfLE (Fin.zero_le j.succ)) := by
        rw [Category.assoc, ← c.F.map_comp]
        rfl
      exact (congrArg (fun g : X ⟶ c.F.obj j.succ => ∀ x,
        Function.Surjective (FundamentalGroup.map g.hom x)) he).mp h
  obtain ⟨hpc, hp⟩ := hstage (Fin.last m)
  let := hpc
  let : IsIso (c.incl.app (Fin.last m)) :=
    c.isColimit.isIso_ι_app_of_isTerminal _ (Fin.isTerminalLast m)
  constructor
  · exact (TopCat.homeoOfIso (asIso (c.incl.app (Fin.last m)))).surjective.pathConnectedSpace
      (TopCat.homeoOfIso (asIso (c.incl.app (Fin.last m)))).continuous
  · have h := hcomp (c.isoBot.inv ≫ c.F.map (homOfLE (Fin.zero_le (Fin.last m))))
        (c.incl.app (Fin.last m)) hp (hiso (asIso (c.incl.app (Fin.last m))))
    have he : (c.isoBot.inv ≫ c.F.map (homOfLE (Fin.zero_le (Fin.last m)))) ≫
        c.incl.app (Fin.last m) = f := by
      rw [Category.assoc, c.incl.naturality]
      simp
    exact (congrArg (fun g : X ⟶ Y => ∀ x,
      Function.Surjective (FundamentalGroup.map g.hom x)) he).mp h

end HolomorphicAnosov
