import Mathlib.Topology.Subpath
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-!
# Rooted subgroup generation by open-cover subdivision

This file derives the fundamental-group generation statement from finite path subdivision. (Hatcher, Lemma 1.15)
-/

namespace HolomorphicAnosov
open Set
local notation "Q" => Path.Homotopic.Quotient.mk

/-- Insertion of a connector and its reverse cancels in the path groupoid. (Hatcher, Lemma 1.15) -/
theorem rooted_path_class_trans_g3
    {X : Type*} [TopologicalSpace X] {x a b c : X}
    (qa : Path x a) (qb : Path x b) (qc : Path x c) (p : Path a b) (r : Path b c) :
    FundamentalGroup.fromPath (Q ((qa.trans (p.trans r)).trans qc.symm)) =
      FundamentalGroup.fromPath (Q ((qb.trans r).trans qc.symm)) *
      FundamentalGroup.fromPath (Q ((qa.trans p).trans qb.symm)) := by
  change (((Q (qa)).trans ((Q (p)).trans (Q (r)))).trans (Q (qc)).symm) =
    (((Q (qa)).trans (Q (p))).trans (Q (qb)).symm).trans (((Q (qb)).trans (Q (r))).trans (Q (qc)).symm)
  simp only [Path.Homotopic.Quotient.trans_assoc]
  rw [← Path.Homotopic.Quotient.trans_assoc (Q (qb)).symm (Q (qb)),
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]

/-- A finite open-cover subdivision expresses a loop class using the rooted classes of its subpaths. (Hatcher, Lemma 1.15) -/
theorem openCover_rooted_path_subgroup_g3
    {X : Type*} [TopologicalSpace X] {x : X} {ι : Type*}
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) (hcover : ∀ y, ∃ i, y ∈ U i)
    (q : ∀ y, Path x y) (hq : Path.Homotopic (q x) (Path.refl x))
    (H : Subgroup (FundamentalGroup X x))
    (hlocal : ∀ i {a b : X} (p : Path a b), (∀ t, p t ∈ U i) →
      FundamentalGroup.fromPath (Q (((q a).trans p).trans (q b).symm)) ∈ H)
    (γ : Path x x) : FundamentalGroup.fromPath (Q (γ)) ∈ H := by
  obtain ⟨s, hs0, hsmono, ⟨N, hsN⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (fun i ↦ (hU i).preimage γ.continuous)
      (fun t _ ↦ mem_iUnion.mpr (hcover (γ t)))
  have hpart : ∀ k, FundamentalGroup.fromPath
      (Q (((q (γ (s 0))).trans (γ.subpath (s 0) (s k))).trans (q (γ (s k))).symm)) ∈ H := by
    intro k
    induction k with
    | zero =>
      simpa only [Path.subpath_self, Path.Homotopic.Quotient.mk_trans,
        Path.Homotopic.Quotient.mk_refl, Path.Homotopic.Quotient.trans_refl,
        Path.Homotopic.Quotient.mk_symm, Path.Homotopic.Quotient.trans_symm]
        using (show FundamentalGroup.fromPath (Path.Homotopic.Quotient.refl x) ∈ H from H.one_mem)
    | succ k ih =>
      obtain ⟨i, hi⟩ := hsub k
      have hp : ∀ t, γ.subpath (s k) (s (k + 1)) t ∈ U i := by
        intro t
        have ht : γ.subpath (s k) (s (k + 1)) t ∈ γ '' Icc (s k) (s (k + 1)) := by
          rw [← γ.range_subpath_of_le _ _ (hsmono (Nat.le_succ k))]
          exact mem_range_self t
        obtain ⟨z, hz, he⟩ := ht
        exact he ▸ hi hz
      have hm := H.mul_mem (hlocal i _ hp) ih
      rw [← rooted_path_class_trans_g3] at hm
      have he := Path.Homotopic.subpath_trans_subpath γ (s 0) (s k) (s (k + 1))
      have he' := (Path.Homotopic.refl (q (γ (s 0)))).hcomp he
      have he'' := he'.hcomp (Path.Homotopic.refl (q (γ (s (k + 1)))).symm)
      exact (Path.Homotopic.Quotient.eq.mpr he'') ▸ hm
  have hfinish := hpart N
  rw [hs0, hsN N le_rfl, Path.subpath_zero_one] at hfinish
  have he : ((q (γ 0)).trans (γ.cast γ.source γ.target)).trans (q (γ 1)).symm =
      ((q x).trans γ).trans (q x).symm := by
    have hcast (a b : X) (ha : a = x) (hb : b = x) :
        ((q a).trans (γ.cast ha hb)).trans (q b).symm =
          ((q x).trans γ).trans (q x).symm := by
      subst a; subst b; rfl
    exact hcast _ _ γ.source γ.target
  rw [he] at hfinish
  have heq : Q (((q x).trans γ).trans (q x).symm) = Q γ := by
    have h := (hq.hcomp (Path.Homotopic.refl γ)).hcomp hq.symm₂
    apply Path.Homotopic.Quotient.eq.mpr
    simp only [Path.refl_symm] at h
    exact h.trans (((Path.Homotopic.refl_trans γ).hcomp
      (Path.Homotopic.refl (Path.refl x))).trans (Path.Homotopic.trans_refl γ))
  exact heq ▸ hfinish


end HolomorphicAnosov
