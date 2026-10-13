import HolomorphicAnosov.Topology.FiniteAttachCellsPeel
import HolomorphicAnosov.Topology.SingleHigherCellAttachmentPi1

namespace HolomorphicAnosov

open CategoryTheory
universe u

/-- A finite nonempty family of cells of dimension at least two induces
surjections on based loops from the original path-connected space.

Source: Hatcher, Algebraic Topology, Proposition 1.26(a),(b), pp.50–51,
using Lemma 1.15 p.35. Induct on the number of cells: the empty pushout is
an isomorphism, while the finite pushout decomposition removes one cell.
The single-cell theorem gives path connectedness and loop surjectivity
for its first map. Apply induction to the remaining map, then map the
first loop homotopy through that map and concatenate the two homotopies.
The two named providers record the geometric and categorical obligations.
-/
theorem finite_higher_cell_attachment_nonempty_pi1_surjective
    {X Y : TopCat.{u}} [PathConnectedSpace X] (f : X ⟶ Y)
    (attachments : HomotopicalAlgebra.AttachCells.{u}
      (fun (n : {n : ℕ // 2 ≤ n}) ↦ TopCat.diskBoundaryInclusion.{u} n.val) f)
    (_hnonempty : Nonempty attachments.ι) [Finite attachments.ι] :
    ∀ (x : X) (γ : Path (f.hom x) (f.hom x)), ∃ δ : Path x x,
      Path.Homotopic (δ.map f.hom.continuous) γ := by
  classical
  have hall : ∀ N : ℕ, ∀ {X Y : TopCat.{u}} [PathConnectedSpace X]
      (f : X ⟶ Y)
      (c : HomotopicalAlgebra.AttachCells.{u}
        (fun (n : {n : ℕ // 2 ≤ n}) ↦ TopCat.diskBoundaryInclusion.{u} n.val) f)
      [Finite c.ι], Nat.card c.ι = N →
      ∀ (x : X) (γ : Path (f.hom x) (f.hom x)), ∃ δ : Path x x,
        Path.Homotopic (δ.map f.hom.continuous) γ := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro X Y hX f c hfinite hcard x γ
      cases isEmpty_or_nonempty c.ι with
      | inl hempty =>
        let k : c.cofan₂.pt ⟶ X := c.isColimit₂.desc
          (CategoryTheory.Limits.Cofan.mk X (fun i ↦ isEmptyElim i))
        have hcomm : c.g₁ ≫ 𝟙 X = c.m ≫ k := by
          apply CategoryTheory.Limits.Cofan.IsColimit.hom_ext c.isColimit₁
          intro i
          exact isEmptyElim i
        let r : Y ⟶ X := c.isPushout.desc (𝟙 X) k hcomm
        have hleft : f ≫ r = 𝟙 X := c.isPushout.inl_desc _ _ _
        have hright : r ≫ f = 𝟙 Y := by
          apply c.hom_ext
          · simp only [← Category.assoc, hleft, Category.id_comp, Category.comp_id]
          · intro i
            exact isEmptyElim i
        have hbase : x = r (f x) :=
          (congrArg (fun h : X ⟶ X ↦ h x) hleft).symm
        refine ⟨(γ.map r.hom.continuous).cast hbase hbase, ?_⟩
        have hloop : ((γ.map r.hom.continuous).cast hbase hbase).map
            f.hom.continuous = γ := by
          ext t
          exact congrArg (fun h : Y ⟶ Y ↦ h (γ t)) hright
        rw [hloop]
      | inr hnonempty =>
        obtain ⟨Z, i, j, a, φ, χ, hpush, hf, rest, hrestfinite, hrestcard⟩ :=
          finite_attachCells_peel _ f c hnonempty
        subst f
        obtain ⟨hZ, hsingle⟩ :=
          single_higher_cell_attachment_pathConnected_loop a.val a.property φ i χ hpush
        have : PathConnectedSpace Z := hZ
        have : Finite rest.ι := hrestfinite
        obtain ⟨η, hη⟩ := ih (Nat.card rest.ι) (by omega) j rest rfl (i x) γ
        obtain ⟨δ, hδ⟩ := hsingle x η
        refine ⟨δ, ?_⟩
        simpa only [Path.map_map] using (hδ.map j.hom).trans hη
  exact hall (Nat.card attachments.ι) f attachments rfl


end HolomorphicAnosov
