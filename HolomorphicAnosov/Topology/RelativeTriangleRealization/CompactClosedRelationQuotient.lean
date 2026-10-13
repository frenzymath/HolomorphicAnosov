import HolomorphicAnosov.Topology.RelativeTriangleRealization.Basic

open Set Filter Topology _root_.Topology

noncomputable section

namespace HolomorphicAnosov.RelativeTriangleRealization

/-!
This file isolates the general topological step used by the paired-triangle
construction.  The source is Hatcher, *Algebraic Topology*, Appendix A.3,
pp. 521–522: a quotient of a compact Hausdorff space by a closed equivalence
relation is Hausdorff.  The proof below expands the two ingredients needed in
the present formalization.  First, the quotient map is closed: for a closed
set `C`, the relation restricted to `X × C` is compact, and its projection is
compact and hence closed.  Second, distinct quotient points have disjoint
neighbourhoods.  Their equivalence classes are disjoint compact closed sets;
the compact Hausdorff separation theorem gives open `U` and `V`, and the
complements of the quotient images of `Uᶜ` and `Vᶜ` are the required saturated
open neighbourhoods.

The statement is deliberately independent of the triangle model so that any
future closedness proof for a finite face-pairing relation can reuse it.
-/
theorem t2Space_quotient_of_closed_relation
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (s : Setoid X) (hR : IsClosed {p : X × X | s.r p.1 p.2}) :
    T2Space (Quotient s) := by
  let q : X → Quotient s := Quotient.mk'
  have hq : IsQuotientMap q := isQuotientMap_quotient_mk'
  have hqclosed : IsClosedMap q := by
    intro C hC
    have hRC : IsClosed ({p : X × X | s.r p.1 p.2} ∩ (Set.univ ×ˢ C)) :=
      hR.inter (isClosed_univ.prod hC)
    have hcomp : IsCompact ({p : X × X | s.r p.1 p.2} ∩ (Set.univ ×ˢ C)) := hRC.isCompact
    have hproj : IsCompact (Prod.fst '' ({p : X × X | s.r p.1 p.2} ∩ (Set.univ ×ˢ C))) :=
      hcomp.image continuous_fst
    have hpre : q ⁻¹' (q '' C) = Prod.fst '' ({p : X × X | s.r p.1 p.2} ∩ (Set.univ ×ˢ C)) := by
      ext x
      constructor
      · rintro ⟨y, hy, hxy⟩
        refine ⟨(x, y), ?_, rfl⟩
        exact ⟨Quotient.exact hxy.symm, ⟨Set.mem_univ _, hy⟩⟩
      · rintro ⟨⟨x', y⟩, ⟨hxy, _, hy⟩, rfl⟩
        exact ⟨y, hy, (Quotient.sound hxy).symm⟩
    have hpreclosed : IsClosed (q ⁻¹' (q '' C)) := hpre ▸ hproj.isClosed
    exact ((isQuotientMap_iff_isClosed.mp hq).2 (q '' C)).mpr hpreclosed
  constructor
  intro y₁ y₂ hne
  obtain ⟨x₁, rfl⟩ := Quotient.exists_rep y₁
  obtain ⟨x₂, rfl⟩ := Quotient.exists_rep y₂
  let A : Set X := {x | s.r x x₁}
  let B : Set X := {x | s.r x x₂}
  have hA : IsClosed A := by exact hR.preimage (continuous_id.prodMk continuous_const)
  have hB : IsClosed B := by exact hR.preimage (continuous_id.prodMk continuous_const)
  have hAc : IsCompact A := hA.isCompact
  have hBc : IsCompact B := hB.isCompact
  have hdis : Disjoint A B := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    apply hne
    apply Quotient.sound
    exact (s.trans (s.symm hxA) hxB)
  obtain ⟨U, V, hU, hV, hAU, hBV, hUV⟩ := SeparatedNhds.of_isCompact_isCompact hAc hBc hdis
  let OU : Set (Quotient s) := (q '' Uᶜ)ᶜ
  let OV : Set (Quotient s) := (q '' Vᶜ)ᶜ
  have hOU : IsOpen OU := (hq.isCoinducing.isOpen_preimage).mp (by
    rw [show q ⁻¹' OU = (q ⁻¹' (q '' Uᶜ))ᶜ by rfl]
    exact (hqclosed _ (isClosed_compl_iff.mpr hU)).isOpen_compl)
  have hOV : IsOpen OV := (hq.isCoinducing.isOpen_preimage).mp (by
    rw [show q ⁻¹' OV = (q ⁻¹' (q '' Vᶜ))ᶜ by rfl]
    exact (hqclosed _ (isClosed_compl_iff.mpr hV)).isOpen_compl)
  refine ⟨OU, OV, hOU, hOV, ?_, ?_, ?_⟩
  · change x₁ ∉ q ⁻¹' (q '' Uᶜ)
    intro hx
    obtain ⟨z, hz, hxz⟩ := hx
    have hxA : x₁ ∈ A := by exact s.refl _
    have hzU : z ∈ Uᶜ := hz
    have hzA : z ∈ A := by change s.r z x₁; exact Quotient.exact hxz
    exact hzU (hAU hzA)
  · change x₂ ∉ q ⁻¹' (q '' Vᶜ)
    intro hx
    obtain ⟨z, hz, hxz⟩ := hx
    have hzB : z ∈ B := by change s.r z x₂; exact Quotient.exact hxz
    exact hz (hBV hzB)
  · rw [Set.disjoint_left]
    intro y hyU hyV
    obtain ⟨x, rfl⟩ := Quotient.exists_rep y
    have hxu : x ∉ q ⁻¹' (q '' Uᶜ) := hyU
    have hxv : x ∉ q ⁻¹' (q '' Vᶜ) := hyV
    have hxU : x ∈ U := by by_contra hnx; exact hxu ⟨x, hnx, rfl⟩
    have hxV : x ∈ V := by by_contra hnx; exact hxv ⟨x, hnx, rfl⟩
    exact Set.disjoint_left.mp hUV hxU hxV

end HolomorphicAnosov.RelativeTriangleRealization
