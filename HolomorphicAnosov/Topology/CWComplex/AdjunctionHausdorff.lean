import HolomorphicAnosov.Topology.CWComplex.DiskAdjunction
import Mathlib.Topology.Maps.Proper.Basic

/-! Compact closed-relation proof for the original finite disk adjunction.
DAG: `topo.finite_adjunction_hausdorff_g4`. This uses a different, explicitly
agent-written route from the radial-neighborhood proof in Hatcher p.522. -/

open Set TopCat _root_.Topology
open scoped TopCat
universe u
namespace HolomorphicAnosov.FiniteCellAdjunction

/-- Attaching finitely many disks to a compact Hausdorff space gives a
Hausdorff quotient. This is an agent-written compact closed-relation proof
of the finite special case of Hatcher Appendix Proposition A.3, p.522.
The generating relation identifies only boundary points with their attaching
images. Its equivalence closure is equality together with pairs of old or
boundary points having equal old-space images. The latter relation is the
continuous image of a closed subset of a compact space, so is closed.
The quotient projection is closed by projecting this closed relation over
closed subsets. It is proper since its fibers are closed in the compact
source. Its product is consequently closed, so the quotient diagonal is
closed and the quotient is Hausdorff. No separation of the quotient is
assumed in the argument. -/
theorem adjunction_t2Space {n : ℕ} {X : TopCat.{u}} [CompactSpace X] [T2Space X]
    {k : ℕ} {a : Fin k → C(∂𝔻 n, X)} : T2Space (adjunction n X k a) := by
  classical
  let : T2Space (TopCat.disk.{u} n) := by unfold TopCat.disk; infer_instance
  let : T2Space (TopCat.diskBoundary.{u} n) := by unfold TopCat.diskBoundary; infer_instance
  let P := X ⊕ (Fin k × 𝔻 n)
  let B := X ⊕ (Fin k × ∂𝔻 n)
  let v : B → P := Sum.map id (fun p ↦ (p.1, diskBoundaryInclusion n p.2))
  let f : B → X := Sum.elim id (fun p ↦ a p.1 p.2)
  have hv : Continuous v := continuous_id.sumMap
    (continuous_fst.prodMk ((diskBoundaryInclusion n).hom.continuous.comp continuous_snd))
  have hf : Continuous f := continuous_id.sumElim (by
    apply continuous_prod_of_discrete_left.mpr
    intro i
    exact (a i).continuous)
  have hvi : Function.Injective v := by
    apply Function.Injective.sumMap Function.injective_id
    intro x y hxy
    have hfst := congrArg (fun p : Fin k × 𝔻 n ↦ p.1) hxy
    have hsnd := congrArg (fun p : Fin k × 𝔻 n ↦ p.2) hxy
    refine Prod.ext hfst ?_
    exact ((TopCat.mono_iff_injective _).mp inferInstance) hsnd
  let R := fun p q : P ↦ ∃ (i : Fin k) (z : ∂𝔻 n),
    p = Sum.inr (i, diskBoundaryInclusion n z) ∧ q = Sum.inl (a i z)
  let E := fun p q : P ↦ p = q ∨ ∃ s t : B, v s = p ∧ v t = q ∧ f s = f t
  have hE {p q : P} (h : Relation.EqvGen R p q) : E p q := by
    induction h with
    | rel p q h =>
      obtain ⟨i, z, rfl, rfl⟩ := h
      exact Or.inr ⟨.inr (i,z), .inl (a i z), rfl, rfl, rfl⟩
    | refl p => exact Or.inl rfl
    | symm p q h ih =>
      rcases ih with he | ⟨s,t,hs,ht,hf⟩
      · exact Or.inl he.symm
      · exact Or.inr ⟨t,s,ht,hs,hf.symm⟩
    | trans p q r h₁ h₂ ih₁ ih₂ =>
      rcases ih₁ with rfl | ⟨s,t,hs,ht,hst⟩
      · exact ih₂
      rcases ih₂ with rfl | ⟨s',t',hs',ht',hst'⟩
      · exact Or.inr ⟨s,t,hs,ht,hst⟩
      have hts : t = s' := hvi (ht.trans hs'.symm)
      exact Or.inr ⟨s,t',hs,ht',hst.trans ((congrArg f hts).trans hst')⟩
  have hlink (b : B) : Relation.EqvGen R (v b) (.inl (f b)) := by
    cases b with
    | inl x => exact Relation.EqvGen.refl _
    | inr p => exact Relation.EqvGen.rel _ _ ⟨p.1,p.2,rfl,rfl⟩
  have hequiv (p q : P) : Relation.EqvGen R p q ↔ E p q := by
    refine ⟨hE, ?_⟩
    rintro (rfl | ⟨s,t,rfl,rfl,hst⟩)
    · exact Relation.EqvGen.refl _
    · apply Relation.EqvGen.trans _ _ _ (hlink s)
      rw [hst]
      exact Relation.EqvGen.symm _ _ (hlink t)
  have hclosed : IsClosed {p : P × P | Relation.EqvGen R p.1 p.2} := by
    have hc : IsCompact {b : B × B | f b.1 = f b.2} :=
      (isClosed_eq (hf.comp continuous_fst) (hf.comp continuous_snd)).isCompact
    have hi : IsClosed ((fun b : B × B ↦ (v b.1, v b.2)) '' {b | f b.1 = f b.2}) :=
      (hc.image ((hv.comp continuous_fst).prodMk (hv.comp continuous_snd))).isClosed
    convert isClosed_diagonal.union hi using 1
    ext ⟨p,q⟩
    rw [mem_ofPred_eq, hequiv]
    simp only [E, mem_union, mem_diagonal_iff, mem_image, mem_ofPred_eq, Prod.exists, Prod.mk.injEq]
    constructor
    · rintro (he | ⟨s,t,hs,ht,hst⟩)
      · exact Or.inl he
      · exact Or.inr ⟨s,t,hst,hs,ht⟩
    · rintro (he | ⟨s,t,hst,hs,ht⟩)
      · exact Or.inl he
      · exact Or.inr ⟨s,t,hs,ht,hst⟩
  let q : P → adjunction n X k a := Quotient.mk _
  have hq : Continuous q := continuous_quotient_mk'
  have hqs : Function.Surjective q := Quotient.mk_surjective
  have hqc : IsClosedMap q := by
    intro A hA
    apply isQuotientMap_quotient_mk'.isCoinducing.isClosed_preimage.mp
    have hh := isClosedMap_snd_of_compactSpace
      {p : P × P | p.1 ∈ A ∧ Relation.EqvGen R p.1 p.2}
      ((hA.preimage continuous_fst).inter hclosed)
    convert hh using 1
    ext p
    constructor
    · rintro ⟨x,hx,he⟩
      exact ⟨(x,p),⟨hx,Quotient.exact he⟩,rfl⟩
    · rintro ⟨⟨x,y⟩,⟨hx,he⟩,rfl⟩
      exact ⟨x,hx,Quotient.sound he⟩
  have hproper : IsProperMap q := by
    apply isProperMap_iff_isClosedMap_and_compact_fibers.mpr
    refine ⟨hq,hqc,?_⟩
    intro y
    obtain ⟨x,rfl⟩ := hqs y
    have hh : IsClosed {p : P | Relation.EqvGen R p x} :=
      hclosed.preimage (continuous_id.prodMk continuous_const)
    convert hh.isCompact using 1
    ext p
    exact Quotient.eq
  apply t2_iff_isClosed_diagonal.mpr
  have hh := (hproper.prodMap hproper).isClosedMap (diagonal P) isClosed_diagonal
  convert hh using 1
  ext ⟨x,y⟩
  constructor
  · intro h
    obtain ⟨z,rfl⟩ := hqs x
    change q z = y at h
    exact ⟨(z,z),rfl,by simpa only [Prod.map_apply, Prod.mk.injEq, true_and] using h⟩
  · rintro ⟨⟨p,r⟩,hpr,hxy⟩
    change p = r at hpr
    subst r
    exact (congrArg Prod.fst hxy).symm.trans (congrArg Prod.snd hxy)

end HolomorphicAnosov.FiniteCellAdjunction
