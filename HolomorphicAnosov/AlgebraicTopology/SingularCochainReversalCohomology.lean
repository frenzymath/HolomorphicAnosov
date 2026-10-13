import HolomorphicAnosov.AlgebraicTopology.SingularCochainPrismIdentity
import HolomorphicAnosov.AlgebraicTopology.SingularMixedCupProduct
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe u
noncomputable section
namespace HolomorphicAnosov.SingularCochain

set_option backward.isDefEq.respectTransparency false in
theorem simplex_value_pullback (R : Type u) [CommRing R]
    {X Y : TopCat.{u}} (f : X ⟶ Y) {p : ℕ}
    (a : cochains R Y p) (σ : (TopCat.toSSet.obj X) _⦋p⦌) :
    simplexValue R X ((pullback R f).f p a) σ =
      simplexValue R Y a ((TopCat.toSSet.map f).app _ σ) := by
  let a' : ((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of R R)).X p ⟶
      ModuleCat.of R R := a
  change (((TopCat.toSSet.obj X).ιChainComplex σ ≫
    (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of R R)).f p ≫ a').hom 1) = _
  rw [SSet.ι_chainComplexMap_f_assoc]
  rfl

theorem vertexRestrict_natural {X Y : TopCat.{u}} (f : X ⟶ Y) {m n : ℕ}
    (v : Fin (m+1) → Fin (n+1)) (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    vertexRestrict Y v ((TopCat.toSSet.map f).app _ σ) =
      (TopCat.toSSet.map f).app _ (vertexRestrict X v σ) := by
  apply (Y.toSSetObjEquiv (.op ⦋m⦌)).injective
  ext x
  rfl

/-- Hatcher Theorem 3.11 pp.211–212: reversal commutes with restriction,
since postcomposition of a simplex commutes with its affine vertex map. -/
theorem reverseCochain_natural (R : Type u) [CommRing R]
    {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ) (a : cochains R Y n) :
    (pullback R f).f n (reverseCochain R Y n a) =
      reverseCochain R X n ((pullback R f).f n a) := by
  apply cochain_ext R X
  intro σ
  simp only [simplex_value_pullback, reverseCochain_value, vertexRestrict_natural]

/-- Hatcher Theorem 3.11 pp.211–212: the prism commutes with restriction,
term by term, so it preserves relative cochains. -/
theorem prismCochain_natural (R : Type u) [CommRing R]
    {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ) (a : cochains R Y (n+1)) :
    (pullback R f).f n (prismCochain R Y n a) =
      prismCochain R X n ((pullback R f).f (n+1) a) := by
  apply cochain_ext R X
  intro σ
  simp only [simplex_value_pullback, prismCochain_value, vertexRestrict_natural]

theorem reverseCochain_zero (R : Type u) [CommRing R] (X : TopCat.{u}) (n : ℕ) :
    reverseCochain R X n 0 = 0 := by
  apply cochain_ext R X
  intro σ
  rw [reverseCochain_value]
  change reversalSign R n * 0 = 0
  simp

theorem prismCochain_zero (R : Type u) [CommRing R] (X : TopCat.{u}) (n : ℕ) :
    prismCochain R X n 0 = 0 := by
  apply cochain_ext R X
  intro σ
  rw [prismCochain_value]
  change (∑ i : Fin (n+1), (-1:R)^i.val * reversalSign R (n-i.val) * 0) = 0
  simp

theorem reverseCochain_degree_zero (R : Type u) [CommRing R] (X : TopCat.{u})
    (a : cochains R X 0) : reverseCochain R X 0 a = a := by
  apply cochain_ext R X
  intro σ
  rw [reverseCochain_value]
  have hrev : (Fin.rev : Fin 1 → Fin 1) = (𝟙 ⦋0⦌ : ⦋0⦌ ⟶ ⦋0⦌) := by
    funext k
    exact Subsingleton.elim _ _
  rw [hrev, vertexRestrict_face]
  simp [reversalSign]

open MixedCup
set_option backward.isDefEq.respectTransparency false in
/-- Signed reversal is the identity on ordinary and same-subspace relative
cohomology. Source: Hatcher Theorem 3.11 pp.211–212. Restriction naturality
lifts the reverse cochain and its prism primitive into the relative kernel.
Reversal commutes with coboundary, so the lift is a cocycle. In positive
degree the prism identity writes its difference from the original cocycle
as a coboundary in that same kernel. In degree zero reversal is literally
identity. Thus their classes in the actual kernel/image quotient agree. -/
theorem exists_reverse_cocycle (R : Type u) [CommRing R] (X : TopCat.{u})
    (A : Set X) (i : Bool) (n : ℕ) (a : cycles R (cupComplex R X A i) n) :
    ∃ b : cycles R (cupComplex R X A i) n,
      (cupInclusion R X A i).f n b.val =
        reverseCochain R X n ((cupInclusion R X A i).f n a.val) ∧
      cocycleClass R (cupComplex R X A i) n b =
        cocycleClass R (cupComplex R X A i) n a := by
  have hlift (n m : ℕ) (F : cochains R X n → cochains R X m)
      (G : cochains R (TopCat.of A) n → cochains R (TopCat.of A) m)
      (hF : ∀ c, (pullback R (subspaceInclusion X A)).f m (F c) =
        G ((pullback R (subspaceInclusion X A)).f n c)) (hG : G 0 = 0)
      (c : (cupComplex R X A i).X n) :
      ∃ d : (cupComplex R X A i).X m,
        (cupInclusion R X A i).f m d = F ((cupInclusion R X A i).f n c) := by
    cases i with
    | false => exact ⟨F c, rfl⟩
    | true =>
      apply (relativeCochain_degree_kernel R X A m).2 _ |>.mpr
      rw [hF, (relativeCochain_degree_kernel R X A n).2 _ |>.mp ⟨c,rfl⟩, hG]
  obtain ⟨b, hb⟩ := hlift n n (reverseCochain R X n) (reverseCochain R (TopCat.of A) n)
    (reverseCochain_natural R (subspaceInclusion X A) n) (reverseCochain_zero R _ n) a.val
  have habs : coboundary R X n ((cupInclusion R X A i).f n a.val) = 0 :=
    (mem_cycles_iff_d_eq_zero R _ _ _).mp (map_cocycle R _ n a)
  have hclosed : b ∈ cycles R (cupComplex R X A i) n := by
    rw [mem_cycles_iff_d_eq_zero]
    apply inclusion_degree_injective R X A i (n+1)
    rw [map_zero]
    have hc := congrArg (fun f ↦ f b) ((cupInclusion R X A i).comm n (n+1))
    change coboundary R X n ((cupInclusion R X A i).f n b) =
      (cupInclusion R X A i).f (n+1) ((cupComplex R X A i).d n (n+1) b) at hc
    rw [← hc, hb, reverseCochain_coboundary, habs, reverseCochain_zero]
  refine ⟨⟨b,hclosed⟩, hb, ?_⟩
  cases n with
  | zero =>
    congr 1
    apply Subtype.ext
    apply inclusion_degree_injective R X A i 0
    exact hb.trans (reverseCochain_degree_zero R X _)
  | succ n =>
    obtain ⟨c,hc⟩ := hlift (n+1) n (prismCochain R X n)
      (prismCochain R (TopCat.of A) n)
      (prismCochain_natural R (subspaceInclusion X A) n)
      (prismCochain_zero R _ n) a.val
    apply (Submodule.Quotient.eq _).mpr
    apply (boundary_successor_iff R _ n _).mpr
    refine ⟨c, ?_⟩
    apply inclusion_degree_injective R X A i (n+1)
    change (cupInclusion R X A i).f (n+1) ((cupComplex R X A i).d n (n+1) c) =
      (cupInclusion R X A i).f (n+1)
        ((⟨b,hclosed⟩ : cycles R (cupComplex R X A i) (n+1)) - a).val
    rw [Submodule.coe_sub, map_sub, hb]
    have hd := congrArg (fun f ↦ f c) ((cupInclusion R X A i).comm n (n+1))
    change coboundary R X n ((cupInclusion R X A i).f n c) =
      (cupInclusion R X A i).f (n+1) ((cupComplex R X A i).d n (n+1) c) at hd
    rw [← hd, hc]
    have h := prism_identity_succ R X n ((cupInclusion R X A i).f (n+1) a.val)
    simpa only [habs, prismCochain_zero, add_zero] using h

end HolomorphicAnosov.SingularCochain
