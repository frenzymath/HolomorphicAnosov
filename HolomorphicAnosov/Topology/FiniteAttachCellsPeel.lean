import Mathlib.AlgebraicTopology.RelativeCellComplex.AttachCells
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.SetTheory.Cardinal.Finite

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
namespace HolomorphicAnosov
universe u v
noncomputable section

/--
  A finite nonempty family of cells factors as a chosen cell followed by the
  pushout of the remaining family.  The proof constructs the tail pushout
  cocone explicitly and proves its `fac` and `uniq` fields by the two colimit
  hom extensionality principles.

  Source: Hatcher, *Algebraic Topology*, Proposition 1.26, pp. 50–51.
  Hatcher supplies the finite reordering argument; the present statement and
  categorical API expansion package that argument for `AttachCells`.
-/
theorem finite_attachCells_peel
    {α : Type v} {A B : α → TopCat.{u}} (g : ∀ a, A a ⟶ B a)
    {X Y : TopCat.{u}} (f : X ⟶ Y)
    (c : HomotopicalAlgebra.AttachCells.{u} g f)
    [Finite c.ι] (hι : Nonempty c.ι) :
    ∃ (Z : TopCat.{u}) (i : X ⟶ Z) (j : Z ⟶ Y)
      (a : α) (φ : A a ⟶ X) (χ : B a ⟶ Z),
      IsPushout φ (g a) i χ ∧ f = i ≫ j ∧
      ∃ rest : HomotopicalAlgebra.AttachCells.{u} g j,
        Finite rest.ι ∧ Nat.card rest.ι + 1 = Nat.card c.ι := by
  let := Fintype.ofFinite c.ι
  let z : c.ι := Classical.choice hι
  let P : TopCat := pushout (c.cofan₁.inj z ≫ c.g₁) (g (c.π z))
  let i : X ⟶ P := pushout.inl _ _
  let χ : B (c.π z) ⟶ P := pushout.inr _ _
  have hw : c.cofan₁.inj z ≫ c.g₁ ≫ f = g (c.π z) ≫ c.cofan₂.inj z ≫ c.g₂ := by
    rw [c.isPushout.w, ← Category.assoc, c.hm]
    simp only [Category.assoc]
  let j : P ⟶ Y := IsPushout.desc (IsPushout.of_hasPushout _ _) f
    (c.cofan₂.inj z ≫ c.g₂) hw
  have hfj : f = i ≫ j := by
    symm
    exact IsPushout.inl_desc (IsPushout.of_hasPushout _ _) f _ hw
  have hχ : χ ≫ j = c.cofan₂.inj z ≫ c.g₂ := by
    exact IsPushout.inr_desc (IsPushout.of_hasPushout _ _) f _ hw
  let : Fintype {q : c.ι // q ≠ z} := Fintype.ofFinite _
  let tail : {q : c.ι // q ≠ z} → TopCat := fun k => A (c.π k.1)
  let tailB : {q : c.ι // q ≠ z} → TopCat := fun k => B (c.π k.1)
  let tailG : ∀ k, tail k ⟶ tailB k := fun k => g (c.π k.1)
  let ta : Cofan tail := Cofan.mk (∐ tail) (fun k => Sigma.ι tail k)
  let tb : Cofan tailB := Cofan.mk (∐ tailB) (fun k => Sigma.ι tailB k)
  have hta : IsColimit ta := colimit.isColimit _
  have htb : IsColimit tb := colimit.isColimit _
  let gl : ta.pt ⟶ P := hta.desc (Cofan.mk P (fun k =>
      c.cofan₁.inj k.1 ≫ c.g₁ ≫ i))
  let gr : tb.pt ⟶ Y := htb.desc (Cofan.mk Y (fun k =>
    c.cofan₂.inj k.1 ≫ c.g₂))
  let mrest : ta.pt ⟶ tb.pt := hta.desc (Cofan.mk tb.pt (fun k => tailG k ≫ tb.inj k))
  have hιomp : gl ≫ j = mrest ≫ gr := by
    apply hta.hom_ext
    intro ⟨k⟩
    have hgl := hta.fac (Cofan.mk P (fun k =>
      c.cofan₁.inj k.1 ≫ c.g₁ ≫ i)) ⟨k⟩
    have hmr := hta.fac (Cofan.mk tb.pt (fun k => tailG k ≫ tb.inj k)) ⟨k⟩
    have hgr := htb.fac (Cofan.mk Y (fun k =>
      c.cofan₂.inj k.1 ≫ c.g₂)) ⟨k⟩
    have hgr' : tb.inj k ≫ gr = c.cofan₂.inj k.1 ≫ c.g₂ := by
      change Sigma.ι tailB k ≫ htb.desc (Cofan.mk Y (fun k =>
        c.cofan₂.inj k.1 ≫ c.g₂)) = _
      exact htb.fac _ ⟨k⟩
    calc
      ta.ι.app ⟨k⟩ ≫ gl ≫ j = (ta.ι.app ⟨k⟩ ≫ gl) ≫ j := by rfl
      _ = (c.cofan₁.inj k.1 ≫ c.g₁ ≫ i) ≫ j := by
        simpa only [Cofan.mk_ι_app] using congrArg (fun t => t ≫ j) hgl
      _ = c.cofan₁.inj k.1 ≫ c.g₁ ≫ (i ≫ j) := by rfl
      _ = c.cofan₁.inj k.1 ≫ c.g₁ ≫ f := by
        simpa only [Category.assoc] using
          (congrArg (fun t => c.cofan₁.inj k.1 ≫ c.g₁ ≫ t) hfj).symm
      _ = g (c.π k.1) ≫ c.cofan₂.inj k.1 ≫ c.g₂ := by
        rw [c.isPushout.w, ← Category.assoc, c.hm]
        simp only [Category.assoc]
      _ = (tailG k ≫ tb.inj k) ≫ gr := by
        simpa only [tailG, Category.assoc] using
          (congrArg (fun t => g (c.π k.1) ≫ t) hgr'.symm)
      _ = (ta.ι.app ⟨k⟩ ≫ mrest) ≫ gr := by
        simpa only [Cofan.mk_ι_app] using congrArg (fun t => t ≫ gr) hmr.symm
      _ = ta.ι.app ⟨k⟩ ≫ mrest ≫ gr := by rfl
  have htail : IsPushout gl mrest j gr := by
    classical
    refine IsPushout.mk ⟨hιomp⟩ ?_
    · let Q : PushoutCocone gl mrest := PushoutCocone.mk j gr hιomp
      refine ⟨PushoutCocone.isColimitAux' Q (fun s => ?_)⟩
      · let kP := s.ι.app WalkingSpan.left
        change P ⟶ s.pt at kP
        let kR := s.ι.app WalkingSpan.right
        change tb.pt ⟶ s.pt at kR
        let kX : X ⟶ s.pt := i ≫ kP
        let kC : c.cofan₂.pt ⟶ s.pt := c.isColimit₂.desc (Cofan.mk s.pt (fun q =>
          if hq : q = z then eqToHom (by subst hq; rfl) ≫ χ ≫ kP
            else tb.inj ⟨q, hq⟩ ≫ kR))
        have hCfac (q : c.ι) : c.cofan₂.inj q ≫ kC =
            if hq : q = z then eqToHom (by subst hq; rfl) ≫ χ ≫ kP
            else tb.inj ⟨q, hq⟩ ≫ kR := by
          exact c.isColimit₂.fac (Cofan.mk s.pt (fun q =>
            if hq : q = z then eqToHom (by subst hq; rfl) ≫ χ ≫ kP
            else tb.inj ⟨q, hq⟩ ≫ kR)) ⟨q⟩
        have hC : c.g₁ ≫ kX = c.m ≫ kC := by
          apply c.isColimit₁.hom_ext
          intro ⟨q⟩
          by_cases hq : q = z
          · subst q
            have hpush₀ : (c.cofan₁.inj z ≫ c.g₁) ≫ i =
                g (c.π z) ≫ χ := pushout.condition
            change ((c.cofan₁.inj z ≫ c.g₁) ≫ i) ≫ kP =
              c.cofan₁.inj z ≫ c.m ≫ kC
            calc
              ((c.cofan₁.inj z ≫ c.g₁) ≫ i) ≫ kP =
                  (g (c.π z) ≫ χ) ≫ kP := by rw [hpush₀]
              _ = g (c.π z) ≫ (χ ≫ kP) := by rfl
              _ = g (c.π z) ≫ (c.cofan₂.inj z ≫ kC) := by
                rw [hCfac z]
                simp
              _ = (g (c.π z) ≫ c.cofan₂.inj z) ≫ kC := by simp only [Category.assoc]
              _ = (c.cofan₁.inj z ≫ c.m) ≫ kC := by rw [c.hm z]
              _ = c.cofan₁.inj z ≫ c.m ≫ kC := by rfl
          · have hs₁ := s.ι.naturality WalkingSpan.Hom.fst
            have hs₂ := s.ι.naturality WalkingSpan.Hom.snd
            dsimp [span] at hs₁ hs₂
            have hs : gl ≫ kP = mrest ≫ kR := by
              rw [hs₁, hs₂]
            have hs' := congrArg
              (fun t => ta.ι.app ⟨⟨q, hq⟩⟩ ≫ t) hs
            calc
              c.cofan₁.ι.app ⟨q⟩ ≫ c.g₁ ≫ kX =
                  c.cofan₁.inj q ≫ c.g₁ ≫ i ≫ kP := by rfl
              _ = ta.ι.app ⟨⟨q, hq⟩⟩ ≫ gl ≫ kP := by
                simp [gl, Category.assoc]
              _ = ta.ι.app ⟨⟨q, hq⟩⟩ ≫ mrest ≫ kR := hs'
              _ = g (c.π q) ≫ tb.inj ⟨q, hq⟩ ≫ kR := by
                simp [mrest, tailG, Category.assoc]
              _ = c.cofan₁.inj q ≫ c.m ≫ kC := by
                have hqfac := hCfac q
                rw [dite_eq_right hq] at hqfac
                calc
                  (g (c.π q) ≫ tb.inj ⟨q, hq⟩) ≫ kR =
                      g (c.π q) ≫ (tb.inj ⟨q, hq⟩ ≫ kR) := by rfl
                  _ = g (c.π q) ≫ (c.cofan₂.inj q ≫ kC) := by
                    rw [hqfac]
                  _ = (c.cofan₁.inj q ≫ c.m) ≫ kC := by
                    rw [c.hm q]
                    simp only [Category.assoc]
                  _ = c.cofan₁.inj q ≫ c.m ≫ kC := by rfl
        let l : Y ⟶ s.pt := c.isPushout.desc kX kC hC
        have hlX : f ≫ l = kX := c.isPushout.inl_desc _ _ _
        have hlC : c.g₂ ≫ l = kC := c.isPushout.inr_desc _ _ _
        have hleft : j ≫ l = kP := by
          apply IsPushout.hom_ext (IsPushout.of_hasPushout
            (c.cofan₁.inj z ≫ c.g₁) (g (c.π z)))
          · change i ≫ j ≫ l = i ≫ kP
            rw [← Category.assoc, ← hfj, hlX]
          · change χ ≫ j ≫ l = χ ≫ kP
            rw [← Category.assoc, hχ, Category.assoc, hlC, hCfac z]
            simp
        have hright : gr ≫ l = kR := by
          apply htb.hom_ext
          rintro ⟨k⟩
          have hgr : tb.inj k ≫ gr = c.cofan₂.inj k.1 ≫ c.g₂ :=
            htb.fac _ ⟨k⟩
          change tb.inj k ≫ gr ≫ l = tb.inj k ≫ kR
          rw [← Category.assoc, hgr, Category.assoc, hlC, hCfac k.1]
          simp [k.2]
        refine ⟨l, hleft, hright, ?_⟩
        intro m hmL hmR
        have hmL' : j ≫ m = s.ι.app WalkingSpan.left := by
          simpa [Q] using hmL
        have hmR' : gr ≫ m = s.ι.app WalkingSpan.right := by
          simpa [Q] using hmR
        apply c.isPushout.hom_ext
        · calc
            f ≫ m = (i ≫ j) ≫ m := congrArg (fun t => t ≫ m) hfj
            _ = i ≫ kP := by rw [Category.assoc, hmL']
            _ = f ≫ l := hlX.symm
        · apply c.isColimit₂.hom_ext
          rintro ⟨q⟩
          change c.cofan₂.inj q ≫ c.g₂ ≫ m = c.cofan₂.inj q ≫ c.g₂ ≫ l
          rw [hlC, hCfac q]
          by_cases hq : q = z
          · subst q
            simp only [dite_eq_left rfl, eqToHom_refl, Category.id_comp]
            rw [← Category.assoc, ← hχ, Category.assoc, hmL']
          · rw [dite_eq_right hq]
            have hgr : tb.inj ⟨q, hq⟩ ≫ gr = c.cofan₂.inj q ≫ c.g₂ :=
              htb.fac _ ⟨⟨q, hq⟩⟩
            rw [← Category.assoc, ← hgr, Category.assoc, hmR']
  let rest : AttachCells g j := {
    ι := {q : c.ι // q ≠ z}
    π := fun q => c.π q.1
    cofan₁ := ta
    cofan₂ := tb
    isColimit₁ := hta
    isColimit₂ := htb
    m := mrest
    hm := by
      intro k
      simp [mrest, tailG]
    g₁ := gl
    g₂ := gr
    isPushout := htail }
  have hrestfinite : Finite rest.ι := by infer_instance
  have hrestcard : Nat.card rest.ι + 1 = Nat.card c.ι := by
    dsimp [rest]
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    rw [Fintype.card_subtype_compl (fun q : c.ι => q = z)]
    simp only [Fintype.card_subtype_eq]
    have hιard : 0 < Fintype.card c.ι := Fintype.card_pos_iff.mpr hι
    omega
  exact ⟨P, i, j, c.π z, c.cofan₁.inj z ≫ c.g₁, χ, 
    IsPushout.of_hasPushout _ _, hfj, rest, hrestfinite, hrestcard⟩

end
end HolomorphicAnosov
