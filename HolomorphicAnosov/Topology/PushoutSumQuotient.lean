import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.Topology.Maps.Basic

open CategoryTheory CategoryTheory.Limits
open Topology _root_.Topology

namespace HolomorphicAnosov
universe u
noncomputable section

/-- The two canonical maps from a topological pushout jointly form a quotient map.

This is the exact quotient presentation needed before applying path subdivision to
a pushout attachment.  The proof uses only the coinduced topology of a `TopCat`
colimit and the jointly-surjective set-level pushout presentation; it imposes no
Hausdorff, T1, or injectivity assumption.  This categorical fact is the generic
replacement for the adjunction-quotient step in Hatcher's one-cell argument.
-/
theorem pushout_sum_isQuotient
    {A X B Y : TopCat.{u}} {f : A ⟶ X} {g : A ⟶ B}
    {h : X ⟶ Y} {k : B ⟶ Y}
    (hp : IsPushout f g h k) :
    IsQuotientMap (Sum.elim h.hom k.hom) := by
  refine IsQuotientMap.mk ?_ ?_
  · apply Topology.IsCoinducing.of_isOpen_preimage_iff_isOpen
    intro U
    rw [isOpen_sum_iff]
    constructor
    · rintro ⟨hleft, hright⟩
      have hleftEq : Sum.inl ⁻¹' Sum.elim h.hom k.hom ⁻¹' U = h.hom ⁻¹' U := by
        ext x
        rfl
      have hrightEq : Sum.inr ⁻¹' Sum.elim h.hom k.hom ⁻¹' U = k.hom ⁻¹' U := by
        ext x
        rfl
      rw [hleftEq] at hleft
      rw [hrightEq] at hright
      have hc := TopCat.isOpen_iff_of_isColimit
        (PushoutCocone.mk h k hp.w) hp.isColimit U
      apply hc.mpr
      intro j
      cases j with
      | none => exact (hleft.preimage f.hom.continuous)
      | some i =>
        cases i with
        | left => simpa using hleft
        | right => simpa using hright
    · intro hU
      have hc := TopCat.isOpen_iff_of_isColimit
        (PushoutCocone.mk h k hp.w) hp.isColimit U
      have hj := hc.mp hU
      constructor
      · have hleft := hj WalkingSpan.left
        change IsOpen (h.hom ⁻¹' U)
        exact hleft
      · have hright := hj WalkingSpan.right
        change IsOpen (k.hom ⁻¹' U)
        exact hright
  · intro y
    obtain ⟨x, rfl⟩ | ⟨b, rfl⟩ :=
      Types.eq_or_eq_of_isPushout (hp.map (forget TopCat)) y
    · exact ⟨Sum.inl x, rfl⟩
    · exact ⟨Sum.inr b, rfl⟩

/-- The right leg of a topological pushout has singleton fibres at points whose
preimage under the attaching map is empty.  This is the precise interior-fibre
fact needed when deleting an interior disk point in the auxiliary-strip proof.
It does not assert that the whole right leg is injective: boundary points may
still be identified when the attaching map is noninjective.  The proof uses
the set-level pushout universal property with a two-valued separator, so it
requires no separation axiom or continuity of that separator. -/
theorem pushout_right_injective_off_left_range
    {A X B Y : TopCat.{u}} {f : A ⟶ X} {g : A ⟶ B}
    {h : X ⟶ Y} {k : B ⟶ Y}
    (hp : IsPushout f g h k) {b₁ b₂ : B}
    (hb₂ : b₂ ∉ Set.range g.hom) (heq : k.hom b₁ = k.hom b₂) : b₁ = b₂ := by
  classical
  let hpT := hp.map (forget TopCat)
  let qX : X → ULift.{u} Bool := fun _ ↦ ULift.up false
  let qB : B → ULift.{u} Bool := fun b ↦ ULift.up (if b = b₂ then true else false)
  have hqB (a : A) : qB (g.hom a) = qX (f.hom a) := by
    dsimp [qB, qX]
    by_cases h : g.hom a = b₂
    · exact (hb₂ ⟨a, h⟩).elim
    · simp [h]
  have hc : (forget TopCat).map f ≫ TypeCat.ofHom qX =
      (forget TopCat).map g ≫ TypeCat.ofHom qB := by
    ext a
    simpa [TypeCat.ofHom, CategoryTheory.comp_apply] using (hqB a).symm
  let d := hpT.desc (TypeCat.ofHom qX) (TypeCat.ofHom qB) hc
  have hdB (b : B) : d (k.hom b) = qB b := by
    change (hpT.desc (TypeCat.ofHom qX) (TypeCat.ofHom qB) hc).hom
      ((forget TopCat).map k b) = qB b
    have hh := ConcreteCategory.congr_hom
      (hpT.inr_desc (TypeCat.ofHom qX) (TypeCat.ofHom qB) hc) b
    convert hh using 1 ; rfl
  have heq' : qB b₁ = qB b₂ := by
    rw [← hdB, ← hdB, heq]
  by_contra hne
  have hq1 : qB b₁ = ULift.up false := by simp [qB, hne]
  have hq2 : qB b₂ = ULift.up true := by simp [qB]
  rw [hq1, hq2] at heq'
  cases heq'

/-- A point of the right summand outside the attaching range is not in the
image of the left summand.  This cross-fibre form is useful for restricting a
pushout quotient after deleting an interior disk point. -/
theorem pushout_left_ne_right_off_left_range
    {A X B Y : TopCat.{u}} {f : A ⟶ X} {g : A ⟶ B}
    {h : X ⟶ Y} {k : B ⟶ Y}
    (hp : IsPushout f g h k) {b₂ : B}
    (hb₂ : b₂ ∉ Set.range g.hom) : ∀ x : X, h.hom x ≠ k.hom b₂ := by
  classical
  let hpT := hp.map (forget TopCat)
  let qX : X → ULift.{u} Bool := fun _ ↦ ULift.up false
  let qB : B → ULift.{u} Bool := fun b ↦ ULift.up (if b = b₂ then true else false)
  have hqB (a : A) : qB (g.hom a) = qX (f.hom a) := by
    dsimp [qB, qX]
    by_cases h : g.hom a = b₂
    · exact (hb₂ ⟨a, h⟩).elim
    · simp [h]
  have hc : (forget TopCat).map f ≫ TypeCat.ofHom qX =
      (forget TopCat).map g ≫ TypeCat.ofHom qB := by
    ext a
    simpa [TypeCat.ofHom, CategoryTheory.comp_apply] using (hqB a).symm
  let d := hpT.desc (TypeCat.ofHom qX) (TypeCat.ofHom qB) hc
  have hdX (x : X) : d (h.hom x) = qX x := by
    change (hpT.desc (TypeCat.ofHom qX) (TypeCat.ofHom qB) hc).hom
      ((forget TopCat).map h x) = qX x
    have hh := ConcreteCategory.congr_hom
      (hpT.inl_desc (TypeCat.ofHom qX) (TypeCat.ofHom qB) hc) x
    convert hh using 1 ; rfl
  have hdB : d (k.hom b₂) = qB b₂ := by
    change (hpT.desc (TypeCat.ofHom qX) (TypeCat.ofHom qB) hc).hom
      ((forget TopCat).map k b₂) = qB b₂
    have hh := ConcreteCategory.congr_hom
      (hpT.inr_desc (TypeCat.ofHom qX) (TypeCat.ofHom qB) hc) b₂
    convert hh using 1 ; rfl
  intro x heq
  have hfalse : qX x = qB b₂ := by rw [← hdX, ← hdB]; exact congrArg d heq
  simp [qX, qB] at hfalse

/-- The preimage of an interior right-summand point under the canonical sum
map is its single right representative. -/
theorem pushout_sum_preimage_singleton_of_right_off_range
    {A X B Y : TopCat.{u}} {f : A ⟶ X} {g : A ⟶ B}
    {h : X ⟶ Y} {k : B ⟶ Y}
    (hp : IsPushout f g h k) {b₂ : B}
    (hb₂ : b₂ ∉ Set.range g.hom) :
    (Sum.elim h.hom k.hom) ⁻¹' ({k.hom b₂} : Set Y) = {Sum.inr b₂} := by
  ext s
  cases s with
  | inl x =>
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Sum.elim_inl]
      constructor
      · intro heq
        exact (pushout_left_ne_right_off_left_range hp hb₂ x heq).elim
      · intro hfalse
        exact (Sum.inl_ne_inr hfalse).elim
  | inr b =>
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Sum.elim_inr,
        Set.mem_singleton_iff]
      constructor
      · intro heq
        exact congrArg Sum.inr (pushout_right_injective_off_left_range hp hb₂ heq)
      · intro heq
        exact congrArg k.hom (Sum.inr.inj heq)

/-- The complement of an interior right-summand point has open preimage under
the canonical sum quotient.  This is stated at the source level so that the
quotient criterion can establish openness in an arbitrary pushout target. -/
theorem pushout_sum_preimage_singleton_compl_isOpen
    {A X B Y : TopCat.{u}} [T1Space B] {f : A ⟶ X} {g : A ⟶ B}
    {h : X ⟶ Y} {k : B ⟶ Y}
    (hp : IsPushout f g h k) {b₂ : B}
    (hb₂ : b₂ ∉ Set.range g.hom) :
    IsOpen ((Sum.elim h.hom k.hom) ⁻¹' ({k.hom b₂}ᶜ : Set Y)) := by
  have hleft : h.hom ⁻¹' ({k.hom b₂}ᶜ : Set Y) = Set.univ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_univ,
      iff_true]
    exact pushout_left_ne_right_off_left_range hp hb₂ x
  have hright : k.hom ⁻¹' ({k.hom b₂}ᶜ : Set Y) = ({b₂}ᶜ : Set B) := by
    ext b
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff,
      Set.mem_compl_iff]
    constructor
    · intro heq hbeq
      apply heq
      rw [hbeq]
    · intro hbeq heq
      apply hbeq
      exact pushout_right_injective_off_left_range hp hb₂ heq
  apply isOpen_sum_iff.mpr
  constructor
  · change IsOpen (h.hom ⁻¹' ({k.hom b₂}ᶜ : Set Y))
    rw [hleft]
    exact isOpen_univ
  · change IsOpen (k.hom ⁻¹' ({k.hom b₂}ᶜ : Set Y))
    rw [hright]
    exact isClosed_singleton.isOpen_compl

/-- Quotientness upgrades the source-level openness above to openness of the
deleted-point complement in the pushout target itself. -/
theorem pushout_singleton_compl_isOpen_of_right_off_range
    {A X B Y : TopCat.{u}} [T1Space B] {f : A ⟶ X} {g : A ⟶ B}
    {h : X ⟶ Y} {k : B ⟶ Y}
    (hp : IsPushout f g h k) {b₂ : B}
    (hb₂ : b₂ ∉ Set.range g.hom) : IsOpen ({k.hom b₂}ᶜ : Set Y) := by
  have hpre := pushout_sum_preimage_singleton_compl_isOpen hp hb₂
  exact (pushout_sum_isQuotient hp).isCoinducing.isOpen_preimage.mp hpre


/-- In a pushout, the right preimage of the old-space image is exactly the
attaching range. This follows from commutativity on the boundary and the
cross-fibre separation away from the attaching range. -/
theorem pushout_right_preimage_left_range
    {A X B Y : TopCat.{u}} {f : A ⟶ X} {g : A ⟶ B}
    {h : X ⟶ Y} {k : B ⟶ Y}
    (hp : IsPushout f g h k) :
    k.hom ⁻¹' Set.range h.hom = Set.range g.hom := by
  classical
  ext b
  constructor
  · rintro ⟨x, hx⟩
    by_contra hb
    exact pushout_left_ne_right_off_left_range hp hb x hx
  · rintro ⟨a, rfl⟩
    refine ⟨f.hom a, ?_⟩
    exact congrArg (fun m : A ⟶ Y ↦ m a) hp.w

/-- A closed attaching range has closed old-space image in the pushout.
No separation hypothesis on the old space or target is required: the quotient
preimage is the entire left summand and the closed attaching range on the right. -/
theorem pushout_left_range_isClosed
    {A X B Y : TopCat.{u}} {f : A ⟶ X} {g : A ⟶ B}
    {h : X ⟶ Y} {k : B ⟶ Y}
    (hp : IsPushout f g h k) (hg : IsClosed (Set.range g.hom)) :
    IsClosed (Set.range h.hom) := by
  apply (pushout_sum_isQuotient hp).isCoinducing.isClosed_preimage.mp
  apply isClosed_sum_iff.mpr
  constructor
  · change IsClosed (h.hom ⁻¹' Set.range h.hom)
    have heq : h.hom ⁻¹' Set.range h.hom = Set.univ := by
      ext x
      simp
    rw [heq]
    exact isClosed_univ
  · change IsClosed (k.hom ⁻¹' Set.range h.hom)
    rw [pushout_right_preimage_left_range hp]
    exact hg


/-- An open subset of the right summand disjoint from the attaching range has
open image in the pushout. Its sum preimage is empty on the left and is the
original open set on the right, by the singleton-fibre and cross-fibre facts. -/
theorem pushout_right_image_isOpen_off_range
    {A X B Y : TopCat.{u}} {f : A ⟶ X} {g : A ⟶ B}
    {h : X ⟶ Y} {k : B ⟶ Y}
    (hp : IsPushout f g h k) {U : Set B} (hU : IsOpen U)
    (hdisj : ∀ b ∈ U, b ∉ Set.range g.hom) : IsOpen (k.hom '' U) := by
  apply (pushout_sum_isQuotient hp).isCoinducing.isOpen_preimage.mp
  apply isOpen_sum_iff.mpr
  constructor
  · change IsOpen (h.hom ⁻¹' (k.hom '' U))
    have heq : h.hom ⁻¹' (k.hom '' U) = ∅ := by
      ext x
      constructor
      · rintro ⟨b, hb, heq⟩
        exact (pushout_left_ne_right_off_left_range hp (hdisj b hb) x heq.symm).elim
      · simp
    rw [heq]
    exact isOpen_empty
  · change IsOpen (k.hom ⁻¹' (k.hom '' U))
    have heq : k.hom ⁻¹' (k.hom '' U) = U := by
      ext b
      constructor
      · rintro ⟨b', hb', heq⟩
        have hb : b = b' := pushout_right_injective_off_left_range hp
          (hdisj b' hb') heq.symm
        exact hb.symm ▸ hb'
      · intro hb
        exact ⟨b, hb, rfl⟩
    rw [heq]
    exact hU

/-- Removing a closed attaching range identifies the remaining right summand
homeomorphically with the complement of the old-space image in the pushout.
This is the open-cell chart for an arbitrary adjunction space. The inverse is
provided by joint surjectivity; the preceding fibre and open-image lemmas give
bijectivity and continuity of the inverse. No separation assumption is used. -/
theorem pushout_complement_homeomorph
    {A X B Y : TopCat.{u}} {f : A ⟶ X} {g : A ⟶ B}
    {h : X ⟶ Y} {k : B ⟶ Y}
    (hp : IsPushout f g h k) (hg : IsClosed (Set.range g.hom)) :
    ∃ e : {b : B // b ∉ Set.range g.hom} ≃ₜ {y : Y // y ∉ Set.range h.hom},
      ∀ b, (e b : Y) = k.hom b := by
  classical
  let j : {b : B // b ∉ Set.range g.hom} → {y : Y // y ∉ Set.range h.hom} := fun b ↦
    ⟨k.hom b, by
      intro hb
      have heq := pushout_right_preimage_left_range hp
      have : (b : B) ∈ k.hom ⁻¹' Set.range h.hom := hb
      rw [heq] at this
      exact b.property this⟩
  have hc : Continuous j := (k.hom.continuous.comp continuous_subtype_val).subtype_mk _
  have hinj : Function.Injective j := by
    intro b b' heq
    apply Subtype.ext
    exact pushout_right_injective_off_left_range hp b'.property
      (congrArg Subtype.val heq)
  have hsurj : Function.Surjective j := by
    intro y
    obtain ⟨x, hx⟩ | ⟨b, hb⟩ :=
      Types.eq_or_eq_of_isPushout (hp.map (forget TopCat)) (y : Y)
    · exact (y.property ⟨x, hx⟩).elim
    · have hbr : b ∉ Set.range g.hom := by
        intro hbg
        have hh : b ∈ k.hom ⁻¹' Set.range h.hom := by
          rw [pushout_right_preimage_left_range hp]
          exact hbg
        exact y.property (hb ▸ hh)
      exact ⟨⟨b, hbr⟩, Subtype.ext hb⟩
  have ho : IsOpenMap j := by
    intro U hU
    have hU' : IsOpen (Subtype.val '' U : Set B) :=
      hg.isOpen_compl.isOpenEmbedding_subtypeVal.isOpenMap U hU
    have himage := pushout_right_image_isOpen_off_range hp hU'
      (by rintro b ⟨b', hb', rfl⟩; exact b'.property)
    have heq : j '' U = Subtype.val ⁻¹' (k.hom '' (Subtype.val '' U)) := by
      ext y
      constructor
      · rintro ⟨b, hb, rfl⟩
        exact ⟨b, ⟨b, hb, rfl⟩, rfl⟩
      · rintro ⟨b, ⟨b', hb', rfl⟩, heq⟩
        exact ⟨b', hb', Subtype.ext heq⟩
    rw [heq]
    exact himage.preimage continuous_subtype_val
  exact ⟨(Equiv.ofBijective j ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen hc ho,
    fun _ ↦ rfl⟩


/-- Deleting an off-boundary point from a pushout preserves its quotient
presentation by the unchanged left summand and punctured right summand.
Only the right summand needs to be T1. Restrict the sum quotient to the open
point complement, then use the continuous open surjection which splits its
source preimage into the two summands. This is the punctured quotient needed
for descending radial deformations in the one-cell argument. -/
theorem pushout_punctured_sum_isQuotient
    {A X B Y : TopCat.{u}} [T1Space B] {f : A ⟶ X} {g : A ⟶ B}
    {h : X ⟶ Y} {k : B ⟶ Y}
    (hp : IsPushout f g h k) {b₀ : B} (hb₀ : b₀ ∉ Set.range g.hom) :
    IsQuotientMap
      (Sum.elim (fun x : X ↦
        (⟨h.hom x, pushout_left_ne_right_off_left_range hp hb₀ x⟩ :
          {y : Y // y ≠ k.hom b₀}))
        (fun b : {b : B // k.hom b ≠ k.hom b₀} ↦
          (⟨k.hom b.val, b.property⟩ : {y : Y // y ≠ k.hom b₀}))) := by
  let q : X ⊕ B → Y := Sum.elim h.hom k.hom
  let U : Set Y := {y | y ≠ k.hom b₀}
  have hU : IsOpen U := pushout_singleton_compl_isOpen_of_right_off_range hp hb₀
  let S := {s : X ⊕ B // q s ≠ k.hom b₀}
  let D := {b : B // k.hom b ≠ k.hom b₀}
  let e : X ⊕ D → S := Sum.elim
    (fun x ↦ ⟨Sum.inl x, pushout_left_ne_right_off_left_range hp hb₀ x⟩)
    (fun b ↦ ⟨Sum.inr b.val, b.property⟩)
  have hecont : Continuous e :=
    (continuous_inl.subtype_mk _).sumElim
      ((continuous_inr.comp continuous_subtype_val).subtype_mk _)
  have hD : IsOpen {b : B | k.hom b ≠ k.hom b₀} := hU.preimage k.hom.continuous
  have heopen : IsOpenMap e :=
    (isOpenMap_inl.subtype_mk _).sumElim
      ((isOpenMap_inr.comp hD.isOpenEmbedding_subtypeVal.isOpenMap).subtype_mk _)
  have hesurj : Function.Surjective e := by
    rintro ⟨s, hs⟩
    cases s with
    | inl x => exact ⟨Sum.inl x, rfl⟩
    | inr b => exact ⟨Sum.inr ⟨b, hs⟩, rfl⟩
  have hq := (pushout_sum_isQuotient hp).restrictPreimage_isOpen hU
  have hh := hq.comp (heopen.isQuotientMap hecont hesurj)
  have heq : (U.restrictPreimage q) ∘ e =
      Sum.elim (fun x : X ↦
        (⟨h.hom x, pushout_left_ne_right_off_left_range hp hb₀ x⟩ :
          {y : Y // y ≠ k.hom b₀}))
        (fun b : D ↦ (⟨k.hom b.val, b.property⟩ : {y : Y // y ≠ k.hom b₀})) := by
    funext s
    cases s with
    | inl x => rfl
    | inr b => rfl
  rw [heq] at hh
  exact hh


/-- Compatible continuous formulas on the unchanged left summand and the
punctured right summand descend to the punctured pushout. To prove this, extend
the right formula arbitrarily at the deleted fibre, use the set-level pushout
universal property, and recover continuity on the puncture from its sum
quotient presentation. The arbitrary extension is never evaluated there.
This supplies the radial retraction and homotopy descent without imposing T1
on the old space or on the pushout target. -/
theorem pushout_punctured_continuous_desc
    {A X B Y : TopCat.{u}} [T1Space B] {f : A ⟶ X} {g : A ⟶ B}
    {h : X ⟶ Y} {k : B ⟶ Y}
    (hp : IsPushout f g h k) {b₀ : B} (hb₀ : b₀ ∉ Set.range g.hom)
    {T : Type u} [TopologicalSpace T] [Nonempty T]
    (F : C(X, T)) (G : C({b : B // k.hom b ≠ k.hom b₀}, T))
    (hcompat : ∀ (a : A) (ha : k.hom (g.hom a) ≠ k.hom b₀),
      F (f.hom a) = G ⟨g.hom a, ha⟩) :
    ∃ R : C({y : Y // y ≠ k.hom b₀}, T),
      (∀ x, R ⟨h.hom x, pushout_left_ne_right_off_left_range hp hb₀ x⟩ = F x) ∧
      (∀ b, R ⟨k.hom b.val, b.property⟩ = G b) := by
  classical
  let hpT := hp.map (forget TopCat)
  let GB : B → T := fun b ↦ if hb : k.hom b ≠ k.hom b₀ then G ⟨b, hb⟩
    else Classical.choice ‹Nonempty T›
  have hboundary (a : A) : k.hom (g.hom a) ≠ k.hom b₀ := by
    have heq : h.hom (f.hom a) = k.hom (g.hom a) :=
      congrArg (fun m : A ⟶ Y ↦ m a) hp.w
    rw [← heq]
    exact pushout_left_ne_right_off_left_range hp hb₀ (f.hom a)
  have hc : (forget TopCat).map f ≫ TypeCat.ofHom F =
      (forget TopCat).map g ≫ TypeCat.ofHom GB := by
    ext a
    change F (f.hom a) = GB (g.hom a)
    simpa only [GB, dite_eq_left (hboundary a)] using hcompat a (hboundary a)
  let d := hpT.desc (TypeCat.ofHom F) (TypeCat.ofHom GB) hc
  have hdX (x : X) : d (h.hom x) = F x := by
    change (hpT.desc (TypeCat.ofHom F) (TypeCat.ofHom GB) hc).hom
      ((forget TopCat).map h x) = F x
    have hh := ConcreteCategory.congr_hom
      (hpT.inl_desc (TypeCat.ofHom F) (TypeCat.ofHom GB) hc) x
    convert hh using 1 ; rfl
  have hdB (b : B) : d (k.hom b) = GB b := by
    change (hpT.desc (TypeCat.ofHom F) (TypeCat.ofHom GB) hc).hom
      ((forget TopCat).map k b) = GB b
    have hh := ConcreteCategory.congr_hom
      (hpT.inr_desc (TypeCat.ofHom F) (TypeCat.ofHom GB) hc) b
    convert hh using 1 ; rfl
  let R : {y : Y // y ≠ k.hom b₀} → T := fun y ↦ d y.val
  have hRX (x : X) : R ⟨h.hom x,
      pushout_left_ne_right_off_left_range hp hb₀ x⟩ = F x := hdX x
  have hRB (b : {b : B // k.hom b ≠ k.hom b₀}) :
      R ⟨k.hom b.val, b.property⟩ = G b := by
    change d (k.hom b.val) = G b
    rw [hdB]
    simp only [GB, dite_eq_left b.property]
  have hR : Continuous R := by
    apply (pushout_punctured_sum_isQuotient hp hb₀).continuous_iff.mpr
    have heq : R ∘ Sum.elim
        (fun x : X ↦ (⟨h.hom x, pushout_left_ne_right_off_left_range hp hb₀ x⟩ :
          {y : Y // y ≠ k.hom b₀}))
        (fun b : {b : B // k.hom b ≠ k.hom b₀} ↦
          (⟨k.hom b.val, b.property⟩ : {y : Y // y ≠ k.hom b₀})) =
        Sum.elim F G := by
      funext s
      cases s with
      | inl x => exact hRX x
      | inr b => exact hRB b
    rw [heq]
    exact F.continuous.sumElim G.continuous
  exact ⟨⟨R, hR⟩, hRX, hRB⟩

end
end HolomorphicAnosov

