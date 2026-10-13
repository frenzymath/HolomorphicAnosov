import HolomorphicAnosov.Topology.CWComplex.AdjunctionDescent
import HolomorphicAnosov.Topology.CWComplex.AttachmentCellDisjoint
import HolomorphicAnosov.Topology.CWComplex.AttachmentSelectedTopology
import HolomorphicAnosov.Topology.CWComplex.AttachmentCells
import Mathlib.Topology.CWComplex.Abstract.Basic

import Mathlib.Topology.Category.TopCat.Limits.Products
import Mathlib.CategoryTheory.ComposableArrows.Basic
/-! Native CW structures for finite attachment towers and boundary-closed selections.

Following Hatcher, Algebraic Topology, Appendix pp.519–520, the quotient
universal property supplies each attaching pushout. A finite chain is extended
constantly to a natural-number diagram; its explicit terminal cocone is colimiting.
For a selection, the old subspace is compact, and its restricted adjunction maps
continuously and bijectively onto the selected subtype. Compactness and the
Hausdorff property identify the quotient topology with the actual induced topology.
-/
open Set TopCat
open scoped TopCat
open CategoryTheory Limits HomotopicalAlgebra
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace HolomorphicAnosov.FiniteCellAdjunction
/-- The literal adjunction is a pushout of boundary and disk coproducts: compatible maps descend uniquely through its quotient (Hatcher Appendix p.519). -/
private noncomputable def adjunctionAttachCells {n : ℕ} {X : TopCat.{u}} {k : ℕ}
    (a : Fin k → C(∂𝔻 n, X)) :
    let f : (X : TopCat) ⟶ adjunction n X k a :=
      TopCat.ofHom ⟨oldInclusion, continuous_quotient_mk'.comp continuous_inl⟩
    AttachCells (fun (_ : Unit) ↦ TopCat.diskBoundaryInclusion n) f := by
  let f : (X : TopCat) ⟶ adjunction n X k a :=
      TopCat.ofHom ⟨oldInclusion, continuous_quotient_mk'.comp continuous_inl⟩
  change AttachCells (fun (_ : Unit) ↦ TopCat.diskBoundaryInclusion n) f
  have hcomm :
      (TopCat.ofHom ⟨fun p : Σ _ : Fin k, ∂𝔻 n ↦ a p.1 p.2, by continuity⟩) ≫ f =
      (TopCat.ofHom ⟨fun p : Σ i : Fin k, (fun _ : Fin k ↦ ∂𝔻 n) i ↦
        (⟨p.1, diskBoundaryInclusion n p.2⟩ : Σ i : Fin k, (fun _ : Fin k ↦ 𝔻 n) i), by continuity⟩) ≫
      (TopCat.ofHom ⟨fun p : Σ _ : Fin k, 𝔻 n ↦ Quotient.mk _ (Sum.inr (p.1, p.2)), by
        apply continuous_quotient_mk'.comp
        continuity⟩) := by
    apply Cofan.IsColimit.hom_ext (TopCat.sigmaCofanIsColimit _)
    intro i
    ext z
    change oldInclusion (a i z) = Quotient.mk _ (Sum.inr (i, diskBoundaryInclusion n z))
    apply Quotient.sound
    let R : (X ⊕ (Fin k × 𝔻 n)) → (X ⊕ (Fin k × 𝔻 n)) → Prop :=
      fun p q => ∃ (j : Fin k) (w : ∂𝔻 n),
        p = Sum.inr (j, diskBoundaryInclusion n w) ∧ q = Sum.inl (a j w)
    exact (Relation.EqvGen.rel (r := R)
      (Sum.inr (i, diskBoundaryInclusion n z)) (Sum.inl (a i z)) ⟨i, z, rfl, rfl⟩).symm
  refine {
  ι := Fin k
  π _ := ()
  cofan₁ := TopCat.sigmaCofan (fun _ : Fin k ↦ ∂𝔻 n)
  cofan₂ := TopCat.sigmaCofan (fun _ : Fin k ↦ 𝔻 n)
  isColimit₁ := TopCat.sigmaCofanIsColimit _
  isColimit₂ := TopCat.sigmaCofanIsColimit _
  m := TopCat.ofHom ⟨fun p : Σ i : Fin k, (fun _ : Fin k ↦ ∂𝔻 n) i ↦
      (⟨p.1, diskBoundaryInclusion n p.2⟩ : Σ i : Fin k, (fun _ : Fin k ↦ 𝔻 n) i), by continuity⟩
  hm i := by
    ext z
    rfl
  g₁ := TopCat.ofHom ⟨fun p : Σ _ : Fin k, ∂𝔻 n ↦ a p.1 p.2, by continuity⟩
  g₂ := TopCat.ofHom ⟨fun p : Σ _ : Fin k, 𝔻 n ↦ Quotient.mk _ (Sum.inr (p.1, p.2)), by
    apply continuous_quotient_mk'.comp
    continuity⟩
  isPushout := by
    refine { w := hcomm, isColimit' := ?_ }
    refine ⟨PushoutCocone.IsColimit.mk hcomm ?_ ?_ ?_ ?_⟩
    · intro s
      let f' : C(X, s.pt) := s.inl.hom
      let g' : Fin k → C(𝔻 n, s.pt) := fun i =>
        (((TopCat.sigmaCofan (fun _ : Fin k ↦ 𝔻 n)).ι.app ⟨i⟩) ≫ s.inr).hom
      have hg : ∀ (i : Fin k) (z : ∂𝔻 n), g' i (diskBoundaryInclusion n z) = f' (a i z) := by
        intro i z
        change s.inr.hom (Sigma.mk i (diskBoundaryInclusion n z)) = s.inl.hom (a i z)
        simpa [TopCat.coe_comp, Function.comp_apply, TopCat.ofHom] using
          (ConcreteCategory.congr_hom s.condition (Sigma.mk i z)).symm
      let hdesc := adjunction_desc_existsUnique f' g' hg
      exact TopCat.ofHom (Classical.choose hdesc.exists)
    · intro s
      let g' : Fin k → C(𝔻 n, s.pt) := fun i =>
        (((TopCat.sigmaCofan (fun _ : Fin k ↦ 𝔻 n)).ι.app ⟨i⟩) ≫ s.inr).hom
      have hg : ∀ (i : Fin k) (z : ∂𝔻 n), g' i (diskBoundaryInclusion n z) = s.inl.hom (a i z) := by
        intro i z
        change s.inr.hom (Sigma.mk i (diskBoundaryInclusion n z)) = s.inl.hom (a i z)
        simpa [TopCat.coe_comp, Function.comp_apply, TopCat.ofHom] using
          (ConcreteCategory.congr_hom s.condition (Sigma.mk i z)).symm
      let hdesc := adjunction_desc_existsUnique s.inl.hom g' hg
      apply TopCat.hom_ext
      ext x
      change Classical.choose hdesc.exists (oldInclusion x) = s.inl.hom x
      exact (Classical.choose_spec hdesc.exists).1 x
    · intro s
      let g' : Fin k → C(𝔻 n, s.pt) := fun i =>
        (((TopCat.sigmaCofan (fun _ : Fin k ↦ 𝔻 n)).ι.app ⟨i⟩) ≫ s.inr).hom
      have hg : ∀ (i : Fin k) (z : ∂𝔻 n), g' i (diskBoundaryInclusion n z) = s.inl.hom (a i z) := by
        intro i z
        change s.inr.hom (Sigma.mk i (diskBoundaryInclusion n z)) = s.inl.hom (a i z)
        simpa [TopCat.coe_comp, Function.comp_apply, TopCat.ofHom] using
          (ConcreteCategory.congr_hom s.condition (Sigma.mk i z)).symm
      let hdesc := adjunction_desc_existsUnique s.inl.hom g' hg
      have hF := (Classical.choose_spec hdesc.exists).2
      apply TopCat.hom_ext
      ext ⟨i, z⟩
      change Classical.choose hdesc.exists (newCharacteristic i z) = g' i z
      exact hF i z
    · intro s m hm₁ hm₂
      let g' : Fin k → C(𝔻 n, s.pt) := fun i =>
        (((TopCat.sigmaCofan (fun _ : Fin k ↦ 𝔻 n)).ι.app ⟨i⟩) ≫ s.inr).hom
      have hg : ∀ (i : Fin k) (z : ∂𝔻 n), g' i (diskBoundaryInclusion n z) = s.inl.hom (a i z) := by
        intro i z
        change s.inr.hom (Sigma.mk i (diskBoundaryInclusion n z)) = s.inl.hom (a i z)
        simpa [TopCat.coe_comp, Function.comp_apply, TopCat.ofHom] using
          (ConcreteCategory.congr_hom s.condition (Sigma.mk i z)).symm
      let hdesc := adjunction_desc_existsUnique s.inl.hom g' hg
      have hmprop :
          (∀ x : X, m.hom (oldInclusion x) = s.inl.hom x) ∧
            (∀ i : Fin k, ∀ z : 𝔻 n, m.hom (newCharacteristic i z) = g' i z) := by
        constructor
        · intro x
          have hx := ConcreteCategory.congr_hom hm₁ x
          change m.hom (oldInclusion x) = s.inl.hom x at hx
          exact hx
        · intro i z
          have hz := ConcreteCategory.congr_hom hm₂ (Sigma.mk i z)
          change m.hom (newCharacteristic i z) = g' i z at hz
          exact hz
      apply TopCat.hom_ext
      exact hdesc.unique hmprop (Classical.choose_spec hdesc.exists)

  }

/-- A finite chain with dimension-indexed attaching pushouts. -/
private structure FChain (N : ℕ) where
  X : Fin (N+1) → TopCat.{u}
  f : ∀ i : Fin N, X i.castSucc ⟶ X i.succ
  att : ∀ i : Fin N, AttachCells (fun _ : Unit ↦ TopCat.diskBoundaryInclusion i.val) (f i)

/-- Append one attaching pushout, transporting the old stages along finite-index equalities. -/
private noncomputable def FChain.append {N : ℕ} (C : FChain.{u} N)
    {Z : TopCat} (g : C.X (Fin.last N) ⟶ Z)
    (a : AttachCells (fun _ : Unit ↦ TopCat.diskBoundaryInclusion N) g) :
    FChain (N+1) := by
  let X' : Fin ((N+1)+1) → TopCat := Fin.lastCases Z (fun i => C.X i)
  let f' : ∀ i : Fin (N+1), X' i.castSucc ⟶ X' i.succ := fun i =>
    Fin.lastCases (by
      have hs : X' (Fin.last N).castSucc = C.X (Fin.last N) := by
        simp only [X', Fin.lastCases_castSucc]
      have ht : X' (Fin.last N).succ = Z := by simp [X']
      exact eqToHom hs ≫ g ≫ eqToHom ht.symm)
      (fun j => by
        have hs : X' j.castSucc.castSucc = C.X j.castSucc := by
          simp only [X', Fin.lastCases_castSucc]
        have ht : X' j.castSucc.succ = C.X j.succ := by
          rw [Fin.succ_castSucc]
          simp only [X', Fin.lastCases_castSucc]
        exact (eqToHom hs ≫ C.f j ≫ eqToHom ht.symm)) i
  let att' : ∀ i : Fin (N+1), AttachCells (fun _ : Unit ↦ TopCat.diskBoundaryInclusion i.val) (f' i) := fun i =>
    Fin.lastCases (by
      have hs : X' (Fin.last N).castSucc = C.X (Fin.last N) := by
        simp only [X', Fin.lastCases_castSucc]
      have ht : X' (Fin.last N).succ = Z := by simp [X']
      let e := Arrow.isoMk' g (f' (Fin.last N)) (eqToIso hs.symm) (eqToIso ht.symm) (by simp [f'])
      exact a.ofArrowIso e) (fun j => by
      have hs : X' j.castSucc.castSucc = C.X j.castSucc := by
        simp only [X', Fin.lastCases_castSucc]
      have ht : X' j.castSucc.succ = C.X j.succ := by
        rw [Fin.succ_castSucc]
        simp only [X', Fin.lastCases_castSucc]
      let e := Arrow.isoMk' (C.f j) (f' j.castSucc) (eqToIso hs.symm) (eqToIso ht.symm) (by simp [f'])
      exact (C.att j).ofArrowIso e) i
  exact { X := X', f := f', att := att' }

private noncomputable def emptyCofan (A : TopCat.{u}) : Cofan (fun _ : PEmpty.{u+1} ↦ A) :=
  Cofan.mk (TopCat.of PEmpty.{u+1}) (fun i ↦ i.elim)

private noncomputable def emptyCofanColimit (A : TopCat.{u}) : IsColimit (emptyCofan A) where
  desc s := TopCat.ofHom ⟨PEmpty.elim, continuous_of_discreteTopology⟩
  fac s j := j.as.elim
  uniq s m h := by ext x; exact x.elim

private noncomputable def emptyAttachCells (n : ℕ) (X : TopCat.{u}) :
    AttachCells.{u} (TopCat.RelativeCWComplex.basicCell n) (𝟙 X) where
  ι := PEmpty.{u+1}
  π i := i.elim
  cofan₁ := emptyCofan _
  cofan₂ := emptyCofan _
  isColimit₁ := emptyCofanColimit _
  isColimit₂ := emptyCofanColimit _
  m := 𝟙 _
  hm i := i.elim
  g₁ := TopCat.ofHom ⟨PEmpty.elim, continuous_of_discreteTopology⟩
  g₂ := TopCat.ofHom ⟨PEmpty.elim, continuous_of_discreteTopology⟩
  isPushout := IsPushout.of_id_snd

private noncomputable def diskZero : TopCat.disk.{u} 0 := ⟨⟨0, by simp⟩⟩

private instance diskZeroSubsingleton : Subsingleton (TopCat.disk.{u} 0) := by
  unfold TopCat.disk
  infer_instance

private instance boundaryZeroEmpty : IsEmpty (TopCat.diskBoundary.{u} 0) := by
  refine ⟨fun z ↦ ?_⟩
  have h := z.down.property
  have hz : z.down.val = 0 := Subsingleton.elim _ _
  simp [hz] at h

private noncomputable def discreteZeroCofan (X : TopCat.{u}) [DiscreteTopology X] :
    Cofan (fun _ : X ↦ TopCat.disk.{u} 0) :=
  Cofan.mk X (fun x ↦ TopCat.ofHom (ContinuousMap.const _ x))

private noncomputable def discreteZeroCofanColimit (X : TopCat.{u}) [DiscreteTopology X] :
    IsColimit (discreteZeroCofan X) where
  desc s := TopCat.ofHom ⟨fun x ↦ s.ι.app ⟨x⟩ diskZero, continuous_of_discreteTopology⟩
  fac s i := by
    ext z
    change s.ι.app i diskZero = s.ι.app i z
    congr 1
    exact @Subsingleton.elim (TopCat.disk.{u} 0) diskZeroSubsingleton _ _
  uniq s m h := by
    ext x
    exact ConcreteCategory.congr_hom (h ⟨x⟩) diskZero

private noncomputable def boundaryZeroCofan (X : TopCat.{u}) :
    Cofan (fun _ : X ↦ TopCat.diskBoundary.{u} 0) :=
  Cofan.mk (TopCat.of PEmpty.{u+1})
    (fun _ ↦ TopCat.ofHom ⟨isEmptyElim, continuous_of_discreteTopology⟩)

private noncomputable def boundaryZeroCofanColimit (X : TopCat.{u}) :
    IsColimit (boundaryZeroCofan X) where
  desc s := TopCat.ofHom ⟨PEmpty.elim, continuous_of_discreteTopology⟩
  fac s i := by
    ext z
    have : False := boundaryZeroEmpty.false z
    exact this.elim
  uniq s m h := by ext x; exact x.elim

private noncomputable def discreteZeroAttach (X : TopCat.{u}) [DiscreteTopology X] :
    AttachCells.{u} (TopCat.RelativeCWComplex.basicCell 0) (TopCat.isInitialPEmpty.to X) where
  ι := X
  π _ := ()
  cofan₁ := boundaryZeroCofan X
  cofan₂ := discreteZeroCofan X
  isColimit₁ := boundaryZeroCofanColimit X
  isColimit₂ := discreteZeroCofanColimit X
  m := TopCat.isInitialPEmpty.to X
  hm i := by ext z; exact isEmptyElim z
  g₁ := 𝟙 _
  g₂ := 𝟙 X
  isPushout := IsPushout.of_id_fst

/-- Extend a finite chain constantly beyond its last stage. -/
private noncomputable def FChain.diagram {N : ℕ} (C : FChain.{u} N) : ℕ ⥤ TopCat.{u} :=
  (show Monotone (fun n : ℕ ↦ (⟨min n N, by omega⟩ : Fin (N+1))) from
    fun i j h ↦ min_le_min_right N h).functor ⋙
    ComposableArrows.mkOfObjOfMapSucc C.X C.f

private noncomputable def FChain.cocone {N : ℕ} (C : FChain.{u} N) : Cocone C.diagram where
  pt := C.X (Fin.last N)
  ι := {
    app := fun n ↦ (ComposableArrows.mkOfObjOfMapSucc C.X C.f).map
      (homOfLE (show (⟨min n N, by omega⟩ : Fin (N+1)) ≤ Fin.last N from Fin.le_last _))
    naturality := fun i j f ↦ by
      dsimp [diagram]
      rw [Category.comp_id, ← Functor.map_comp]
      congr 1 }

/-- The stabilized diagram has the final finite stage as colimit: naturality determines every cocone by its map at that stage. -/
private noncomputable def FChain.coconeColimit {N : ℕ} (C : FChain.{u} N) :
    IsColimit C.cocone where
  desc s := (ComposableArrows.mkOfObjOfMapSucc C.X C.f).map
      (homOfLE (show Fin.last N ≤ (⟨min N N, by omega⟩ : Fin (N+1)) from by simp [Fin.le_def])) ≫ s.ι.app N
  fac s n := by
    dsimp [cocone]
    rw [← Category.assoc, ← Functor.map_comp]
    by_cases hn : n ≤ N
    · have h := s.ι.naturality (homOfLE hn)
      dsimp [diagram] at h
      rw [Category.comp_id] at h
      convert h using 1
      · rfl
      · congr 2
    · have hn : N ≤ n := by omega
      have h := s.ι.naturality (homOfLE hn)
      dsimp [diagram] at h
      rw [Category.comp_id] at h
      rw [← h, ← Category.assoc, ← Functor.map_comp]
      have hm : ((homOfLE (show (⟨min n N, by omega⟩ : Fin (N+1)) ≤ Fin.last N from Fin.le_last _) ≫
        homOfLE (show Fin.last N ≤ (⟨min N N, by omega⟩ : Fin (N+1)) from by simp [Fin.le_def])) ≫
        (show Monotone (fun n : ℕ ↦ (⟨min n N, by omega⟩ : Fin (N+1))) from
          fun i j h ↦ min_le_min_right N h).functor.map (homOfLE hn)) = 𝟙 _ := Subsingleton.elim _ _
      rw [hm]
      erw [CategoryTheory.Functor.map_id, Category.id_comp]
  uniq s m h := by
    have hh := h N
    dsimp [cocone] at hh ⊢
    rw [← hh, ← Category.assoc, ← Functor.map_comp]
    simp

private noncomputable def attachmentIndexCongr {N n : ℕ} (G : Fin (N+1) ⥤ TopCat.{u})
    {i j i' j' : Fin (N+1)} (hi : i = i') (hj : j = j') (h : i ≤ j) (h' : i' ≤ j')
    (a : AttachCells.{u} (TopCat.RelativeCWComplex.basicCell n) (G.map (homOfLE h))) :
    AttachCells.{u} (TopCat.RelativeCWComplex.basicCell n) (G.map (homOfLE h')) := by
  subst i'; subst j'; exact a

private noncomputable def FChain.diagramAttach {N : ℕ} (C : FChain.{u} N) (n : ℕ) :
    AttachCells.{u} (TopCat.RelativeCWComplex.basicCell n)
      (C.diagram.map (homOfLE (Nat.le_succ n))) := by
  change AttachCells _ ((ComposableArrows.mkOfObjOfMapSucc C.X C.f).map
    (homOfLE (show (⟨min n N, by omega⟩ : Fin (N+1)) ≤ ⟨min (n+1) N, by omega⟩ from min_le_min_right N (Nat.le_succ n))))
  by_cases hn : n < N
  · refine attachmentIndexCongr _
      (show (⟨n, by omega⟩ : Fin (N+1)) = ⟨min n N, by omega⟩ from Fin.ext (min_eq_left (Nat.le_of_lt hn)).symm)
      (show (⟨n+1, by omega⟩ : Fin (N+1)) = ⟨min (n+1) N, by omega⟩ from Fin.ext (min_eq_left (Nat.succ_le_of_lt hn)).symm)
      (show (⟨n, by omega⟩ : Fin (N+1)) ≤ ⟨n+1, by omega⟩ from Nat.le_succ n) _ ?_
    rw [show (ComposableArrows.mkOfObjOfMapSucc C.X C.f).map _ = C.f ⟨n, hn⟩ from
      ComposableArrows.mkOfObjOfMapSucc_map_succ C.X C.f n hn]
    exact C.att ⟨n, hn⟩
  · have hn : N ≤ n := by omega
    refine attachmentIndexCongr _
      (show Fin.last N = (⟨min n N, by omega⟩ : Fin (N+1)) from Fin.ext (min_eq_right hn).symm)
      (show Fin.last N = (⟨min (n+1) N, by omega⟩ : Fin (N+1)) from Fin.ext (min_eq_right (Nat.le_trans hn (Nat.le_succ n))).symm)
      le_rfl _ ?_
    have hm : (homOfLE (show Fin.last N ≤ Fin.last N from le_rfl)) = 𝟙 _ := Subsingleton.elim _ _
    rw [hm, CategoryTheory.Functor.map_id]
    exact emptyAttachCells n _

/-- The stabilized chain starts at the empty space and attaches the required disks, hence gives Mathlib’s native CW structure. -/
private noncomputable def FChain.cw {N : ℕ} (C : FChain.{u} N)
    (hzero : C.X 0 = TopCat.of PEmpty.{u+1}) : TopCat.CWComplex (C.X (Fin.last N)) where
  F := C.diagram
  isoBot := eqToIso (by simpa [diagram] using hzero) ≪≫ TopCat.initialIsoPEmpty.symm
  incl := C.cocone.ι
  isColimit := C.coconeColimit
  attachCells n _ := C.diagramAttach n

private theorem tower_chain {d : ℕ} {X : TopCat.{u}} (T : Tower d X) :
    ∃ C : FChain.{u} (d+1), C.X 0 = TopCat.of PEmpty.{u+1} ∧ C.X (Fin.last (d+1)) = X := by
  induction T with
  | points X hfinite hdiscrete =>
    let := hdiscrete
    let C : FChain.{u} 0 := {
      X := fun _ ↦ TopCat.of PEmpty.{u+1}
      f := fun i ↦ Fin.elim0 i
      att := fun i ↦ Fin.elim0 i }
    refine ⟨C.append (TopCat.isInitialPEmpty.to X) (discreteZeroAttach X), ?_, ?_⟩
    · change Fin.lastCases (motive := fun _ ↦ TopCat.{u}) X C.X (0 : Fin 1).castSucc = _
      rw [Fin.lastCases_castSucc]
    · dsimp only [FChain.append]
      exact Fin.lastCases_last
  | @attach n X T k a ih =>
    obtain ⟨C, hzero, hlast⟩ := ih
    let f : X ⟶ adjunction (n+1) X k a :=
      TopCat.ofHom ⟨oldInclusion, continuous_quotient_mk'.comp continuous_inl⟩
    let g := eqToHom hlast ≫ f
    have att : AttachCells.{u} (TopCat.RelativeCWComplex.basicCell (n+1)) g :=
      ((adjunctionAttachCells a).reindex (Equiv.ulift : ULift.{u} (Fin k) ≃ Fin k)).ofArrowIso
        (Arrow.isoMk' f g (eqToIso hlast.symm) (Iso.refl _) (by simp [g]))
    refine ⟨C.append g att, ?_, ?_⟩
    · change Fin.lastCases (motive := fun _ ↦ TopCat.{u}) (adjunction (n+1) X k a) C.X (0 : Fin (n+2)).castSucc = _
      rw [Fin.lastCases_castSucc]
      exact hzero
    · dsimp only [FChain.append]
      exact Fin.lastCases_last

/-- Every finite disk-attachment tower admits a native categorical CW structure.
The quotient universal property gives the successive pushouts. Attach zero-disks
to the empty space, append the tower’s positive-dimensional stages, and stabilize.
The final stage is the colimit of this sequence. Hatcher Appendix pp.519–520. -/
theorem tower_native_cw {d : ℕ} {X : TopCat.{u}} (T : Tower d X) :
    Nonempty (TopCat.CWComplex X) := by
  obtain ⟨C, hzero, hlast⟩ := tower_chain T
  rw [← hlast]
  exact ⟨C.cw hzero⟩

private theorem adjunction_split {n : ℕ} {X : TopCat.{u}} {k : ℕ} {a : Fin k → C(∂𝔻 n,X)}
    (q : adjunction n X k a) :
    (∃ x, q = oldInclusion x) ∨ (∃ i, ∃ z : 𝔹 n, q = newCharacteristic i (ballInclusion n z)) := by
  induction q using Quotient.inductionOn with
  | h p =>
    cases p with
    | inl x => exact Or.inl ⟨x, rfl⟩
    | inr p =>
      rcases disk_point_interior_or_boundary n p.2 with ⟨z,hz⟩ | ⟨z,hz⟩
      · exact Or.inr ⟨p.1,z,congrArg (newCharacteristic p.1) hz.symm⟩
      · exact Or.inl ⟨a p.1 z, (congrArg (newCharacteristic p.1) hz.symm).trans (newCharacteristic_boundary _ _)⟩

/-- A map of adjunctions induced by injections on old points and disk labels is injective. Every quotient point is old or interior; interior equivalence classes are singletons. -/
private theorem adjunction_map_injective {n : ℕ} {X Y : TopCat.{u}} {k l : ℕ}
    {a : Fin k → C(∂𝔻 n,X)} {b : Fin l → C(∂𝔻 n,Y)}
    (e : X → Y) (he : Function.Injective e) (j : Fin k → Fin l) (hj : Function.Injective j)
    (F : adjunction n X k a → adjunction n Y l b)
    (hOld : ∀ x, F (oldInclusion x) = oldInclusion (e x))
    (hNew : ∀ i z, F (newCharacteristic i z) = newCharacteristic (j i) z) :
    Function.Injective F := by
  intro p q hpq
  rcases adjunction_split p with ⟨x,rfl⟩ | ⟨i,z,rfl⟩
  · rcases adjunction_split q with ⟨y,rfl⟩ | ⟨i,z,rfl⟩
    · rw [hOld,hOld] at hpq
      exact congrArg oldInclusion (he (adjunction_old_isClosedEmbedding.injective hpq))
    · rw [hOld,hNew] at hpq
      have h := adjunction_interior_fiber (j i) z (.inl (e x)) hpq
      cases h
  · rcases adjunction_split q with ⟨y,rfl⟩ | ⟨i',z',rfl⟩
    · rw [hNew,hOld] at hpq
      have h := adjunction_interior_fiber (j i) z (.inl (e y)) hpq.symm
      cases h
    · rw [hNew,hNew] at hpq
      have h := Sum.inr.inj (adjunction_interior_fiber (j i') z' (.inr (j i, ballInclusion n z)) hpq)
      have hi := hj (congrArg Prod.fst h)
      have hz := congrArg Prod.snd h
      rw [hi]
      exact congrArg (newCharacteristic i') hz

/-- The restricted attachment quotient is homeomorphic to the selected subtype: descent gives a continuous bijection, its source is compact, and its target is Hausdorff. Transport the attaching pushout along this homeomorphism. -/
private theorem selected_adjunction_attach {n : ℕ} {X : TopCat.{u}} {k l : ℕ}
    {a : Fin k → C(∂𝔻 n,X)} [T2Space (adjunction n X k a)]
    (A : Set X) [CompactSpace A] (j : Fin l → Fin k) (hj : Function.Injective j)
    (ha : ∀ i z, a (j i) z ∈ A)
    (L : Set (adjunction n X k a))
    (hL : L = oldInclusion '' A ∪ ⋃ i, Set.range (newCharacteristic (j i)))
    (f : C(A,L)) (hf : ∀ x : A, (f x).val = oldInclusion x.val) :
    Nonempty (AttachCells.{u} (TopCat.RelativeCWComplex.basicCell n) (TopCat.ofHom f)) := by
  classical
  let b : Fin l → C(∂𝔻 n, TopCat.of A) := fun i ↦
    ⟨fun z ↦ ⟨a (j i) z, ha i z⟩, (a (j i)).continuous.subtype_mk _⟩
  let g : Fin l → C(𝔻 n, TopCat.of L) := fun i ↦
    ⟨fun z ↦ ⟨newCharacteristic (j i) z, by rw [hL]; exact Or.inr (mem_iUnion.mpr ⟨i,z,rfl⟩)⟩,
      (by apply Continuous.subtype_mk; exact continuous_quotient_mk'.comp (continuous_inr.comp (continuous_const.prodMk continuous_id)))⟩
  obtain ⟨F,hF,huniq⟩ := adjunction_desc_existsUnique (a := b) f g (by
    intro i z
    apply Subtype.ext
    exact (newCharacteristic_boundary (j i) z).trans (hf (b i z)).symm)
  have hFinj : Function.Injective F := by
    apply Function.Injective.of_comp (f := Subtype.val)
    exact adjunction_map_injective Subtype.val Subtype.val_injective j hj
      (fun q ↦ (F q).val)
      (fun x ↦ (congrArg Subtype.val (hF.1 x)).trans (hf x))
      (fun i z ↦ congrArg Subtype.val (hF.2 i z))
  have hFsurj : Function.Surjective F := by
    intro y
    have hy := y.property
    simp only [hL] at hy
    rcases hy with ⟨x,hx,hxy⟩ | hy
    · refine ⟨oldInclusion (⟨x,hx⟩ : A), ?_⟩
      apply Subtype.ext
      exact (congrArg Subtype.val (hF.1 ⟨x,hx⟩)).trans ((hf ⟨x,hx⟩).trans hxy)
    · obtain ⟨i,z,hz⟩ := mem_iUnion.mp hy
      refine ⟨newCharacteristic i z, ?_⟩
      apply Subtype.ext
      exact (congrArg Subtype.val (hF.2 i z)).trans hz
  let : CompactSpace (adjunction n (TopCat.of A) l b) := by unfold adjunction; infer_instance
  let e : adjunction n (TopCat.of A) l b ≃ₜ L :=
    (Equiv.ofBijective F ⟨hFinj,hFsurj⟩).toHomeomorphOfContinuousClosed
      F.continuous F.continuous.isClosedMap
  let f₀ : TopCat.of A ⟶ adjunction n (TopCat.of A) l b :=
    TopCat.ofHom ⟨@oldInclusion n (TopCat.of A) l b, continuous_quotient_mk'.comp continuous_inl⟩
  refine ⟨((adjunctionAttachCells b).reindex (Equiv.ulift : ULift.{u} (Fin l) ≃ Fin l)).ofArrowIso
    (Arrow.isoMk' f₀ (TopCat.ofHom f) (Iso.refl _) (TopCat.isoOfHomeo e) ?_)⟩
  ext x
  exact congrArg Subtype.val (hF.1 x).symm

private def selectedUnion {d : ℕ} {X : TopCat.{u}} (T : Tower d X) (S : ∀ n, Set (Cell T n)) : Set X :=
  ⋃ (n : ℕ) (c : S n), openCell c.val

private def TowerLabel : {d : ℕ} → {X : TopCat.{u}} → Tower d X → Type (u + 1) :=
  fun {_} {_} T ↦ Tower.rec
    (motive := fun {_} {_} _ ↦ Type (u + 1))
    (fun X _ _ ↦ ULift.{u+1} X)
    (fun _ k _ L ↦ L ⊕ ULift.{u+1} (Fin k)) T

private noncomputable def decodeLabel : {d : ℕ} → {X : TopCat.{u}} → (T : Tower d X) → TowerLabel T → Σ n, Cell T n :=
  fun {_} {_} T ↦ Tower.rec
    (motive := fun {_} {_} T ↦ TowerLabel T → Σ n, Cell T n)
    (fun _X _ _ x ↦ ⟨0, .point x.down⟩)
    (fun _T _k _a f x ↦ match x with
      | .inl z => ⟨(f z).1, .old (f z).2⟩
      | .inr i => ⟨_, .fresh i.down⟩) T

private theorem decodeLabel_surjective {d : ℕ} {X : TopCat.{u}} (T : Tower d X) :
    Function.Surjective (decodeLabel T) := by
  intro ⟨n,c⟩
  induction c with
  | point x => exact ⟨ULift.up x,rfl⟩
  | @old d n X T k a c ih =>
    obtain ⟨z,hz⟩ := ih
    refine ⟨.inl z, ?_⟩
    change (⟨(decodeLabel T z).1, .old (decodeLabel T z).2⟩ : Σ n, Cell (T.attach k a) n) = _
    rw [hz]
  | fresh i => exact ⟨.inr (ULift.up i),rfl⟩

private theorem mem_selected_label {d : ℕ} {X : TopCat.{u}} (T : Tower d X)
    (S : ∀ n, Set (Cell T n)) (x : X) : x ∈ selectedUnion T S ↔
    ∃ l : TowerLabel T, (decodeLabel T l).2 ∈ S (decodeLabel T l).1 ∧
      x ∈ openCell (decodeLabel T l).2 := by
  constructor
  · intro hx
    obtain ⟨n,c,hc⟩ := (by simpa only [selectedUnion,mem_iUnion] using hx)
    obtain ⟨l,hl⟩ := decodeLabel_surjective T ⟨n,c.val⟩
    refine ⟨l, ?_⟩
    have hh : (fun p : Σ n, Cell T n ↦ p.2 ∈ S p.1 ∧ x ∈ openCell p.2) ⟨n,c.val⟩ := ⟨c.property,hc⟩
    rwa [← hl] at hh
  · rintro ⟨l,hl,hx⟩
    exact mem_iUnion.mpr ⟨_,mem_iUnion.mpr ⟨⟨_,hl⟩,hx⟩⟩

/-- Membership of an old point in a selection is exactly membership in its old selection. Fresh interiors cannot meet the old image. -/
private theorem selected_old_iff {d : ℕ} {X : TopCat.{u}} (T : Tower d X) {k : ℕ}
    (a : Fin k → C(∂𝔻 (d+1),X)) (S : ∀ n, Set (Cell (T.attach k a) n)) (x : X) :
    oldInclusion x ∈ selectedUnion (T.attach k a) S ↔
      x ∈ selectedUnion T (fun n ↦ {c | Cell.old c ∈ S n}) := by
  rw [mem_selected_label,mem_selected_label]
  constructor
  · rintro ⟨l,hl,z,hz⟩
    cases l with
    | inl b =>
      exact ⟨b,hl,z,adjunction_old_isClosedEmbedding.injective hz⟩
    | inr i =>
      have he := adjunction_interior_fiber i.down z (.inl x) hz.symm
      cases he
  · rintro ⟨l,hl,z,hz⟩
    exact ⟨.inl l,hl,z,congrArg oldInclusion hz⟩

private theorem selected_full {d : ℕ} {X : TopCat.{u}} (T : Tower d X)
    (S : ∀ n, Set (Cell T n))
    (hboundary : ∀ n c, c ∈ S n → boundaryImage c ⊆ selectedUnion T S)
    {n : ℕ} (c : Cell T n) (hc : c ∈ S n) :
    Set.range (characteristic c) ⊆ selectedUnion T S := by
  rintro x ⟨z,rfl⟩
  rcases disk_point_interior_or_boundary n z with ⟨b,rfl⟩ | ⟨b,rfl⟩
  · exact mem_iUnion.mpr ⟨n,mem_iUnion.mpr ⟨⟨c,hc⟩,b,rfl⟩⟩
  · exact hboundary n c hc ⟨b,rfl⟩

/-- Restrict the tower stage by stage. Boundary closure restricts each selected attaching map; compactness identifies each restricted quotient with the selected subspace. Append these pushouts to the selected zero-stage chain. -/
private theorem selected_chain {d : ℕ} {X : TopCat.{u}} (T : Tower d X)
    (S : ∀ n, Set (Cell T n))
    (hboundary : ∀ n c, c ∈ S n → boundaryImage c ⊆ selectedUnion T S) :
    ∃ C : FChain.{u} (d+1), C.X 0 = TopCat.of PEmpty.{u+1} ∧
      C.X (Fin.last (d+1)) = TopCat.of (selectedUnion T S) := by
  classical
  induction T with
  | points X hfinite hdiscrete =>
    let := hfinite
    let := hdiscrete
    exact tower_chain (Tower.points (TopCat.of (selectedUnion (.points X hfinite hdiscrete) S)) inferInstance inferInstance)
  | @attach d X T k a ih =>
    let S' : ∀ n, Set (Cell T n) := fun n ↦ {c | Cell.old c ∈ S n}
    let A := selectedUnion T S'
    let L := selectedUnion (T.attach k a) S
    have hb : ∀ n c, c ∈ S' n → boundaryImage c ⊆ A := by
      intro n c hc x hx
      apply (selected_old_iff T a S x).mp
      apply hboundary n (.old c) hc
      obtain ⟨z,rfl⟩ := hx
      exact ⟨z,rfl⟩
    obtain ⟨C,hzero,hlast⟩ := ih S' hb
    let := tower_compactSpace T
    let := tower_t2Space (T.attach k a)
    let : CompactSpace A := isCompact_iff_compactSpace.mp (tower_selected_topology T S' hb).1.isCompact
    let I := {i : Fin k // Cell.fresh (T := T) (a := a) i ∈ S (d+1)}
    let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
    let j : Fin (Fintype.card I) → Fin k := fun i ↦ (e.symm i).val
    have hj : Function.Injective j := Subtype.val_injective.comp e.symm.injective
    have ha : ∀ i z, a (j i) z ∈ A := by
      intro i z
      apply (selected_old_iff T a S _).mp
      have hz := hboundary (d+1) (.fresh (j i)) (e.symm i).property
        (show newCharacteristic (j i) (diskBoundaryInclusion (d+1) z) ∈ boundaryImage (.fresh (j i)) from ⟨z,rfl⟩)
      rwa [newCharacteristic_boundary] at hz
    have hL : L = oldInclusion '' A ∪ ⋃ i, Set.range (newCharacteristic (j i)) := by
      ext y
      constructor
      · intro hy
        obtain ⟨l,hl,z,hz⟩ := (mem_selected_label (T.attach k a) S y).mp hy
        cases l with
        | inl b =>
          refine Or.inl ⟨characteristic (decodeLabel T b).2 (ballInclusion _ z), ?_, hz⟩
          exact (mem_selected_label T S' _).mpr ⟨b,hl,z,rfl⟩
        | inr i =>
          refine Or.inr (mem_iUnion.mpr ⟨e ⟨i.down,hl⟩, ballInclusion _ z, ?_⟩)
          change newCharacteristic i.down (ballInclusion (d+1) z) = y at hz
          simpa only [j, Equiv.symm_apply_apply] using hz
      · rintro (⟨x,hx,rfl⟩ | hy)
        · exact (selected_old_iff T a S x).mpr hx
        · obtain ⟨i,z,rfl⟩ := mem_iUnion.mp hy
          exact selected_full (T.attach k a) S hboundary (.fresh (j i)) (e.symm i).property ⟨z,rfl⟩
    let f : C(A,L) := ⟨fun x ↦ ⟨oldInclusion x.val, (selected_old_iff T a S x.val).mpr x.property⟩,
      (continuous_quotient_mk'.comp (continuous_inl.comp continuous_subtype_val)).subtype_mk _⟩
    obtain ⟨att⟩ := selected_adjunction_attach A j hj ha L hL f (fun _ ↦ rfl)
    let g := eqToHom hlast ≫ TopCat.ofHom f
    have att' : AttachCells.{u} (TopCat.RelativeCWComplex.basicCell (d+1)) g :=
      att.ofArrowIso (Arrow.isoMk' (TopCat.ofHom f) g (eqToIso hlast.symm) (Iso.refl _) (by simp [g]))
    refine ⟨C.append g att', ?_, ?_⟩
    · change Fin.lastCases (motive := fun _ ↦ TopCat.{u}) (TopCat.of L) C.X (0 : Fin (d+2)).castSucc = _
      rw [Fin.lastCases_castSucc]
      exact hzero
    · dsimp only [FChain.append]
      exact Fin.lastCases_last

/-- A boundary-closed selection has a native categorical CW structure on its
actual subtype topology. Restrict the old stages and the selected attaching maps.
The resulting finite quotient is continuously bijective to the selected subspace;
compactness and Hausdorff separation make this a homeomorphism. The transported
pushouts form a finite chain, which stabilizes to the required CW sequence.
Empty selections and empty attachment families are included. Hatcher Appendix p.520. -/
theorem tower_selected_native_cw {d : ℕ} {X : TopCat.{u}} (T : Tower d X)
    (S : (n : ℕ) → Set (Cell T n)) :
    let L : Set X := ⋃ (n : ℕ) (c : S n), openCell c.val
    (∀ n c, c ∈ S n → boundaryImage c ⊆ L) →
    Nonempty (TopCat.CWComplex (TopCat.of L)) := by
  intro L hb
  obtain ⟨C,hzero,hlast⟩ := selected_chain T S hb
  change Nonempty (TopCat.CWComplex (TopCat.of (selectedUnion T S)))
  rw [← hlast]
  exact ⟨C.cw hzero⟩

end HolomorphicAnosov.FiniteCellAdjunction


