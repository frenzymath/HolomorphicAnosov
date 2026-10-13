import HolomorphicAnosov.Topology.CWComplex.AdjunctionOldEmbedding
import HolomorphicAnosov.Topology.CWComplex.AttachmentCells
import Mathlib.Tactic

/-! Disjointness of the original open cells in finite attachment towers.
Source: Hatcher, Algebraic Topology, Appendix p.519. -/
open Set TopCat
open scoped TopCat
universe u
namespace HolomorphicAnosov.FiniteCellAdjunction

/-- An interior disk point has a singleton equivalence class under the boundary
attachment relation. Induction on the equivalence closure works because no
boundary generator meets that interior point. -/
theorem adjunction_interior_fiber {n : ℕ} {X : TopCat.{u}} {k : ℕ}
    {a : Fin k → C(∂𝔻 n, X)} (i : Fin k) (z : 𝔹 n)
    (p : X ⊕ (Fin k × 𝔻 n))
    (h : (Quotient.mk _ p : adjunction n X k a) =
      newCharacteristic i (ballInclusion n z)) :
    p = .inr (i, ballInclusion n z) := by
  let R := fun p q : X ⊕ (Fin k × 𝔻 n) ↦ ∃ (j : Fin k) (w : ∂𝔻 n),
    p = .inr (j, diskBoundaryInclusion n w) ∧ q = .inl (a j w)
  have hne (j : Fin k) (w : ∂𝔻 n) :
      (Sum.inr (j, diskBoundaryInclusion n w) : X ⊕ (Fin k × 𝔻 n)) ≠
        .inr (i, ballInclusion n z) := by
    intro he
    have he' := congrArg (fun v : 𝔻 n ↦ v.down.val)
      (congrArg Prod.snd (Sum.inr.inj he))
    have hw := w.down.property
    have hz := z.down.property
    change dist w.down.val 0 = 1 at hw
    change dist z.down.val 0 < 1 at hz
    change w.down.val = z.down.val at he'
    rw [he'] at hw
    exact (ne_of_lt hz) hw
  have hinvariant {p q} (he : Relation.EqvGen R p q) :
      p = .inr (i, ballInclusion n z) ↔ q = .inr (i, ballInclusion n z) := by
    induction he with
    | rel p q h =>
      obtain ⟨j, w, rfl, rfl⟩ := h
      exact iff_of_false (hne j w) (by intro h; cases h)
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  exact (hinvariant (Quotient.exact h)).mpr rfl

/-- Distinct original open cells of a finite attachment tower are disjoint.
Use the recursive disjoint-union labels of the finite-cell counting proof.
Two old cells reduce through the injective old inclusion to the preceding
stage. Old and fresh cells cannot meet because interior equivalence classes
are singletons; two fresh cells can meet only when their disk labels agree.
The initial point cells are singleton images. Surjectivity of the recursive
label decoder then gives disjointness for all original cell labels. -/
theorem tower_openCells_pairwiseDisjoint {d : ℕ} {X : TopCat.{u}} (T : Tower d X) :
    (Set.univ : Set (Σ n, Cell T n)).PairwiseDisjoint (fun c ↦ openCell c.2) := by
  let Label : {d : ℕ} → {X : TopCat.{u}} → Tower d X → Type (u + 1) :=
    fun {_} {_} T ↦ Tower.rec
      (motive := fun {_} {_} _ ↦ Type (u + 1))
      (fun X _ _ ↦ ULift.{u+1} X)
      (fun _ k _ L ↦ L ⊕ ULift.{u+1} (Fin k)) T
  let decode : {d : ℕ} → {X : TopCat.{u}} → (T : Tower d X) → Label T → Σ n, Cell T n :=
    fun {_} {_} T ↦ Tower.rec
      (motive := fun {_} {_} T ↦ Label T → Σ n, Cell T n)
      (fun X _ _ x ↦ ⟨0, .point x.down⟩)
      (fun T k a f x ↦ match x with
        | .inl z => ⟨(f z).1, .old (f z).2⟩
        | .inr i => ⟨_, .fresh i.down⟩) T
  have hsurj : ∀ {d : ℕ} {X : TopCat.{u}} (T : Tower d X),
      Function.Surjective (decode T) := by
    intro d X T ⟨n,c⟩
    induction c with
    | point x => exact ⟨ULift.up x, rfl⟩
    | @old d n X T k a c ih =>
      obtain ⟨z,hz⟩ := ih
      refine ⟨.inl z, ?_⟩
      change (⟨(decode T z).1, .old (decode T z).2⟩ : Σ n, Cell (T.attach k a) n) = _
      rw [hz]
    | fresh i => exact ⟨.inr (ULift.up i), rfl⟩
  have unique : ∀ {d : ℕ} {X : TopCat.{u}} (T : Tower d X)
      (a b : Label T) (x : X),
      x ∈ openCell (decode T a).2 → x ∈ openCell (decode T b).2 →
        decode T a = decode T b := by
    intro d X T
    induction T with
    | points X finite discrete =>
      intro a b x ha hb
      obtain ⟨z, hz⟩ := ha
      obtain ⟨w, hw⟩ := hb
      have he : a.down = b.down := hz.trans hw.symm
      change (⟨0, Cell.point a.down⟩ : Σ n, Cell (.points X finite discrete) n) =
        ⟨0, Cell.point b.down⟩
      rw [he]
    | @attach d X T k a ih =>
      intro s t x hs ht
      cases s with
      | inl s =>
        cases t with
        | inl t =>
          obtain ⟨z, hz⟩ := hs
          obtain ⟨w, hw⟩ := ht
          have he := adjunction_old_isClosedEmbedding.injective (hz.trans hw.symm)
          have hc := ih s t _ ⟨z, rfl⟩ ⟨w, he.symm⟩
          change (⟨(decode T s).1, .old (decode T s).2⟩ : Σ n, Cell (T.attach k a) n) =
            ⟨(decode T t).1, .old (decode T t).2⟩
          rw [hc]
        | inr t =>
          obtain ⟨z, hz⟩ := hs
          obtain ⟨w, hw⟩ := ht
          have he := adjunction_interior_fiber t.down w _ (hz.trans hw.symm)
          cases he
      | inr s =>
        cases t with
        | inl t =>
          obtain ⟨z, hz⟩ := hs
          obtain ⟨w, hw⟩ := ht
          have he := adjunction_interior_fiber s.down z _ (hw.trans hz.symm)
          cases he
        | inr t =>
          obtain ⟨z, hz⟩ := hs
          obtain ⟨w, hw⟩ := ht
          have he := adjunction_interior_fiber t.down w _ (hz.trans hw.symm)
          have hi : s.down = t.down := congrArg Prod.fst (Sum.inr.inj he)
          change (⟨d + 1, Cell.fresh s.down⟩ : Σ n, Cell (T.attach k a) n) =
            ⟨d + 1, Cell.fresh t.down⟩
          rw [hi]
  intro a _ b _ hab
  apply Set.disjoint_left.mpr
  intro x ha hb
  obtain ⟨s, rfl⟩ := hsurj T a
  obtain ⟨t, rfl⟩ := hsurj T b
  exact hab (unique T s t x ha hb)

end HolomorphicAnosov.FiniteCellAdjunction
