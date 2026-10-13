import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Abel

/-! Finite-cover fixed-point counting by the elementary fibre enumeration in
Franks, *Anosov Diffeomorphisms* (1970), characteristic orientation cover argument. -/

universe u v
namespace HolomorphicAnosov.FranksCoverCount

/-- Fixed points of a self-map, as used in Franks's periodic point count. -/
abbrev FixedPoints (A : Type u) (g : A → A) := {x // g x = x}

/-- Fixed points of the deck translate `a + F` in the Franks cover count. -/
abbrev DeckFixed {X : Type u} {Y : Type v} [AddCommGroup X] [AddCommGroup Y]
    (p : Y →+ X) (F : Y → Y) (a : p.ker) : Type v :=
  FixedPoints Y (fun y ↦ (a : Y) + F y)

/-- Choose one lift of each point downstairs. A translated fixed point y maps to
(p y, y - s(p y)); the inverse maps (x,k) to y=s(x)+k and its unique translation
parameter y-F(y). The commuting equation puts that parameter in the kernel. -/
private theorem enumeration
    {X : Type u} {Y : Type v} [AddCommGroup X] [AddCommGroup Y]
    (p : Y →+ X) (F : Y → Y) (f : X → X)
    (_hp : Function.Surjective p) (_hcomm : ∀ y, p (F y) = f (p y)) :
    Nonempty ((Σ a : p.ker, DeckFixed p F a) ≃ FixedPoints X f × p.ker) := by
  classical
  let s : X → Y := fun x ↦ Classical.choose (_hp x)
  have hs : ∀ x, p (s x) = x := fun x ↦ Classical.choose_spec (_hp x)
  let forward : (Σ a : p.ker, DeckFixed p F a) → FixedPoints.{u} X f × p.ker := fun z ↦
    let a := z.1
    let y : Y := z.2.1
    let hy := z.2.2
    let hfix : f (p y) = p y := by
      rw [← _hcomm y]
      have h := congrArg p hy
      rw [map_add, AddMonoidHom.mem_ker.mp a.2, zero_add] at h
      exact h
    let k : p.ker := ⟨y - s (p y), by
      apply AddMonoidHom.mem_ker.mpr
      rw [AddMonoidHom.map_sub, hs]
      exact sub_self _⟩
    (⟨p y, hfix⟩, k)
  let inverse : FixedPoints.{u} X f × p.ker → (Σ a : p.ker, DeckFixed p F a) := fun z ↦
    let x := z.1
    let k := z.2
    let y : Y := s x.1 + (k : Y)
    let a : p.ker := ⟨y - F y, by
      apply AddMonoidHom.mem_ker.mpr
      rw [AddMonoidHom.map_sub, _hcomm]
      have hpy : p y = x.1 := by
        dsimp [y]
        rw [map_add, hs, AddMonoidHom.mem_ker.mp k.2, add_zero]
      rw [hpy, x.2]
      exact sub_self _⟩
    ⟨a, ⟨y, sub_add_cancel _ _⟩⟩
  have hleft : Function.LeftInverse inverse forward := by
    rintro ⟨a, y, hy⟩
    let k : p.ker := ⟨y - s (p y), by
      apply AddMonoidHom.mem_ker.mpr
      rw [AddMonoidHom.map_sub, hs]
      exact sub_self _⟩
    have hy' : s (p y) + (k : Y) = y := by
      dsimp [k]
      abel
    apply Sigma.subtype_ext
    · apply Subtype.ext
      change s (p y) + (y - s (p y)) - F (s (p y) + (y - s (p y))) = (a : Y)
      have h := hy'
      change s (p y) + (y - s (p y)) = y at h
      rw [h]
      exact (sub_eq_iff_eq_add).mpr hy.symm
    · change s (p y) + (y - s (p y)) = y
      abel
  have hright : Function.RightInverse inverse forward := by
    rintro ⟨x, k⟩
    apply Prod.ext
    · apply Subtype.ext
      dsimp [forward, inverse]
      rw [map_add, hs, AddMonoidHom.mem_ker.mp k.2, add_zero]
    · apply Subtype.ext
      dsimp [forward, inverse]
      rw [map_add, hs, AddMonoidHom.mem_ker.mp k.2, add_zero]
      abel
  exact ⟨Equiv.ofBijective forward
    ⟨hleft.injective, fun z ↦ ⟨inverse z, hright z⟩⟩⟩

/-- Every deck translate has a finite fixed set when the kernel and downstairs
fixed set are finite. Source: Franks (1970), orientation-cover finite-fibre count.
The enumeration embeds each translated fixed set into the finite product of the
fixed set downstairs with the kernel, including when the former is empty. -/
theorem deck_fixed_finite
    {X : Type u} {Y : Type v} [AddCommGroup X] [AddCommGroup Y]
    (p : Y →+ X) (F : Y → Y) (f : X → X)
    (hp : Function.Surjective p) (hcomm : ∀ y, p (F y) = f (p y))
    [Finite p.ker] [Finite (FixedPoints X f)] (a : p.ker) :
    Finite (DeckFixed p F a) := by
  obtain ⟨e⟩ := enumeration p F f hp hcomm
  have : Finite (Σ a : p.ker, DeckFixed p F a) := Finite.of_injective e e.injective
  exact Finite.of_injective (Sigma.mk a) (fun x y h ↦ by simpa using h)

/-- Summing fixed points of every deck translate gives the degree times the fixed
point count downstairs. Source: Franks (1970), orientation-cover periodic point
count. Choose one lift of each downstairs point and enumerate the union of all
translated fixed sets by Fix(f) × ker(p). This also proves their finiteness;
cardinality of a sigma type is a sum, and cardinality of a product is a product.
No equivariance of F under deck translations or nonempty fixed set is assumed. -/
theorem fixed_count_sum
    {X : Type u} {Y : Type v} [AddCommGroup X] [AddCommGroup Y]
    (p : Y →+ X) (F : Y → Y) (f : X → X)
    (hp : Function.Surjective p) (hcomm : ∀ y, p (F y) = f (p y))
    [Fintype p.ker] [Finite (FixedPoints X f)] :
    (∑ a : p.ker, Nat.card (DeckFixed p F a)) =
      Nat.card p.ker * Nat.card (FixedPoints X f) := by
  have : ∀ a : p.ker, Finite (DeckFixed p F a) := deck_fixed_finite p F f hp hcomm
  obtain ⟨e⟩ := enumeration p F f hp hcomm
  calc
    ∑ a : p.ker, Nat.card (DeckFixed p F a) =
        Nat.card (Σ a : p.ker, DeckFixed p F a) := Nat.card_sigma.symm
    _ = Nat.card (FixedPoints X f × p.ker) := Nat.card_congr e
    _ = Nat.card p.ker * Nat.card (FixedPoints X f) := by
      rw [Nat.card_prod, Nat.mul_comm]

end HolomorphicAnosov.FranksCoverCount

