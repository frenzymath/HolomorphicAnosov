import Mathlib.Algebra.DirectSum.Ring

noncomputable section
namespace HolomorphicAnosov

/-- Package a unital associative graded bilinear product as a graded ring.
This is the algebraic construction behind Hatcher, Algebraic Topology, p.207:
bilinearity gives distributivity and zero products, while the specified unit
supplies natural and integer casts by its additive multiples. -/
@[instance_reducible]
def gradedRingOfBilinearProduct (R : Type*) [CommRing R]
    (A : ℕ → Type*) [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    (mul : ∀ p q, A p →ₗ[R] A q →ₗ[R] A (p + q)) (one : A 0)
    (hone : ∀ p (a : A p), HEq (mul 0 p one a) a)
    (hmulone : ∀ p (a : A p), HEq (mul p 0 a one) a)
    (hassoc : ∀ p q r (a : A p) (b : A q) (c : A r),
      HEq (mul (p + q) r (mul p q a b) c) (mul p (q + r) a (mul q r b c))) :
    DirectSum.GRing A := by
  let : GradedMonoid.GMul A := ⟨fun {p q} a b ↦ mul p q a b⟩
  let : GradedMonoid.GOne A := ⟨one⟩
  refine {
    mul_zero := ?_
    zero_mul := ?_
    mul_add := ?_
    add_mul := ?_
    one_mul := ?_
    mul_one := ?_
    mul_assoc := ?_
    natCast := fun n ↦ n • one
    natCast_zero := zero_nsmul _
    natCast_succ := fun n ↦ succ_nsmul _ _
    intCast := fun n ↦ n • one
    intCast_ofNat := fun n ↦ natCast_zsmul _ _
    intCast_negSucc_ofNat := fun n ↦ by simp }
  · intro p q a
    exact (mul p q a).map_zero
  · intro p q b
    exact congrArg (fun L : A q →ₗ[R] A (p + q) ↦ L b) (mul p q).map_zero
  · intro p q a b c
    exact (mul p q a).map_add b c
  · intro p q a b c
    exact congrArg (fun L : A q →ₗ[R] A (p + q) ↦ L c) ((mul p q).map_add a b)
  · rintro ⟨p, a⟩
    exact Sigma.ext (zero_add p) (hone p a)
  · rintro ⟨p, a⟩
    exact Sigma.ext (add_zero p) (hmulone p a)
  · rintro ⟨p, a⟩ ⟨q, b⟩ ⟨r, c⟩
    exact Sigma.ext (add_assoc p q r) (hassoc p q r a b c)

end HolomorphicAnosov
