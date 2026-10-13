import Mathlib.Algebra.DirectSum.Algebra
import Mathlib.LinearAlgebra.DirectSum.TensorProduct

/-!
# Coefficient algebra carried by a graded bilinear ring

This is the coefficient compatibility step in Hatcher, Algebraic Topology,
p.216: a graded ring whose multiplication is R-bilinear carries the original
R-action through the degree-zero unit.  The construction is independent of
singular cohomology.
-/

noncomputable section

open scoped DirectSum

universe u

namespace HolomorphicAnosov.AlgebraicTopology

variable (R : Type u) [CommRing R]

/-- A bilinear graded ring carries an `R`-algebra structure via scalar multiples
of its actual degree-zero unit. -/
theorem graded_algebra_of_bilinear (A : ℕ → Type u) [∀ n, AddCommGroup (A n)]
    [∀ n, Module R (A n)] [DirectSum.GRing A]
    (μ : ∀ p q, A p →ₗ[R] A q →ₗ[R] A (p + q))
    (hmul : ∀ p q (a : A p) (b : A q), GradedMonoid.GMul.mul a b = μ p q a b) :
    Nonempty (DirectSum.GAlgebra R A) := by
  let one : A 0 := GradedMonoid.GOne.one
  have hleft (p : ℕ) (a : A p) :
      GradedMonoid.mk (0 + p) (μ 0 p one a) = GradedMonoid.mk p a := by
    have h := GradedMonoid.GMonoid.one_mul (GradedMonoid.mk p a)
    change GradedMonoid.mk (0 + p) (GradedMonoid.GMul.mul one a) = _ at h
    rwa [hmul] at h
  have hright (p : ℕ) (a : A p) :
      GradedMonoid.mk (p + 0) (μ p 0 a one) = GradedMonoid.mk p a := by
    have h := GradedMonoid.GMonoid.mul_one (GradedMonoid.mk p a)
    change GradedMonoid.mk (p + 0) (GradedMonoid.GMul.mul a one) = _ at h
    rwa [hmul] at h
  refine ⟨{
    toFun := (LinearMap.toSpanSingleton R (A 0) one).toAddMonoidHom
    map_one := by simp [one]
    map_mul := ?_
    commutes := ?_
    smul_def := ?_ }⟩
  · intro r s
    change GradedMonoid.mk 0 ((r * s) • one) =
      GradedMonoid.mk (0 + 0) (GradedMonoid.GMul.mul (r • one) (s • one))
    simp only [hmul, map_smul, LinearMap.smul_apply]
    have hu : μ 0 0 one one = one := by
      exact eq_of_heq (Sigma.mk.inj_iff.mp (hleft 0 one) |>.2)
    simp only [hu, smul_smul, mul_comm r s]
  · intro r
    rintro ⟨p, a⟩
    change GradedMonoid.mk (0 + p) (GradedMonoid.GMul.mul (r • one) a) =
      GradedMonoid.mk (p + 0) (GradedMonoid.GMul.mul a (r • one))
    simp only [hmul, map_smul, LinearMap.smul_apply]
    exact (congrArg (fun z : GradedMonoid A ↦ r • z) (hleft p a)).trans
      (congrArg (fun z : GradedMonoid A ↦ r • z) (hright p a)).symm
  · intro r
    rintro ⟨p, a⟩
    change GradedMonoid.mk p (r • a) =
      GradedMonoid.mk (0 + p) (GradedMonoid.GMul.mul (r • one) a)
    rw [hmul, map_smul, LinearMap.smul_apply]
    exact (congrArg (fun z : GradedMonoid A ↦ r • z) (hleft p a)).symm


end HolomorphicAnosov.AlgebraicTopology
