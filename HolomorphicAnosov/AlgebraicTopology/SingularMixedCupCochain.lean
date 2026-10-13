import HolomorphicAnosov.AlgebraicTopology.SingularRelativeCochainDegreeKernel
import HolomorphicAnosov.AlgebraicTopology.SingularCochainCupProductBilinear
import HolomorphicAnosov.AlgebraicTopology.SingularCochainCupProductNaturality

/-!
# Ordinary, mixed and relative singular cup cochains

Source: Hatcher, *Algebraic Topology*, p.209, the three same-subspace
relative products and the vanishing argument following them.
DAG node: `topo.singular_mixed_cup_cochain_g6`.
-/

open CategoryTheory CategoryTheory.Limits
universe u
noncomputable section
namespace HolomorphicAnosov.SingularCochain

set_option backward.isDefEq.respectTransparency false in
/-- The front/back formula gives a bilinear cup operation on the genuine
ordinary and relative cochain modules. Inclusion into ordinary cochains
identifies it with the original cup formula, so these are its relative lifts.

Source: Hatcher, *Algebraic Topology*, p.209. Pullback to A commutes with the
front/back formula. If either factor is relative its restriction is zero;
bilinearity then makes the product restriction zero. The degreewise kernel
property supplies a unique relative preimage. If both factors are ordinary,
use the ordinary product. Injectivity of the output inclusion transfers all
four bilinearity equations from the ordinary formula to these preimages.
No openness of A or excision assumption is needed for this single-subspace
construction. Empty A, A=X, degree zero and the zero ring are included. -/
theorem mixed_cup_cochain (R : Type u) [CommRing R]
    (X : TopCat.{u}) (A : Set X) (i j : Bool) (p q : ℕ) :
    ∃ μ : (cupComplex R X A i).X p →ₗ[R]
        (cupComplex R X A j).X q →ₗ[R] (cupComplex R X A (i || j)).X (p+q),
      ∀ a b, (cupInclusion R X A (i || j)).f (p+q) (μ a b) =
        cupCochain R X ((cupInclusion R X A i).f p a)
          ((cupInclusion R X A j).f q b) := by
  classical
  have hinj (k : Bool) (n : ℕ) : Function.Injective ((cupInclusion R X A k).f n) := by
    cases k
    · exact Function.injective_id
    · exact (relativeCochain_degree_kernel R X A n).1
  have hzero (n : ℕ) (a : (relativeComplex R X A).X n) :
      (pullback R (subspaceInclusion X A)).f n ((cupInclusion R X A true).f n a) = 0 := by
    exact (relativeCochain_degree_kernel R X A n).2 _ |>.mp ⟨a, rfl⟩
  obtain ⟨B, hB⟩ := cupCochain_bilinear R X p q
  obtain ⟨BA, hBA⟩ := cupCochain_bilinear R (TopCat.of A) p q
  have hvanish (a : (cupComplex R X A i).X p) (b : (cupComplex R X A j).X q)
      (hij : (i || j) = true) :
      (pullback R (subspaceInclusion X A)).f (p+q)
        (cupCochain R X ((cupInclusion R X A i).f p a)
          ((cupInclusion R X A j).f q b)) = 0 := by
    rw [pullback_cupCochain, ← hBA]
    cases i <;> cases j
    · contradiction
    · rw [hzero q b, map_zero]
    · rw [hzero p a]
      simp
    · rw [hzero p a]
      simp
  have hex (a : (cupComplex R X A i).X p) (b : (cupComplex R X A j).X q) :
      ∃ c : (cupComplex R X A (i || j)).X (p+q),
        (cupInclusion R X A (i || j)).f (p+q) c =
          cupCochain R X ((cupInclusion R X A i).f p a)
            ((cupInclusion R X A j).f q b) := by
    by_cases hij : (i || j) = true
    · rw [hij]
      exact (relativeCochain_degree_kernel R X A (p+q)).2 _ |>.mpr (hvanish a b hij)
    · have hi : i = false := by cases i <;> cases j <;> simp_all
      have hj : j = false := by cases i <;> cases j <;> simp_all
      subst i
      subst j
      exact ⟨cupCochain R X a b, rfl⟩
  let v (a : (cupComplex R X A i).X p) (b : (cupComplex R X A j).X q) :=
    Classical.choose (hex a b)
  have hv (a : (cupComplex R X A i).X p) (b : (cupComplex R X A j).X q) :
      (cupInclusion R X A (i || j)).f (p+q) (v a b) =
        B ((cupInclusion R X A i).f p a) ((cupInclusion R X A j).f q b) := by
    rw [hB]
    exact Classical.choose_spec (hex a b)
  refine ⟨{
    toFun := fun a ↦ {
      toFun := v a
      map_add' := ?_
      map_smul' := ?_ }
    map_add' := ?_
    map_smul' := ?_ }, ?_⟩
  · intro b b'
    apply hinj (i || j) (p+q)
    rw [map_add, hv, hv, hv, map_add, map_add]
  · intro r b
    apply hinj (i || j) (p+q)
    rw [map_smul, hv, hv, map_smul, map_smul]
    rfl
  · intro a a'
    ext b
    apply hinj (i || j) (p+q)
    change (cupInclusion R X A (i || j)).f (p+q) (v (a+a') b) =
      (cupInclusion R X A (i || j)).f (p+q) (v a b + v a' b)
    rw [map_add, hv, hv, hv, map_add, map_add, LinearMap.add_apply]
  · intro r a
    ext b
    apply hinj (i || j) (p+q)
    change (cupInclusion R X A (i || j)).f (p+q) (v (r • a) b) =
      (cupInclusion R X A (i || j)).f (p+q) (r • v a b)
    rw [map_smul, hv, hv, map_smul, map_smul, LinearMap.smul_apply]
  · intro a b
    exact (hv a b).trans (hB _ _)

end HolomorphicAnosov.SingularCochain
