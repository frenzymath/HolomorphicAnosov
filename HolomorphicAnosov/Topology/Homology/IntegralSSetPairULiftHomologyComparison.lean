import HolomorphicAnosov.Topology.ChainComplexIsoHomology
open CategoryTheory
noncomputable section
namespace HolomorphicAnosov
universe u

private def intULiftEquiv {M : Type} [AddCommGroup M] [Module ℤ M] : ULift.{u} M ≃ₗ[ℤ] M where
  toFun := ULift.down
  invFun := ULift.up
  left_inv := by intro x; cases x; rfl
  right_inv := by intro x; rfl
  map_add' := by intro x y; rfl
  map_smul' := by
    intro a x
    change (a • x).down =
      (Module.toDistribMulAction (self := inferInstance) : DistribMulAction ℤ M).smul a x.down
    exact (ULift.smul_down x a).trans
      (int_smul_eq_zsmul (inferInstance : Module ℤ M) a x.down).symm

private theorem chain_complex_ulift_comparison_int {R : Type} [Ring R]
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (L : ChainComplex (ModuleCat.{0} R) ℕ)
    (q : ℕ)
    (e : ∀ n, (K.X n : Type u) ≃ₗ[R] (L.X n : Type))
    (he : ∀ n x, e n ((K.d (n + 1) n).hom x) =
      (L.d (n + 1) n).hom (e (n + 1) x)) :
    ∃ E : K ≅ (ModuleCat.uliftFunctor.{u, 0} R).mapHomologicalComplex (.down ℕ) |>.obj L,
      (∀ n x, (((E).hom.f n) x).down = e n x) ∧
      ∃ _h : K.homology q ≃ₗ[R] L.homology q, True := by
  let F := ModuleCat.uliftFunctor.{u, 0} R
  let LF := F.mapHomologicalComplex (.down ℕ)
  let ei (n : ℕ) : K.X n ≅ (LF.obj L).X n :=
    ((e n).trans
      (ULift.moduleEquiv.symm : (L.X n ≃ₗ[R] ULift.{u} ((L.X n) : Type)))).toModuleIso
  have hei : ∀ i j, (ComplexShape.down ℕ).Rel i j →
      (ei i).hom ≫ (LF.obj L).d i j = K.d i j ≫ (ei j).hom := by
    intro i j hij
    have hij' : j + 1 = i := hij
    subst i
    ext x
    exact congrArg ULift.up (he j x).symm
  let E : K ≅ LF.obj L := HomologicalComplex.Hom.isoOfComponents (ei) (hei)
  refine ⟨E, (by intro n x; rfl), ?_⟩
  let qi : (LF.obj L).homology q ≅ F.obj (L.homology q) :=
    ((L.sc q).mapHomologyIso F)
  let H : K.homology q ≅ F.obj (L.homology q) :=
    HomologicalComplex.homologyMapIso E q ≪≫ qi
  let h : K.homology q ≃ₗ[R] L.homology q :=
    H.toLinearEquiv.trans ULift.moduleEquiv
  exact ⟨h, trivial⟩

/-- Given a componentwise ULift chain equivalence, the induced integral homology equivalence transports the universe-zero group to the universe-`u` coefficient complex. -/
theorem integral_ulift_homology_comparison
    (C : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    (D : ChainComplex (ModuleCat.{u} ℤ) ℕ)
    (q : ℕ) (e : ∀ k, ULift.{u} (C.X k : Type) ≃ₗ[ℤ] (D.X k : Type u))
    (he : ∀ k (x : C.X (k + 1)),
      e k (ULift.up ((C.d (k + 1) k).hom x)) =
        (D.d (k + 1) k).hom (e (k + 1) (ULift.up x))) :
    Nonempty (ULift.{u} (C.homology q : Type) ≃ₗ[ℤ] (D.homology q : Type u)) := by
  let e' : ∀ n, (D.X n : Type u) ≃ₗ[ℤ] (C.X n : Type) := fun n =>
    (e n).symm.trans intULiftEquiv
  have he' : ∀ n x, e' n ((D.d (n + 1) n).hom x) =
      (C.d (n + 1) n).hom (e' (n + 1) x) := by
    intro n x
    dsimp [e']
    refine intULiftEquiv.symm.injective (a₁ := intULiftEquiv ((e n).symm ((D.d (n + 1) n).hom x)))
      (a₂ := (C.d (n + 1) n).hom (intULiftEquiv ((e (n + 1)).symm x))) ?_
    apply (e n).injective
    let z : ULift.{u} (C.X (n + 1) : Type) := (e (n + 1)).symm x
    have hz : (e (n + 1)) z = x := by simp [z]
    have hzup : ULift.up z.down = z := by cases z; rfl
    have hcompat := he n z.down
    rw [hzup, hz] at hcompat
    simp only [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
    change (D.d (n + 1) n).hom x =
      (e n) (ULift.up ((C.d (n + 1) n).hom z.down))
    simpa [z] using hcompat.symm
  obtain ⟨E, hE, hpair⟩ := chain_complex_ulift_comparison_int D C q e' he'
  obtain ⟨h, _⟩ := hpair
  let qIso : (ULift.{u} (C.homology q : Type)) ≃ₗ[ℤ] (D.homology q : Type u) :=
    intULiftEquiv.trans h.symm
  exact ⟨qIso⟩
end HolomorphicAnosov
