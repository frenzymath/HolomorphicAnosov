import HolomorphicAnosov.Topology.BarrNaturalHomotopyInduction

/-! Bredon VI1.2, pp.316–317: the inductive comparison construction in a
preadditive category, applied also to natural transformations. -/

open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace HolomorphicAnosov

/-- A comparison extends prescribed components in degrees zero and one when
all higher residual cycles can be filled. Source: Bredon VI1.2, pp.316–317.
The residual in degree n+2 is d composed with the previous component. Its
boundary vanishes by the preceding chain identity and d²=0. Fill it and use
Mathlib's inductive chain-map constructor. -/
theorem chain_comparison_induction
    {V : Type*} [Category V] [Preadditive V] (P Q : ChainComplex V ℕ)
    (zero : P.X 0 ⟶ Q.X 0) (one : P.X 1 ⟶ Q.X 1)
    (hone : one ≫ Q.d 1 0 = P.d 1 0 ≫ zero)
    (fill : ∀ n (r : P.X (n + 2) ⟶ Q.X (n + 1)),
      r ≫ Q.d (n + 1) n = 0 →
      ∃ s : P.X (n + 2) ⟶ Q.X (n + 2), s ≫ Q.d (n + 2) (n + 1) = r) :
    ∃ θ : P ⟶ Q, θ.f 0 = zero ∧ θ.f 1 = one := by
  classical
  let step (n : ℕ)
      (p : Σ' (f : P.X n ⟶ Q.X n) (f' : P.X (n + 1) ⟶ Q.X (n + 1)),
        f' ≫ Q.d (n + 1) n = P.d (n + 1) n ≫ f) :
      ∃ s : P.X (n + 2) ⟶ Q.X (n + 2),
        s ≫ Q.d (n + 2) (n + 1) = P.d (n + 2) (n + 1) ≫ p.2.1 := by
    apply fill n
    rw [Category.assoc, p.2.2, ← Category.assoc, P.d_comp_d, zero_comp]
  exact ⟨ChainComplex.mkHom P Q zero one hone
    (fun n p ↦ ⟨(step n p).choose, (step n p).choose_spec⟩), rfl, rfl⟩

/-- Reassemble a chain map in the functor category into a natural chain map. -/
def naturalTransformationOfChainMap {C V : Type*} [Category C] [Category V] [Preadditive V]
    {S T : C ⥤ ChainComplex V ℕ} (f : chainComplexOfFunctor S ⟶ chainComplexOfFunctor T) :
    S ⟶ T where
  app X :=
    { f n := (f.f n).app X
      comm' i j _ := NatTrans.congr_app (f.comm i j) X }
  naturality X Y g := by
    ext n
    exact (f.f n).naturality g

end HolomorphicAnosov
