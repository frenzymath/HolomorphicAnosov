import Mathlib.Algebra.Homology.Homotopy

open CategoryTheory CategoryTheory.Preadditive

namespace HolomorphicAnosov

/-- Barr's uniqueness induction with the degree-zero homotopy fixed to zero.

Source: Barr, Acyclic Models, Chapter 5 §5 Proposition 5.5, printed p.116.
The source proof constructs a homotopy by filling the residual cycle in each
degree. When the chain map vanishes in degree zero, start with H0 = 0.
In degree n+1 subtract the preceding H-component composed with the source
differential. The chain-map identity, preceding homotopy identity and d² = 0
make this residual a cycle. The stated Hom-exactness supplies its filling.
The resulting components satisfy e = dH + Hd, with H0 unchanged at zero. -/
theorem barr_relative_null_homotopy
    {V : Type*} [Category V] [Preadditive V]
    {P Q : ChainComplex V ℕ} (e : P ⟶ Q) (hzero : e.f 0 = 0)
    (hfill : ∀ (n : ℕ) (r : P.X (n + 1) ⟶ Q.X (n + 1)),
      r ≫ Q.d (n + 1) n = 0 →
      ∃ s : P.X (n + 1) ⟶ Q.X (n + 2), s ≫ Q.d (n + 2) (n + 1) = r) :
    ∃ H : Homotopy e 0, H.hom 0 1 = 0 := by
  classical
  have hcycle1 : e.f 1 ≫ Q.d 1 0 = 0 := by
    simp only [e.comm, hzero, CategoryTheory.Limits.comp_zero]
  obtain ⟨one, hone⟩ := hfill 0 (e.f 1) hcycle1
  have hcomm0 : e.f 0 = (0 : P.X 0 ⟶ Q.X 1) ≫ Q.d 1 0 := by
    simpa using hzero
  have hcomm1 : e.f 1 = P.d 1 0 ≫ (0 : P.X 0 ⟶ Q.X 1) + one ≫ Q.d 2 1 := by
    simpa using hone.symm
  have hstep (n : ℕ)
      (p : Σ' (f : P.X n ⟶ Q.X (n + 1)) (f' : P.X (n + 1) ⟶ Q.X (n + 2)),
        e.f (n + 1) = P.d (n + 1) n ≫ f + f' ≫ Q.d (n + 2) (n + 1)) :
      ∃ f'' : P.X (n + 2) ⟶ Q.X (n + 3),
        e.f (n + 2) = P.d (n + 2) (n + 1) ≫ p.2.1 + f'' ≫ Q.d (n + 3) (n + 2) := by
    rcases p with ⟨f, f', hp⟩
    let r := e.f (n + 2) - P.d (n + 2) (n + 1) ≫ f'
    have hcycle : r ≫ Q.d (n + 2) (n + 1) = 0 := by
      dsimp [r]
      rw [sub_comp, e.comm, Category.assoc, ← comp_sub, hp, add_sub_cancel_right]
      rw [← Category.assoc, P.d_comp_d, CategoryTheory.Limits.zero_comp]
    obtain ⟨s, hs⟩ := hfill (n + 1) r hcycle
    refine ⟨s, ?_⟩
    rw [hs]
    dsimp [r]
    abel
  refine ⟨Homotopy.mkInductive e 0 hcomm0 one hcomm1
    (fun n p ↦ ⟨(hstep n p).choose, (hstep n p).choose_spec⟩), ?_⟩
  simp [Homotopy.mkInductive, Homotopy.mkInductiveAux₂_zero]

/-- Relative uniqueness form of Barr's Proposition 5.5, printed p.116.
Apply the preceding residual-cycle induction to the difference of the two maps.
The standard correspondence from a null homotopy of the difference to a
homotopy between the maps preserves every homotopy component. -/
theorem barr_relative_homotopy
    {V : Type*} [Category V] [Preadditive V]
    {P Q : ChainComplex V ℕ} (f g : P ⟶ Q) (hzero : f.f 0 = g.f 0)
    (hfill : ∀ (n : ℕ) (r : P.X (n + 1) ⟶ Q.X (n + 1)),
      r ≫ Q.d (n + 1) n = 0 →
      ∃ s : P.X (n + 1) ⟶ Q.X (n + 2), s ≫ Q.d (n + 2) (n + 1) = r) :
    ∃ H : Homotopy f g, H.hom 0 1 = 0 := by
  obtain ⟨H, hH⟩ := barr_relative_null_homotopy (f - g) (by simp [hzero]) hfill
  exact ⟨Homotopy.equivSubZero.symm H, hH⟩

end HolomorphicAnosov
