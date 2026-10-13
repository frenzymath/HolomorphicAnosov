import HolomorphicAnosov.Topology.Franks.WindingMatrixHomotopy

/-! Recentering torus coordinates preserves the original integer matrix.
Source: Hatcher Lemma 1.19, pp.37–38, applied to the explicit translation
homotopy; Franks (1970), pp.69–71, the choice of pointed torus coordinates. -/
noncomputable section
namespace HolomorphicAnosov

/-- Replacing the origin by a torus point does not change the winding matrix of
a continuous self-map, using arbitrary connecting paths in both coordinates.

Proof: Choose a path a(t) from zero to a. The continuous family
f_t(x)=f(x+a(t))-a(t) joins f to its recentered conjugate. Homotopy invariance
of the winding matrix identifies their matrices, including in dimension zero. -/
theorem winding_matrix_recentering (n : ℕ)
    (f : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n)))
    (a : UnitAddTorus (Fin n))
    (w : FundamentalGroup (UnitAddTorus (Fin n)) 0 ≃* Multiplicative (Fin n → ℤ))
    (A B : Matrix (Fin n) (Fin n) ℤ) :
    let g : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n)) :=
      ⟨fun x ↦ f (x + a) - a, (f.continuous.comp (continuous_id.add continuous_const)).sub
        continuous_const⟩
    (∀ (p : Path (f 0) (0 : UnitAddTorus (Fin n))) γ,
      (w (FundamentalGroup.fundamentalGroupMulEquivOfPath p
        (FundamentalGroup.map f 0 γ))).toAdd = A.mulVec (w γ).toAdd) →
    (∀ (p : Path (g 0) (0 : UnitAddTorus (Fin n))) γ,
      (w (FundamentalGroup.fundamentalGroupMulEquivOfPath p
        (FundamentalGroup.map g 0 γ))).toAdd = B.mulVec (w γ).toAdd) → A = B := by
  dsimp only
  intro hA hB
  let g : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n)) :=
    ⟨fun x ↦ f (x + a) - a, (f.continuous.comp (continuous_id.add continuous_const)).sub
      continuous_const⟩
  let p := PathConnectedSpace.somePath (0 : UnitAddTorus (Fin n)) a
  let H : f.Homotopy g := {
    toFun := fun tx ↦ f (tx.2 + p tx.1) - p tx.1
    continuous_toFun := (f.continuous.comp
      (continuous_snd.add (p.continuous.comp continuous_fst))).sub
        (p.continuous.comp continuous_fst)
    map_zero_left := by intro x; simp
    map_one_left := by intro x; simp [g] }
  exact winding_matrix_homotopy n f g H w A B hA hB

end HolomorphicAnosov
