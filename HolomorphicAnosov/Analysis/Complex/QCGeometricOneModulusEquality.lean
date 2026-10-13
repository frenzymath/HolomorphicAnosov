import HolomorphicAnosov.Analysis.Complex.MarkedConformalModulusCyclic

/-! # Unit geometric distortion preserves marked moduli

Source: Lehto–Virtanen (1973), I §3.1, p.16, reciprocal dilatations;
I Theorem 5.1, p.29, equality of the source and image modules.
-/

namespace HolomorphicAnosov
open Set Analysis.MarkedRectangle

/-- A one-sided unit marked-modulus bound is an equality for every admissible pair.
Source: Lehto–Virtanen I §3.1 p.16 and I Theorem 5.1 p.29.

Proof: apply the bound with the original marks and with their one-corner cyclic
shift. The latter has reciprocal source and image moduli. Both are positive
because their rectangle side lengths are positive, so inversion reverses the
second inequality. Antisymmetry gives equality. This algebraic step needs no
regularity of the mapping beyond the stated source and image modulus witnesses. -/
theorem qc_geometric_one_modulus_equality {U : Set ℂ} {g : ℂ → ℂ}
    (hBound : ∀ (Q : Set ℂ) (p : Fin 4 → ℂ) (m m' : ℝ),
      IsCompact (closure Q) → closure Q ⊆ U →
      HasMarkedConformalModulus Q p m →
      HasMarkedConformalModulus (g '' Q) (fun i ↦ g (p i)) m' → m' ≤ m)
    {Q : Set ℂ} {p : Fin 4 → ℂ} {m m' : ℝ}
    (hcompact : IsCompact (closure Q)) (hinside : closure Q ⊆ U)
    (hQ : HasMarkedConformalModulus Q p m)
    (hImage : HasMarkedConformalModulus (g '' Q) (fun i ↦ g (p i)) m') :
    m' = m := by
  have hm : 0 < m := by
    obtain ⟨a, b, ha, hb, rfl, _⟩ := hQ
    exact div_pos ha hb
  have hm' : 0 < m' := by
    obtain ⟨a, b, ha, hb, rfl, _⟩ := hImage
    exact div_pos ha hb
  have hinv : m'⁻¹ ≤ m⁻¹ := hBound Q (fun i ↦ p (i + 1)) _ _ hcompact hinside
    hQ.cyclic hImage.cyclic
  exact (hBound Q p m m' hcompact hinside hQ hImage).antisymm
    ((inv_le_inv₀ hm' hm).mp hinv)

end HolomorphicAnosov
