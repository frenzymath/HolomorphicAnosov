import Mathlib.Algebra.Group.Hom.End

namespace HolomorphicAnosov.Topology

/-- A group homomorphism transports a finite signed generator word by mapping
 each letter and preserving the list product. This is the algebraic bridge
 used after compact subdivision has produced a quotient word.

Source: Hatcher, *Algebraic Topology*, Proposition 1A.2, pp.84--85; the
quotient-induced fundamental-group map sends each oriented generator to its
image and respects multiplication and inversion.
-/
theorem graph_spanning_tree_loop_fundamental_word_map_g3
    {G H E : Type*} [Group G] [Group H]
    (φ : G →* H) (generator : E → G) (word : List (E × Bool)) :
    φ ((word.map (fun letter ↦
      if letter.2 then generator letter.1 else (generator letter.1)⁻¹)).prod) =
      (word.map (fun letter ↦
        if letter.2 then φ (generator letter.1) else (φ (generator letter.1))⁻¹)).prod := by
  induction word with
  | nil => simp
  | cons a w ih =>
      simp only [List.map_cons, List.prod_cons, map_mul]
      rw [ih]
      cases a.2 <;> simp

end HolomorphicAnosov.Topology
