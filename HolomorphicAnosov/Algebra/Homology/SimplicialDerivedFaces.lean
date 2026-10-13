import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

/-! For every simplicial object in a preadditive category, let ∂* be the alternating sum F₁−F₂+⋯ of all faces except the initial face. The full boundary is F₀−∂*, and in every positive input degree ∂*D₀=id−D₀∂*. Adjoining an initial vertex to every ordinal map defines an injective-on-morphisms functor which shifts every face and degeneracy index by one. The boundary on the derived simplicial object is the original positive-face operator in degrees at least two, and initial face defines a natural transformation from the derived object to the original.

Eilenberg–Mac Lane, On the Groups H(Π,n), I (1953), §3 definition (3.3) p.59; Theorem3.2 equation (3.5), boundary splitting (3.6), face commutations (3.7), and degeneracy identity (3.11), p.60. Supplied original: literature/G2-EM1953-full-supplied.txt and corresponding PDF. -/


open CategoryTheory
open scoped Simplicial

namespace HolomorphicAnosov.SimplicialDerivedFaces
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The alternating positive-face operator F₁−F₂+⋯, denoted ∂* in
Eilenberg–Mac Lane (1953), §3 pp.58–60. -/
def positiveFaces (X : SimplicialObject C) (n : ℕ) : X _⦋n + 1⦌ ⟶ X _⦋n⦌ :=
  ∑ i : Fin (n + 1), (-1 : ℤ)^i.val • X.δ i.succ

/-- The full boundary is F₀−∂*, including the degree-one boundary.
Source: EM1953 §3 equation (3.6), p.60. -/
theorem boundary_eq_first_sub_positive (X : SimplicialObject C) (n : ℕ) :
    AlgebraicTopology.AlternatingFaceMapComplex.objD X n = X.δ 0 - positiveFaces X n := by
  unfold AlgebraicTopology.AlternatingFaceMapComplex.objD positiveFaces
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ,
    mul_neg, mul_one, neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg]

/-- The initial degeneracy satisfies ∂*D₀=id−D₀∂* in every positive input degree.
Source: EM1953 equation (3.11), p.60. The initial positive-face term is the identity;
all other terms commute past D₀ with opposite sign by the fourth simplicial identity. -/
theorem degeneracyZero_positiveFaces (X : SimplicialObject C) (n : ℕ) :
    X.σ (0 : Fin (n + 2)) ≫ positiveFaces X (n + 1) =
      𝟙 _ - positiveFaces X n ≫ X.σ (0 : Fin (n + 1)) := by
  unfold positiveFaces
  rw [Preadditive.comp_sum, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, Preadditive.comp_zsmul, one_smul,
    Fin.val_succ, pow_succ, mul_neg, mul_one, neg_smul,
    Preadditive.comp_neg, Finset.sum_neg_distrib]
  rw [X.δ_comp_σ_succ]
  rw [Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp, sub_eq_add_neg]
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  exact X.δ_comp_σ_of_gt (j := (0 : Fin (n + 1))) (i := i.succ)
    (by change 0 < i.val + 1; omega)
end HolomorphicAnosov.SimplicialDerivedFaces

namespace HolomorphicAnosov.SimplicialDerivedFaces

/-- Adjoin an initial vertex to an ordinal map, fixing the new vertex and shifting
all old values up. Source: EM1953 §3 pp.58–60, the derived-operator construction. -/
def prependMap {a b : SimplexCategory} (f : a ⟶ b) : ⦋a.len + 1⦌ ⟶ ⦋b.len + 1⦌ :=
  SimplexCategory.mkHom
    ⟨Fin.cases 0 (fun i ↦ (f.toOrderHom i).succ), by
      intro i j hij
      cases i using Fin.cases with
      | zero => simp
      | succ i =>
        cases j using Fin.cases with
        | zero => exact False.elim (by simp at hij)
        | succ j =>
          simpa using f.toOrderHom.monotone (Fin.succ_le_succ_iff.mp hij)⟩

/-- Adjoining an initial vertex is a functor; it therefore preserves every
coefficient identity of composites of ordinal maps. Source: EM1953 (3.5), p.60. -/
def prependFunctor : SimplexCategory ⥤ SimplexCategory where
  obj a := ⦋a.len + 1⦌
  map f := prependMap f
  map_id a := by
    ext i
    cases i using Fin.cases <;> rfl
  map_comp f g := by
    ext i
    cases i using Fin.cases <;> rfl

/-- Derivation raises the index of each face operator by one. -/
theorem prependMap_delta {n : ℕ} (i : Fin (n + 2)) :
    prependMap (SimplexCategory.δ i) = SimplexCategory.δ i.succ := by
  ext j
  cases j using Fin.cases with
  | zero => simp [prependMap, SimplexCategory.δ]
  | succ j => simp [prependMap, SimplexCategory.δ]

/-- Derivation raises the index of each degeneracy operator by one. -/
theorem prependMap_sigma {n : ℕ} (i : Fin (n + 1)) :
    prependMap (SimplexCategory.σ i) = SimplexCategory.σ i.succ := by
  ext j
  cases j using Fin.cases with
  | zero => simp [prependMap, SimplexCategory.σ]
  | succ j => simp [prependMap, SimplexCategory.σ]

/-- Shift a simplicial object along the initial-vertex functor. This implements
EM's derived operators on the actual simplicial object. -/
def derived {C : Type u} [Category.{v} C] (X : SimplicialObject C) : SimplicialObject C :=
  prependFunctor.op ⋙ X

/-- The shifted simplicial faces are the original positive-index faces. -/
theorem derived_delta {C : Type u} [Category.{v} C] (X : SimplicialObject C)
    {n : ℕ} (i : Fin (n + 2)) : (derived X).δ i = X.δ i.succ := by
  change X.map (prependMap (SimplexCategory.δ i)).op = _
  rw [prependMap_delta]
  rfl

/-- For every simplicial object in a preadditive category, let ∂* be the alternating sum F₁−F₂+⋯ of all faces except the initial face. The full boundary is F₀−∂*, and in every positive input degree ∂*D₀=id−D₀∂*. Adjoining an initial vertex to every ordinal map defines an injective-on-morphisms functor which shifts every face and degeneracy index by one. The boundary on the derived simplicial object is the original positive-face operator in degrees at least two, and initial face defines a natural transformation from the derived object to the original.

Source and proof origin: Eilenberg–Mac Lane, On the Groups H(Π,n), I (1953), §3 definition (3.3) p.59; Theorem3.2 equation (3.5), boundary splitting (3.6), face commutations (3.7), and degeneracy identity (3.11), p.60. Supplied original: literature/G2-EM1953-full-supplied.txt and corresponding PDF.

Proof: Split the alternating-face sum into the initial face and the remaining terms, shifting each remaining exponent by one. For ∂*D₀, split off F₁D₀=id. Every remaining face Fᵢ with i>1 commutes past D₀ as D₀Fᵢ₋₁ by the fourth simplicial identity; its exponent changes sign. Summing proves the stated equation without a degree-zero exception hidden in the claim.

For an ordinal map f define f′(0)=0 and f′(i+1)=f(i)+1. Monotonicity holds by separating zero from successor arguments. The identity and composition equations follow by those same two cases. Evaluating at successors recovers f, proving injectivity. Applying this definition to vertex-deletion and vertex-merging maps proves that all face and degeneracy indices increase by one.

Precompose a simplicial object by the opposite initial-vertex functor. Its faces are the original positive-index faces, so its alternating boundary is the positive-face operator in original degree at least two. The equality δ₀f′=fδ₀ on ordinal maps, checked at every vertex, gives the natural initial-face transformation. No equality of ∂* with the zero boundary of original degree one is asserted. -/
theorem derived_boundary {C : Type u} [Category.{v} C] [Preadditive C]
    (X : SimplicialObject C) (n : ℕ) :
    AlgebraicTopology.AlternatingFaceMapComplex.objD (derived X) n = positiveFaces X (n + 1) := by
  simp only [AlgebraicTopology.AlternatingFaceMapComplex.objD, positiveFaces, derived_delta]
  rfl

/-- Derivation is injective on ordinal maps, by evaluation at successor vertices. -/
theorem prependMap_injective {a b : SimplexCategory} :
    Function.Injective (@prependMap a b) := by
  intro f g h
  ext i
  have hh := SimplexCategory.congr_toOrderHom_apply h i.succ
  exact congrArg Fin.val (Fin.succ_injective _ hh)

/-- Deleting the new initial vertex commutes with every derived ordinal map.
Source: EM1953 equation (3.7), p.60. -/
theorem deltaZero_prependMap {a b : SimplexCategory} (f : a ⟶ b) :
    SimplexCategory.δ (0 : Fin (a.len + 2)) ≫ prependMap f =
      f ≫ SimplexCategory.δ (0 : Fin (b.len + 2)) := by
  ext i
  simp [prependMap, SimplexCategory.δ]
  rfl

/-- The shifted simplicial degeneracies have the original index raised by one. -/
theorem derived_sigma {C : Type u} [Category.{v} C] (X : SimplicialObject C)
    {n : ℕ} (i : Fin (n + 1)) : (derived X).σ i = X.σ i.succ := by
  change X.map (prependMap (SimplexCategory.σ i)).op = _
  rw [prependMap_sigma]
  rfl

/-- The initial face is natural from the derived simplicial object to the original.
Source: EM1953 equation (3.7), p.60. -/
def initialFaceTransformation {C : Type u} [Category.{v} C]
    (X : SimplicialObject C) : derived X ⟶ X where
  app a := X.map (SimplexCategory.δ (0 : Fin (a.unop.len + 2))).op
  naturality a b f := by
    change X.map (prependMap f.unop).op ≫ X.map (SimplexCategory.δ _).op =
      X.map (SimplexCategory.δ _).op ≫ X.map f
    rw [← X.map_comp, ← X.map_comp]
    congr 1
end HolomorphicAnosov.SimplicialDerivedFaces
