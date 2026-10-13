import HolomorphicAnosov.Topology.Homology.SignedShuffleChainMap

/-!
# Transposition of the native rational signed shuffle

Source: Hatcher, Algebraic Topology, §3.B pp.277–278; Bredon, Topology and
Geometry, VI §3 pp.324–325. The proof reflects the actual staircase grid paths,
counts the reversed horizontal-vertical pairs, identifies the affine simplices,
and extends the resulting signed identity to the two native free chain modules.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial TensorProduct

namespace HolomorphicAnosov.SignedSingularCrossProduct

/-- Reflect a grid path in the diagonal, exchanging horizontal and vertical steps. -/
def transposePath {p q : ℕ} (w : GridPath p q) : GridPath q p :=
  fun k ↦ (w ⟨k.val, by omega⟩).swap

@[simp] theorem transposePath_transposePath {p q : ℕ} (w : GridPath p q) :
    transposePath (transposePath w) = w := by
  funext k
  rfl

/-- Diagonal reflection carries staircases to staircases by exchanging step types. -/
theorem transposePath_mem {p q : ℕ} (w : GridPath p q) (hw : w ∈ staircases p q) :
    transposePath w ∈ staircases q p := by
  classical
  simp only [staircases, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
  rcases hw with ⟨h0, hl, hs⟩
  refine ⟨?_, ?_, ?_⟩
  · change (w 0).swap = _
    rw [h0]
    rfl
  · change (w ⟨q+p, _⟩).swap = _
    have hi : (⟨q+p, by omega⟩ : Fin (p+q+1)) = Fin.last (p+q) := Fin.ext (Nat.add_comm q p)
    rw [hi, hl]
    rfl
  · intro i
    rcases hs ⟨i.val, by omega⟩ with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact Or.inr ⟨h2,h1⟩
    · exact Or.inl ⟨h2,h1⟩

/-- Reflection and the horizontal-step count show that there are q vertical steps. -/
theorem verticalSteps_card {p q : ℕ} (w : GridPath p q) (hw : w ∈ staircases p q) :
    (Finset.univ.filter (fun i : Fin (p+q) ↦
      (w i.succ).2.val = (w i.castSucc).2.val + 1)).card = q := by
  classical
  apply Eq.trans _ (horizontalSteps_card (transposePath w) (transposePath_mem w hw))
  apply Finset.card_bij (fun i _ ↦ (⟨i.val, by omega⟩ : Fin (q+p)))
  · intro i hi
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
  · intro i hi j hj hij
    exact Fin.ext (congrArg (fun z : Fin (q+p) ↦ z.val) hij)
  · intro i hi
    refine ⟨⟨i.val, by omega⟩, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩

/-- Each horizontal-vertical pair is inverted in exactly one of a staircase and
its transpose; hence their inversion counts sum to the rectangle area. This is
the sign computation in Hatcher §3.B pp.277--278 and Bredon VI §3 pp.324--325. -/
theorem inversionCount_transpose_add {p q : ℕ} (w : GridPath p q)
    (hw : w ∈ staircases p q) : inversionCount w + inversionCount (transposePath w) = p*q := by
  classical
  let V := Finset.univ.filter (fun i : Fin (p+q) ↦
    (w i.succ).2.val = (w i.castSucc).2.val + 1)
  let H := Finset.univ.filter (fun i : Fin (p+q) ↦
    (w i.succ).1.val = (w i.castSucc).1.val + 1)
  have hV : V.card = q := verticalSteps_card w hw
  have hH : H.card = p := horizontalSteps_card w hw
  have hne : ∀ i ∈ V, ∀ j ∈ H, i ≠ j := by
    intro i hi j hj hij
    subst j
    have hs := (Finset.mem_filter.mp hw).2.2.2 i
    simp only [V, H, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    rcases hs with ⟨_, he⟩ | ⟨he, _⟩
    · have hv := congrArg Fin.val he
      omega
    · have hv := congrArg Fin.val he
      omega
  have hleft : ((V ×ˢ H).filter (fun ij ↦ ij.1 < ij.2)).card = inversionCount w := by
    congr 1
    ext ij
    simp only [V,H, Finset.mem_filter, Finset.mem_product,
      Finset.mem_univ, true_and]
    tauto
  have hright : ((V ×ˢ H).filter (fun ij ↦ ¬ij.1 < ij.2)).card =
      inversionCount (transposePath w) := by
    unfold inversionCount
    apply Finset.card_bij (fun ij _ ↦
      ((⟨ij.2.val, by omega⟩ : Fin (q+p)), (⟨ij.1.val, by omega⟩ : Fin (q+p))))
    · intro ij hij
      obtain ⟨hij, hnot⟩ := Finset.mem_filter.mp hij
      obtain ⟨hi,hj⟩ := Finset.mem_product.mp hij
      have hneq := hne ij.1 hi ij.2 hj
      have hlt : ij.2 < ij.1 := lt_of_le_of_ne (le_of_not_gt hnot) (Ne.symm hneq)
      simp only [V,H, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, hj, hi⟩
    · intro ij hij kl hkl heq
      apply Prod.ext <;> apply Fin.ext
      · exact congrArg (fun z ↦ z.2.val) heq
      · exact congrArg (fun z ↦ z.1.val) heq
    · intro ij hij
      obtain ⟨_,hlt,hv,hh⟩ := Finset.mem_filter.mp hij
      refine ⟨(⟨ij.2.val, by omega⟩, ⟨ij.1.val, by omega⟩), ?_, rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩
      · exact not_lt_of_ge hlt.le
  have hc := Finset.card_filter_add_card_filter_not (s := V ×ˢ H) (p := fun ij ↦ ij.1 < ij.2)
  rw [hleft, hright, Finset.card_product, hV,hH, Nat.mul_comm] at hc
  exact hc

end HolomorphicAnosov.SignedSingularCrossProduct

namespace HolomorphicAnosov.SignedSingularCrossProduct

/-- The complementary inversion counts give the Koszul sign under reflection. -/
theorem orientation_transpose {p q : ℕ} (w : GridPath p q) (hw : w ∈ staircases p q) :
    orientation w = (-1 : ℤ)^(p*q) * orientation (transposePath w) := by
  have hc := inversionCount_transpose_add w hw
  rw [← hc, orientation, orientation, pow_add, mul_assoc, ← pow_add]
  simp [← two_mul, pow_mul]

end HolomorphicAnosov.SignedSingularCrossProduct

namespace HolomorphicAnosov.SignedShuffle
open SignedSingularCrossProduct (GridPath staircases transposePath)
open OperatorModel
universe u

/-- Swapping a product simplex is exactly its transposed affine staircase simplex. -/
theorem pushforward_productSimplex_swap (X Y : TopCat.{u}) {p q : ℕ}
    (w : GridPath p q) (σ : Simplex X p) (τ : Simplex Y q) :
    pushforward (⟨Prod.swap, continuous_snd.prodMk continuous_fst⟩ : C(X × Y, Y × X)) (p+q)
      (generator (TopCat.of (X × Y)) (SignedSingularCrossProduct.productSimplex X Y w σ τ)) =
    regrade (TopCat.of (Y × X)) (Nat.add_comm q p)
      (generator (TopCat.of (Y × X))
        (SignedSingularCrossProduct.productSimplex Y X (transposePath w) τ σ)) := by
  rw [pushforward_generator, ← evaluate_gridPath Y X, regrade_evaluate_generator]
  apply congrArg (generator (TopCat.of (Y × X)))
  apply (TopCat.toSSetObjEquiv (TopCat.of (Y × X)) (Opposite.op ⦋p+q⦌)).injective
  rfl

end HolomorphicAnosov.SignedShuffle

namespace HolomorphicAnosov.SignedShuffle
open SignedSingularCrossProduct (GridPath staircases transposePath)
universe u

/-- Transposing every staircase exchanges the inputs. Each of the p horizontal
and q vertical steps reverses relative order, producing the sign (-1)^(p*q).
Source: Hatcher §3.B pp.277--278; Bredon VI §3 pp.324--325. -/
theorem shuffleGenerator_swap (X Y : TopCat.{u}) {p q : ℕ}
    (σ : Simplex X p) (τ : Simplex Y q) :
    pushforward (⟨Prod.swap, continuous_snd.prodMk continuous_fst⟩ : C(X × Y, Y × X)) (p+q)
      (shuffleGenerator X Y σ τ) =
    (-1 : ℚ)^(p*q) • regrade (TopCat.of (Y × X)) (Nat.add_comm q p)
      (shuffleGenerator Y X τ σ) := by
  classical
  unfold shuffleGenerator
  simp only [map_sum, map_smul, Finset.smul_sum]
  apply Finset.sum_bij (fun w _ ↦ transposePath w)
  · intro w hw
    exact SignedSingularCrossProduct.transposePath_mem w hw
  · intro w hw z hz h
    have hh := congrArg transposePath h
    simpa only [SignedSingularCrossProduct.transposePath_transposePath] using hh
  · intro w hw
    exact ⟨transposePath w, SignedSingularCrossProduct.transposePath_mem w hw,
      SignedSingularCrossProduct.transposePath_transposePath w⟩
  · intro w hw
    rw [pushforward_productSimplex_swap, smul_smul]
    congr 1
    exact_mod_cast SignedSingularCrossProduct.orientation_transpose w hw

/-- The native rational signed shuffle is graded commutative under product swap,
with the degree transport q+p=p+q and the Koszul coefficient (-1)^(p*q).
Source: Bredon VI §3 pp.324--325; Hatcher §3.B pp.277--278.

Reflect each finite staircase across the diagonal. This involution exchanges
horizontal and vertical steps, and the two inversion counts add to p*q: every
horizontal-vertical pair belongs to exactly one inversion set. The affine
product simplex after swap is exactly the simplex of the transposed staircase
with inputs reversed and its vertices regraded. Thus termwise signs give the
generator identity. The coproduct universal property extends it linearly in
both native chain variables, including degenerate singular simplices. Empty
spaces and zero degrees require no exception; the same finite-sum proof applies. -/
theorem shuffleBilinear_swap (X Z : TopCat.{u}) (p q : ℕ)
    (a : Chain X p) (b : Chain Z q) :
    (SSet.chainComplexMap (TopCat.toSSet.map
      (TopCat.ofHom ⟨Prod.swap, continuous_snd.prodMk continuous_fst⟩ :
        TopCat.of (X × Z) ⟶ TopCat.of (Z × X)))
      (ModuleCat.of ℚ (ULift.{u} ℚ))).f (p+q) (shuffleBilinear X Z p q a b) =
    (-1 : ℚ)^(p*q) • regrade (TopCat.of (Z × X)) (Nat.add_comm q p)
      (shuffleBilinear Z X q p b a) := by
  let swap : C(↑(TopCat.of (X × Z)), ↑(TopCat.of (Z × X))) := ⟨Prod.swap, continuous_snd.prodMk continuous_fst⟩
  let L := (shuffleBilinear X Z p q).compr₂ (pushforward swap (p+q))
  let R := (-1 : ℚ)^(p*q) •
    ((shuffleBilinear Z X q p).flip.compr₂ (regrade (TopCat.of (Z × X)) (Nat.add_comm q p)))
  have heq : L = R := by
    apply chain_linearMap_ext X p (ModuleCat.of ℚ
      (Chain Z q →ₗ[ℚ] Chain (TopCat.of (Z × X)) (p+q)))
    intro σ
    apply chain_linearMap_ext Z q
    intro τ
    change pushforward swap (p+q)
      (shuffleBilinear X Z p q (generator X σ) (generator Z τ)) =
      (-1 : ℚ)^(p*q) • regrade (TopCat.of (Z × X)) (Nat.add_comm q p)
        (shuffleBilinear Z X q p (generator Z τ) (generator X σ))
    rw [shuffleBilinear_generators, shuffleBilinear_generators]
    exact shuffleGenerator_swap X Z σ τ
  exact LinearMap.congr_fun (LinearMap.congr_fun heq a) b

end HolomorphicAnosov.SignedShuffle
