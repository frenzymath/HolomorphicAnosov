import HolomorphicAnosov.Topology.Homology.SignedShuffleData

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial TensorProduct

namespace HolomorphicAnosov.SignedShuffle

universe u

/-- Evaluation of the tensor lift on native singular generators recovers the prescribed finite sum. -/
theorem shuffle_tmul_generator (X Y : TopCat.{u}) (p q : ℕ)
    (σ : Simplex X p) (τ : Simplex Y q) :
    shuffle X Y p q (generator X σ ⊗ₜ[ℚ] generator Y τ) =
      shuffleGenerator X Y σ τ := by
  simp [shuffle, TensorProduct.lift.tmul, shuffleBilinear, rightLinear, generator,
    SSet.ιChainComplex]


/-- Postcomposition sends a unit singular generator to the postcomposed simplex.
Source: the native singular-set functor and its chain-map generator formula. -/
theorem pushforward_generator {X Y : TopCat.{u}} (f : C(X, Y)) (n : ℕ)
    (σ : Simplex X n) :
    pushforward f n (generator X σ) =
      generator Y ((TopCat.toSSet.map (TopCat.ofHom f)).app (Opposite.op ⦋n⦌) σ) := by
  unfold pushforward generator
  rw [← SSet.ι_chainComplexMap_f]
  rfl

/-- The finite staircase sum commutes term by term with continuous postcomposition.
Source: Hatcher §3.B pp.277–278, the literal affine product formula. -/
theorem shuffleGenerator_naturality (X Y X' Y' : TopCat.{u})
    (f : C(X, X')) (g : C(Y, Y')) (p q : ℕ)
    (σ : Simplex X p) (τ : Simplex Y q) :
    pushforward (f.prodMap g) (p + q) (shuffleGenerator X Y σ τ) =
      shuffleGenerator X' Y'
        ((TopCat.toSSet.map (TopCat.ofHom f)).app (Opposite.op ⦋p⦌) σ)
        ((TopCat.toSSet.map (TopCat.ofHom g)).app (Opposite.op ⦋q⦌) τ) := by
  unfold shuffleGenerator
  simp only [map_sum, map_smul, pushforward_generator]
  congr 1

/-- A rational linear map on native singular chains is determined on unit generators.
Source: the coproduct universal property, with every lifted rational a scalar multiple of one. -/
theorem chain_linearMap_ext (X : TopCat.{u}) (n : ℕ) (M : ModuleCat.{u} ℚ)
    (f g : Chain X n →ₗ[ℚ] M)
    (h : ∀ σ : Simplex X n, f (generator X σ) = g (generator X σ)) : f = g := by
  have hh : ModuleCat.ofHom f = ModuleCat.ofHom g := by
    apply SSet.chainComplex_hom_ext
    intro σ
    apply ModuleCat.hom_ext
    ext r
    have hr : r = r.down • (ULift.up (1 : ℚ) : ULift.{u} ℚ) := by
      ext
      simp
    rw [hr]
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      map_smul, generator] using congrArg (fun z ↦ r.down • z) (h σ)
  exact congrArg ModuleCat.Hom.hom hh

/-- Naturality of the prescribed bilinear shuffle on all ordinary rational chains.
Source: Hatcher §3.B pp.277–278; extend termwise naturality by the two free-module descents. -/
theorem shuffle_naturality (X Y X' Y' : TopCat.{u})
    (f : C(X, X')) (g : C(Y, Y')) (p q : ℕ) (a : Chain X p) (b : Chain Y q) :
    pushforward (f.prodMap g) (p + q) (shuffle X Y p q (a ⊗ₜ[ℚ] b)) =
      shuffle X' Y' p q (pushforward f p a ⊗ₜ[ℚ] pushforward g q b) := by
  let fg : C(↑(TopCat.of (X × Y)), ↑(TopCat.of (X' × Y'))) := f.prodMap g
  let L := (shuffleBilinear X Y p q).compr₂ (pushforward fg (p + q))
  let R := ((shuffleBilinear X' Y' p q).comp (pushforward f p)).compl₂
    (pushforward g q)
  have h : L = R := by
    apply chain_linearMap_ext X p (ModuleCat.of ℚ
      (Chain Y q →ₗ[ℚ] Chain (TopCat.of (X' × Y')) (p + q)))
    intro σ
    apply chain_linearMap_ext Y q
    intro τ
    change pushforward fg (p + q)
      (shuffle X Y p q (generator X σ ⊗ₜ[ℚ] generator Y τ)) =
        shuffle X' Y' p q
          (pushforward f p (generator X σ) ⊗ₜ[ℚ] pushforward g q (generator Y τ))
    rw [shuffle_tmul_generator, pushforward_generator, pushforward_generator,
      shuffle_tmul_generator]
    exact shuffleGenerator_naturality X Y X' Y' f g p q σ τ
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

/-- In degree zero there is one staircase and its product is the ordered pair of points.
Source: Hatcher §3.B pp.277–278, point initialization of the staircase formula. -/
theorem shuffle_point_point (X Y : TopCat.{u}) (x : X) (y : Y) :
    shuffle X Y 0 0 (generator X (pointSimplex X x) ⊗ₜ[ℚ]
      generator Y (pointSimplex Y y)) =
        generator (TopCat.of (X × Y)) (pointSimplex (TopCat.of (X × Y)) (x, y)) := by
  classical
  have hcard : (Finset.univ.filter
      (fun w : SignedSingularCrossProduct.GridPath 0 0 ↦ w 0 = (0, 0))).card = 1 := by
    decide
  simp [shuffle, shuffleBilinear, rightLinear, generator, SSet.ιChainComplex,
    shuffleGenerator, SignedSingularCrossProduct.staircases,
    SignedSingularCrossProduct.orientation, SignedSingularCrossProduct.inversionCount,
    SignedSingularCrossProduct.productSimplex, pointSimplex, hcard]
  rfl

/-- The unique staircase in the `(p,0)` row. -/
theorem right_staircase (p : ℕ) :
    SignedSingularCrossProduct.staircases p 0 = {fun k ↦ (k, 0)} := by
  classical
  ext w
  simp only [SignedSingularCrossProduct.staircases, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨h0, hlast, hstep⟩
    funext k
    apply Prod.ext
    · apply Fin.ext
      induction k using Fin.induction with
      | zero => simpa using congrArg (fun z : Fin (p + 1) × Fin 1 ↦ z.1.val) h0
      | succ i ih =>
        have hs := hstep i
        rcases hs with ⟨hs, _⟩ | ⟨_, hs⟩
        · simpa [ih] using hs
        · have h₁ := (w i.succ).2.isLt
          have h₂ := (w i.castSucc).2.isLt
          omega
    · apply Fin.ext
      omega
  · rintro rfl
    constructor
    · rfl
    constructor
    · rfl
    intro i
    exact Or.inl ⟨rfl, rfl⟩

/-- The unique staircase in the `(0,q)` row gives insertion of a point in the
first factor. Source: Hatcher §3.B pp.277–278. The explicit transport below handles the harmless equality
`0 + q = q` at the simplex index. -/
theorem left_row_point (X Y : TopCat.{u}) (q : ℕ) (x : X) (τ : Simplex Y q) :
    shuffle X Y 0 q (generator X (pointSimplex X x) ⊗ₜ[ℚ] generator Y τ) =
      regrade (TopCat.of (X × Y)) (Nat.zero_add q).symm
        (generator (TopCat.of (X × Y)) (insertLeft X Y x τ)) := by
  classical
  have paths : SignedSingularCrossProduct.staircases 0 q =
      {fun k ↦ (0, Fin.cast (by omega) k)} := by
    ext w
    simp only [SignedSingularCrossProduct.staircases, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨h0, hlast, hstep⟩
      funext k
      apply Prod.ext
      · apply Fin.ext
        omega
      · apply Fin.ext
        induction k using Fin.induction with
        | zero => simpa using congrArg (fun z : Fin 1 × Fin (q + 1) ↦ z.2.val) h0
        | succ i ih =>
          rcases hstep i with ⟨hs, _⟩ | ⟨_, hs⟩
          · have h₁ := (w i.succ).1.isLt
            have h₂ := (w i.castSucc).1.isLt
            omega
          · simpa [ih] using hs
    · rintro rfl
      refine ⟨?_, ?_, ?_⟩
      · rfl
      · apply Prod.ext <;> apply Fin.ext <;> simp
      · intro i
        exact Or.inr ⟨rfl, rfl⟩
  have transport (Z : TopCat.{u}) (n m : ℕ) (h : n = m)
      (σ : C(Convexity.StdSimplex ℝ (Fin (m + 1)), Z)) :
      generator Z ((TopCat.toSSetObjEquiv Z (Opposite.op ⦋n⦌)).symm
        (σ.comp ⟨Convexity.StdSimplex.map (Fin.cast (congrArg (· + 1) h)),
          Convexity.StdSimplex.continuous_map ℝ _⟩)) =
        regrade Z h.symm
          (generator Z ((TopCat.toSSetObjEquiv Z (Opposite.op ⦋m⦌)).symm σ)) := by
    subst m
    have hid : (⟨Convexity.StdSimplex.map (Fin.cast (congrArg (· + 1) (rfl : n = n))),
        Convexity.StdSimplex.continuous_map ℝ _⟩ :
        C(Convexity.StdSimplex ℝ (Fin (n + 1)), _)) = ContinuousMap.id _ := by
      apply ContinuousMap.ext
      intro z
      change Convexity.StdSimplex.map id z = z
      exact Convexity.StdSimplex.map_id z
    rw [hid, ContinuousMap.comp_id]
    rfl
  rw [shuffle_tmul_generator]
  simp only [shuffleGenerator, paths, Finset.sum_singleton]
  simp [SignedSingularCrossProduct.orientation, SignedSingularCrossProduct.inversionCount]
  unfold SignedSingularCrossProduct.productSimplex insertLeft pointSimplex
  simp only [Equiv.apply_symm_apply]
  convert transport (TopCat.of (X × Y)) (0 + q) q (Nat.zero_add q)
    ((ContinuousMap.const _ x).prodMk (TopCat.toSSetObjEquiv Y (Opposite.op ⦋q⦌) τ)) using 1
  congr 2

/-- The left zero-degree row extends point insertion linearly in the other chain.
Source: Hatcher §3.B pp.277–278, the unique staircase in the zero-degree row. -/
theorem left_row_chain (X Y : TopCat.{u}) (q : ℕ) (x : X) (b : Chain Y q) :
    shuffleBilinear X Y 0 q (generator X (pointSimplex X x)) b =
      regrade (TopCat.of (X × Y)) (Nat.zero_add q).symm
        (pushforward ((ContinuousMap.const Y x).prodMk (ContinuousMap.id Y)) q b) := by
  have h := chain_linearMap_ext Y q (ModuleCat.of ℚ (Chain (TopCat.of (X × Y)) (0 + q)))
    (shuffleBilinear X Y 0 q (generator X (pointSimplex X x)))
    ((regrade (TopCat.of (X × Y)) (Nat.zero_add q).symm).comp
      (pushforward ((ContinuousMap.const Y x).prodMk (ContinuousMap.id Y)) q))
    (fun τ => by
      change shuffle X Y 0 q
        (generator X (pointSimplex X x) ⊗ₜ[ℚ] generator Y τ) = _
      rw [left_row_point]
      simp only [LinearMap.comp_apply, pushforward_generator]
      rfl)
  exact LinearMap.congr_fun h b

/-- The unique `(p,0)` staircase inserts a point in the right factor.
Source: Hatcher §3.B pp.277–278. -/
theorem right_row_point (X Y : TopCat.{u}) (p : ℕ) (σ : Simplex X p) (y : Y) :
    shuffle X Y p 0 (generator X σ ⊗ₜ[ℚ] generator Y (pointSimplex Y y)) =
      regrade (TopCat.of (X × Y)) (Nat.add_zero p).symm
        (generator (TopCat.of (X × Y)) (insertRight X Y σ y)) := by
  classical
  simp only [Nat.add_zero]
  have hprod : SignedSingularCrossProduct.productSimplex X Y
      (fun k : Fin (p + 1) => (k, (0 : Fin 1))) σ
      (pointSimplex Y y) = insertRight X Y σ y := by
    apply (TopCat.toSSetObjEquiv (TopCat.of (X × Y))
      (Opposite.op ⦋p⦌)).injective
    simp [SignedSingularCrossProduct.productSimplex, insertRight, pointSimplex]
    congr 1
    · ext z
      change ((TopCat.toSSetObjEquiv X (Opposite.op ⦋p⦌)) σ)
        (Convexity.StdSimplex.map id z) = _
      rw [Convexity.StdSimplex.map_id]
  simp [shuffle, shuffleBilinear, rightLinear, generator,
    SSet.ιChainComplex, shuffleGenerator, right_staircase,
    SignedSingularCrossProduct.orientation,
    SignedSingularCrossProduct.inversionCount, regrade, hprod]

/-- Extend the right point-insertion identity to arbitrary left chains.
Source: Hatcher §3.B pp.277–278, bilinear extension of the unique staircase. -/
theorem right_row_chain (X Y : TopCat.{u}) (p : ℕ) (a : Chain X p) (y : Y) :
    shuffleBilinear X Y p 0 a (generator Y (pointSimplex Y y)) =
      pushforward ((ContinuousMap.id X).prodMk (ContinuousMap.const X y)) p a := by
  have h := chain_linearMap_ext X p (ModuleCat.of ℚ (Chain (TopCat.of (X × Y)) p))
    ((shuffleBilinear X Y p 0).flip (generator Y (pointSimplex Y y)))
    (pushforward ((ContinuousMap.id X).prodMk (ContinuousMap.const X y)) p)
    (fun σ => by
      change shuffle X Y p 0
        (generator X σ ⊗ₜ[ℚ] generator Y (pointSimplex Y y)) = _
      rw [right_row_point, pushforward_generator]
      rfl)
  exact LinearMap.congr_fun h a

/-- The native singular differential commutes with postcomposition. -/
theorem boundary_pushforward {X Y : TopCat.{u}} (f : C(X, Y)) (n : ℕ) (a : Chain X n) :
    boundary Y n (pushforward f n a) = pushforward f (n - 1) (boundary X n a) := by
  exact congrArg (fun k => k.hom a)
    ((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f))
      (ModuleCat.of ℚ (ULift.{u} ℚ))).comm n (n - 1))

/-- Equality of degree indices transports the ordinary differential. -/
theorem boundary_regrade (X : TopCat.{u}) {n m : ℕ} (h : n = m) (a : Chain X n) :
    boundary X m (regrade X h a) =
      regrade X (congrArg (fun k => k - 1) h) (boundary X n a) := by
  subst m
  rfl

/-- The boundary formula for a point in the left factor, by naturality of
ordinary singular chains. Source: EM1953 Theorem 5.2, zero-degree initialization. -/
theorem left_row_boundary_point (X Y : TopCat.{u}) (q : ℕ) (hq : q ≠ 0)
    (x : X) (b : Chain Y q) :
    boundary (TopCat.of (X × Y)) (0 + q)
      (shuffle X Y 0 q (generator X (pointSimplex X x) ⊗ₜ[ℚ] b)) =
      firstBoundaryTerm X Y 0 q (generator X (pointSimplex X x)) b +
      (-1 : ℚ)^0 • secondBoundaryTerm X Y 0 q (generator X (pointSimplex X x)) b := by
  change boundary (TopCat.of (X × Y)) (0 + q)
    (shuffleBilinear X Y 0 q (generator X (pointSimplex X x)) b) = _
  rw [left_row_chain, boundary_regrade, boundary_pushforward]
  simp only [firstBoundaryTerm, secondBoundaryTerm, hq, dite_true, dite_false,
    pow_zero, one_smul, zero_add, left_row_chain]
  have transport (Z : TopCat.{u}) {i j k : ℕ} (h : i = j) (h' : j = k)
      (c : Chain Z i) : regrade Z h' (regrade Z h c) = regrade Z (h.trans h') c := by
    subst j
    subst k
    rfl
  rw [transport]



/-- The shuffle boundary rule when either input has degree zero.
Source: Eilenberg–Mac Lane (1953), Theorem 5.2, pp.66–67. Point insertion is
continuous postcomposition, hence commutes with the singular differential.
Every zero-simplex is a point, and linearity extends the identity to all chains. -/
theorem shuffle_zero_boundary (X Y : TopCat.{u}) (p q : ℕ)
    (hzero : p = 0 ∨ q = 0) (a : Chain X p) (b : Chain Y q) :
    boundary (TopCat.of (X × Y)) (p + q) (shuffle X Y p q (a ⊗ₜ[ℚ] b)) =
      firstBoundaryTerm X Y p q a b + (-1 : ℚ) ^ p • secondBoundaryTerm X Y p q a b := by
  by_cases hp : p = 0
  · subst p
    by_cases hq : q = 0
    · subst q
      simp [boundary, firstBoundaryTerm, secondBoundaryTerm]
    · let L := (boundary (TopCat.of (X × Y)) (0 + q)).comp
        ((shuffleBilinear X Y 0 q).flip b)
      let R := (regrade (TopCat.of (X × Y))
        (by omega : 0 + (q - 1) = 0 + q - 1)).comp
        ((shuffleBilinear X Y 0 (q - 1)).flip (boundary Y q b))
      have h : L = R := by
        apply chain_linearMap_ext X 0
        intro σ
        let x := (TopCat.toSSetObjEquiv X (Opposite.op ⦋0⦌) σ)
          (Convexity.StdSimplex.single (0 : Fin 1))
        have hσ : σ = pointSimplex X x := by
          apply (TopCat.toSSetObjEquiv X (Opposite.op ⦋0⦌)).injective
          ext z
          change (TopCat.toSSetObjEquiv X (Opposite.op ⦋0⦌) σ) z = x
          congr 1
          exact @Subsingleton.elim (Convexity.StdSimplex ℝ (Fin 1)) inferInstance _ _
        rw [hσ]
        simpa only [L, R, LinearMap.comp_apply, LinearMap.flip_apply,
          shuffle, TensorProduct.lift.tmul, firstBoundaryTerm, secondBoundaryTerm,
          hq, dite_true, dite_false, pow_zero, one_smul, zero_add] using
          left_row_boundary_point X Y q hq x b
      simpa only [L, R, LinearMap.comp_apply, LinearMap.flip_apply,
        shuffle, TensorProduct.lift.tmul, firstBoundaryTerm, secondBoundaryTerm,
        hq, dite_true, dite_false, pow_zero, one_smul, zero_add] using
        LinearMap.congr_fun h a
  · by_cases hq : q = 0
    · subst q
      let L := (boundary (TopCat.of (X × Y)) p).comp (shuffleBilinear X Y p 0 a)
      let R := shuffleBilinear X Y (p - 1) 0 (boundary X p a)
      have h : L = R := by
        apply chain_linearMap_ext Y 0
        intro τ
        let y := (TopCat.toSSetObjEquiv Y (Opposite.op ⦋0⦌) τ)
          (Convexity.StdSimplex.single (0 : Fin 1))
        have hτ : τ = pointSimplex Y y := by
          apply (TopCat.toSSetObjEquiv Y (Opposite.op ⦋0⦌)).injective
          ext z
          change (TopCat.toSSetObjEquiv Y (Opposite.op ⦋0⦌) τ) z = y
          congr 1
          exact @Subsingleton.elim (Convexity.StdSimplex ℝ (Fin 1)) inferInstance _ _
        rw [hτ]
        change boundary (TopCat.of (X × Y)) p
          (shuffleBilinear X Y p 0 a (generator Y (pointSimplex Y y))) =
          shuffleBilinear X Y (p - 1) 0 (boundary X p a)
            (generator Y (pointSimplex Y y))
        rw [right_row_chain, right_row_chain, boundary_pushforward]
      simpa [L, R, shuffle, TensorProduct.lift.tmul, firstBoundaryTerm,
        secondBoundaryTerm, hp, regrade] using LinearMap.congr_fun h b
    · simp only [firstBoundaryTerm, secondBoundaryTerm, hp, hq, dite_false]
      exact False.elim (hzero.elim hp hq)

/-- Generator evaluation, naturality, point insertion, and the zero-degree boundary
rule for the rational signed shuffle. Source: Hatcher §3.B pp.277–278 and
Eilenberg–Mac Lane (1953), Theorems 5.1–5.2 pp.65–67. -/
theorem shuffle_basic_laws (X Y : TopCat.{u}) :
    (∀ (p q : ℕ) (σ : Simplex X p) (τ : Simplex Y q),
      shuffle X Y p q (generator X σ ⊗ₜ[ℚ] generator Y τ) =
        shuffleGenerator X Y σ τ) ∧
    (∀ (p q : ℕ) (_hzero : p = 0 ∨ q = 0) (a : Chain X p) (b : Chain Y q),
      boundary (TopCat.of (X × Y)) (p + q) (shuffle X Y p q (a ⊗ₜ[ℚ] b)) =
        firstBoundaryTerm X Y p q a b + (-1 : ℚ) ^ p • secondBoundaryTerm X Y p q a b) ∧
    (∀ (X' Y' : TopCat.{u}) (f : C(X, X')) (g : C(Y, Y'))
      (p q : ℕ) (a : Chain X p) (b : Chain Y q),
      pushforward (f.prodMap g) (p + q) (shuffle X Y p q (a ⊗ₜ[ℚ] b)) =
        shuffle X' Y' p q (pushforward f p a ⊗ₜ[ℚ] pushforward g q b)) ∧
    (∀ (q : ℕ) (x : X) (τ : Simplex Y q),
      shuffle X Y 0 q (generator X (pointSimplex X x) ⊗ₜ[ℚ] generator Y τ) =
        regrade (TopCat.of (X × Y)) (Nat.zero_add q).symm
          (generator (TopCat.of (X × Y)) (insertLeft X Y x τ))) ∧
    (∀ (p : ℕ) (σ : Simplex X p) (y : Y),
      shuffle X Y p 0 (generator X σ ⊗ₜ[ℚ] generator Y (pointSimplex Y y)) =
        regrade (TopCat.of (X × Y)) (Nat.add_zero p).symm
          (generator (TopCat.of (X × Y)) (insertRight X Y σ y))) ∧
    (∀ (x : X) (y : Y),
      shuffle X Y 0 0 (generator X (pointSimplex X x) ⊗ₜ[ℚ]
        generator Y (pointSimplex Y y)) =
          generator (TopCat.of (X × Y)) (pointSimplex (TopCat.of (X × Y)) (x, y))) := by
  exact ⟨shuffle_tmul_generator X Y, shuffle_zero_boundary X Y,
    shuffle_naturality X Y, left_row_point X Y, right_row_point X Y,
    shuffle_point_point X Y⟩

end HolomorphicAnosov.SignedShuffle
