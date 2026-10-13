import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Kronecker evaluation for field chain complexes

Source: Hatcher, *Algebraic Topology*, pp. 191–198, especially Theorem 3.2 and
the field-coefficient specialization on pp. 197–198. This module formalizes
`linear.field_chain_kronecker_evaluation_g3`. Its inputs are actual nonnegative,
unaugmented Mathlib chain complexes. The dual cochain complex is constructed by
precomposition, and homology uses Mathlib's concrete module short-complex homology
data. No dimension or finiteness hypothesis is imposed.

All postponed proofs below are constituent obligations of the same DAG node.
The data of the differentials, quotients, evaluation, and induced maps are explicit.
-/

open CategoryTheory

universe u v

noncomputable section

namespace HolomorphicAnosov.FieldChainKronecker

variable {K : Type u} [Field K]

section ModuleHomology

variable {ι : Type*} {c : ComplexShape ι}

/-- The adjacent short complex at a degree, using Mathlib's zero differential
convention at an endpoint. Source: Hatcher, pp. 191–192 and 197–198. -/
def degreeShortComplex (Q : HomologicalComplex (ModuleCat.{max u v} K) c) (k : ι) :
    ShortComplex (ModuleCat.{max u v} K) :=
  ShortComplex.mk (Q.dTo k) (Q.dFrom k) (Q.dTo_comp_dFrom k)

/-- Cycles are the kernel of the outgoing differential.
Source: Hatcher, pp. 191–192. -/
abbrev cycles (Q : HomologicalComplex (ModuleCat.{max u v} K) c) (k : ι) :
    Submodule K (Q.X k) :=
  LinearMap.ker (Q.dFrom k).hom

/-- Boundaries inside the cycle space, using the actual Mathlib module-homology
construction. Source: Hatcher, pp. 191–192; the inclusion follows from ∂² = 0. -/
abbrev boundaries (Q : HomologicalComplex (ModuleCat.{max u v} K) c) (k : ι) :
    Submodule K (cycles Q k) :=
  (degreeShortComplex Q k).moduleCatToCycles.range

/-- The explicit kernel modulo incoming image from Mathlib's module short-complex
homology data. Source: Hatcher, pp. 191–192. -/
abbrev degreeHomology (Q : HomologicalComplex (ModuleCat.{max u v} K) c) (k : ι) :=
  (degreeShortComplex Q k).moduleCatLeftHomologyData.H

/-- The homology class of a cycle. Source: Hatcher, pp. 191–192. -/
def cycleClass (Q : HomologicalComplex (ModuleCat.{max u v} K) c) (k : ι) :
    cycles Q k →ₗ[K] degreeHomology Q k :=
  (boundaries Q k).mkQ

/-- A chain map sends cycles to cycles.
Source: Hatcher, p. 196, naturality of the universal coefficient map.
Proof: commutation with the differentials gives d(Fz) = F(dz) = 0.
The endpoint differential is zero, so the same calculation covers endpoints. -/
theorem map_cycle_mem {Q R : HomologicalComplex (ModuleCat.{max u v} K) c} (F : Q ⟶ R)
    (k : ι) (z : cycles Q k) : (F.f k).hom z ∈ cycles R k := by
  change (R.dFrom k).hom ((F.f k).hom z) = 0
  have hz : (Q.dFrom k).hom z = 0 := z.property
  have he := ConcreteCategory.congr_hom (F.comm_from k) z.val
  simpa only [ModuleCat.comp_apply, hz, map_zero] using he

/-- The restriction of a complex morphism to cycles.
Source: Hatcher, p. 196; it is the component map with its codomain restricted. -/
def cycleMap {Q R : HomologicalComplex (ModuleCat.{max u v} K) c} (F : Q ⟶ R) (k : ι) :
    cycles Q k →ₗ[K] cycles R k :=
  ((F.f k).hom.domRestrict (cycles Q k)).codRestrict (cycles R k)
    (map_cycle_mem F k)

/-- A complex morphism preserves boundaries inside cycles.
Source: Hatcher, p. 196, naturality.
Proof: an incoming boundary has the form dx; its image is F(dx) = d(Fx),
again an incoming boundary. The equality also identifies the cycle subtypes,
whose proof components are irrelevant. Thus the stated submodule inclusion holds. -/
theorem map_boundary_mem {Q R : HomologicalComplex (ModuleCat.{max u v} K) c} (F : Q ⟶ R)
    (k : ι) : boundaries Q k ≤ (boundaries R k).comap (cycleMap F k) := by
  rintro z ⟨x, rfl⟩
  refine ⟨(F.prev k).hom x, ?_⟩
  apply Subtype.ext
  exact ConcreteCategory.congr_hom (F.comm_to k) x

/-- The actual induced map on the kernel/image quotient.
Source: Hatcher, p. 196; it sends the class of z to the class of Fz. -/
def degreeHomologyMap {Q R : HomologicalComplex (ModuleCat.{max u v} K) c} (F : Q ⟶ R)
    (k : ι) : degreeHomology Q k →ₗ[K] degreeHomology R k :=
  (boundaries Q k).mapQ (boundaries R k) (cycleMap F k) (map_boundary_mem F k)

end ModuleHomology

variable (C : ChainComplex (ModuleCat.{max u v} K) ℕ)

/-- The laws required for the concrete dual differential.
Source: Hatcher, pp. 191–192 and 197–198.
Proof: the up-shape relation i + 1 = j is the down-shape relation for (j,i).
Outside it, the original differential is zero, so its transpose is zero.
Two successive transposes compose as the transpose of the reversed composite;
the chain-complex square-zero identity makes that composite zero. -/
theorem dual_complex_laws :
    (∀ i j, ¬(ComplexShape.up ℕ).Rel i j →
      ModuleCat.ofHom (C.d j i).hom.dualMap = 0) ∧
    (∀ i j k, (ComplexShape.up ℕ).Rel i j → (ComplexShape.up ℕ).Rel j k →
      ModuleCat.ofHom (C.d j i).hom.dualMap ≫
        ModuleCat.ofHom (C.d k j).hom.dualMap = 0) := by
  constructor
  · intro i j hij
    have hz : C.d j i = 0 := C.shape j i hij
    rw [hz]
    ext a x
    simp
  · intro i j k _ _
    ext a x
    change a ((C.d j i).hom ((C.d k j).hom x)) = 0
    have he := ConcreteCategory.congr_hom (C.d_comp_d k j i) x
    rw [show (C.d j i).hom ((C.d k j).hom x) = 0 from he]
    exact a.map_zero

/-- The genuine dual cochain complex: its degree-k space is Hom_K(C_k,K), and
its differential sends a to a composed with ∂. Source: Hatcher, pp. 197–198. -/
def dualComplex : CochainComplex (ModuleCat.{max u v} K) ℕ where
  X k := ModuleCat.of K (Module.Dual K (C.X k))
  d i j := ModuleCat.ofHom (C.d j i).hom.dualMap
  shape := (dual_complex_laws C).1
  d_comp_d' := (dual_complex_laws C).2

/-- Cohomology is the homology of the actual dual cochain complex.
Source: Hatcher, pp. 197–198. -/
abbrev cohomology (k : ℕ) := degreeHomology (dualComplex C) k

/-- A chain map transposes to a cochain map.
Source: Hatcher, p. 196 and the induced cochain-map construction on pp. 199–200.
Proof: F_i composed with ∂_D equals ∂_C composed with F_j. Transpose this
identity: precomposition reverses composition. The resulting identity is exactly
the cochain-map square; zero differentials handle indices outside the shape. -/
theorem dual_map_comm {D : ChainComplex (ModuleCat.{max u v} K) ℕ} (F : C ⟶ D)
    (i j : ℕ) :
    ModuleCat.ofHom (F.f i).hom.dualMap ≫ (dualComplex C).d i j =
      (dualComplex D).d i j ≫ ModuleCat.ofHom (F.f j).hom.dualMap := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro x
  change a ((F.f i).hom ((C.d j i).hom x)) = a ((D.d j i).hom ((F.f j).hom x))
  exact congrArg a (ConcreteCategory.congr_hom (F.comm j i) x).symm

/-- The concrete contravariant map of dual cochain complexes.
Source: Hatcher, pp. 196 and 199–200; its components are a ↦ a ∘ F_k. -/
def dualMap {D : ChainComplex (ModuleCat.{max u v} K) ℕ} (F : C ⟶ D) :
    dualComplex D ⟶ dualComplex C where
  f k := ModuleCat.ofHom (F.f k).hom.dualMap
  comm' i j _ := dual_map_comm C F i j

/-- The induced pullback on dual cohomology.
Source: Hatcher, pp. 196 and 199–200. -/
def cohomologyMap {D : ChainComplex (ModuleCat.{max u v} K) ℕ} (F : C ⟶ D) (k : ℕ) :
    cohomology D k →ₗ[K] cohomology C k :=
  degreeHomologyMap (dualMap C F) k

/-- Restrict a cocycle functional to the cycle subspace.
Source: Hatcher, pp. 191–192, evaluation construction. -/
def cycleFunctional (k : ℕ) (a : cycles (dualComplex C) k) : cycles C k →ₗ[K] K :=
  a.val.comp (cycles C k).subtype

/-- A cocycle functional kills chain boundaries.
Source: Hatcher, pp. 191–192 and 198.
Proof: a boundary is ∂x, and the cocycle identity says a ∘ ∂ = 0. Hence
a(∂x) = 0, which is precisely membership in the kernel of the restriction. -/
theorem cycleFunctional_kills_boundaries (k : ℕ) (a : cycles (dualComplex C) k) :
    boundaries C k ≤ LinearMap.ker (cycleFunctional C k a) := by
  rintro z ⟨x, rfl⟩
  change (DFunLike.coe (F := Module.Dual K (C.X k)) a.val) ((C.dTo k).hom x) = 0
  have ha : ((dualComplex C).dFrom k).hom a.val = 0 := a.property
  change (C.d ((ComplexShape.up ℕ).next k) k).hom.dualMap a.val = 0 at ha
  rw [CochainComplex.next] at ha
  rw [C.dTo_eq (show (ComplexShape.down ℕ).Rel (k + 1) k from rfl)]
  exact LinearMap.congr_fun ha _

/-- Descend the restricted functional to homology by the quotient universal
property. Source: Hatcher, pp. 191–192; on a cycle class it has value a(z). -/
def cocycleEvaluation (k : ℕ) (a : cycles (dualComplex C) k) :
    Module.Dual K (degreeHomology C k) :=
  (boundaries C k).liftQ (cycleFunctional C k a)
    (cycleFunctional_kills_boundaries C k a)

/-- Cocycle evaluation is linear in the cocycle.
Source: Hatcher, pp. 191–192.
Proof: on a class represented by z, (a+b)(z) = a(z)+b(z) and (r a)(z) = r a(z).
Every homology class has a cycle representative. Extensionality of functionals
and surjectivity of the quotient map therefore give both equalities. -/
theorem cocycleEvaluation_linear (k : ℕ) :
    (∀ a b : cycles (dualComplex C) k,
      cocycleEvaluation C k (a + b) = cocycleEvaluation C k a + cocycleEvaluation C k b) ∧
    (∀ (r : K) (a : cycles (dualComplex C) k),
      cocycleEvaluation C k (r • a) = r • cocycleEvaluation C k a) := by
  constructor
  · intro a b
    apply (boundaries C k).quot_hom_ext
    intro z
    rfl
  · intro r a
    apply (boundaries C k).quot_hom_ext
    intro z
    rfl

/-- Evaluation as a linear map on the space of cocycles.
Source: Hatcher, pp. 191–192; data are the descended restriction functionals. -/
def cocycleEvaluationMap (k : ℕ) :
    cycles (dualComplex C) k →ₗ[K] Module.Dual K (degreeHomology C k) where
  toFun := cocycleEvaluation C k
  map_add' := (cocycleEvaluation_linear C k).1
  map_smul' := (cocycleEvaluation_linear C k).2

/-- Coboundaries evaluate to zero on cycles.
Source: Hatcher, pp. 191–192.
Proof: a positive-degree coboundary is b ∘ ∂ and z is a cycle, so b(∂z) = b(0) = 0.
There are no degree-zero coboundaries because the incoming differential in the
nonnegative dual complex is zero. Surjectivity of cycleClass then shows the
descended functional is zero, proving the kernel inclusion. -/
theorem cocycleEvaluationMap_kills_coboundaries (k : ℕ) :
    boundaries (dualComplex C) k ≤ LinearMap.ker (cocycleEvaluationMap C k) := by
  rintro a ⟨b, rfl⟩
  apply (boundaries C k).quot_hom_ext
  intro z
  change (DFunLike.coe (F := Module.Dual K (C.X ((ComplexShape.up ℕ).prev k))) b)
    ((C.d k ((ComplexShape.up ℕ).prev k)).hom z.val) = 0
  have hz (j : ℕ) : (C.d k j).hom z.val = 0 := by
    by_cases h : (ComplexShape.down ℕ).Rel k j
    · have he := ConcreteCategory.congr_hom (C.dFrom_comp_xNextIso h) z.val
      have hz' : (C.dFrom k).hom z.val = 0 := z.property
      simpa only [ModuleCat.comp_apply, hz', map_zero] using he.symm
    · rw [C.shape k j h]
      rfl
  rw [hz]
  exact (show Module.Dual K (C.X ((ComplexShape.up ℕ).prev k)) from b).map_zero

/-- The concrete Kronecker evaluation map, obtained by descending evaluation
through both quotients. Source: Hatcher, pp. 191–193. -/
def evaluation (k : ℕ) : cohomology C k →ₗ[K] Module.Dual K (degreeHomology C k) :=
  (boundaries (dualComplex C) k).liftQ (cocycleEvaluationMap C k)
    (cocycleEvaluationMap_kills_coboundaries C k)

/-- Evaluation is bijective over an arbitrary field, with no finiteness assumption.
Source: Hatcher, Theorem 3.2 p. 195 and field specialization pp. 197–198;
the node's subspace-extension proof uses Mathlib `LinearMap.exists_extend`.
Proof: for a homology functional λ, pull back to the cycle subspace along the
quotient map and extend to C_k. This extension kills boundaries and is a cocycle;
its evaluation is λ, proving surjectivity. If evaluation of a cocycle a is zero,
a kills every cycle. In positive degree define b on im ∂_k by b(∂_k x) = a(x).
Two lifts differ by a cycle, so b is well-defined and linear. Extend b to C_(k-1);
then a = b ∘ ∂_k is a coboundary and its cohomology class is zero. In degree zero
all chains are cycles, so a itself is zero. This proves injectivity. Extension of
subspace functionals works for arbitrary vector spaces and needs no finite basis. -/
theorem evaluation_bijective (k : ℕ) : Function.Bijective (evaluation C k) := by
  classical
  constructor
  · apply LinearMap.ker_eq_bot.mp
    change LinearMap.ker ((boundaries (dualComplex C) k).liftQ _ _) = ⊥
    apply Submodule.ker_liftQ_eq_bot
    intro a ha
    have haz (z : cycles C k) :
        (DFunLike.coe (F := Module.Dual K (C.X k)) a.val) z.val = 0 :=
      LinearMap.congr_fun ha (cycleClass C k z)
    cases k with
    | zero =>
      have ha0 : a = 0 := by
        apply Subtype.ext
        apply LinearMap.ext
        intro x
        have hx : x ∈ cycles C 0 := by
          change (C.d 0 ((ComplexShape.down ℕ).next 0)).hom x = 0
          rw [ChainComplex.next_nat_zero, C.shape 0 0 (by simp)]
          rfl
        exact haz ⟨x, hx⟩
      rw [ha0]
      exact Submodule.zero_mem _
    | succ k =>
      let d := (C.d (k + 1) k).hom
      have hker : LinearMap.ker d ≤ LinearMap.ker a.val := by
        intro x hx
        have hx' : x ∈ cycles C (k + 1) := by
          change (C.d (k + 1) ((ComplexShape.down ℕ).next (k + 1))).hom x = 0
          rw [ChainComplex.next_nat_succ]
          exact hx
        exact haz ⟨x, hx'⟩
      let b₀ : LinearMap.range d →ₗ[K] K :=
        ((LinearMap.ker d).liftQ a.val hker).comp d.quotKerEquivRange.symm.toLinearMap
      obtain ⟨b, hb⟩ := b₀.exists_extend
      have hba : d.dualMap b = a.val := by
        apply LinearMap.ext
        intro x
        have he := LinearMap.congr_fun hb (⟨d x, LinearMap.mem_range_self d x⟩)
        dsimp [b₀] at he
        rw [LinearMap.quotKerEquivRange_symm_apply_image] at he
        exact he
      change a ∈ LinearMap.range (degreeShortComplex (dualComplex C) (k + 1)).moduleCatToCycles
      let r : (ComplexShape.up ℕ).Rel k (k + 1) := rfl
      refine ⟨((dualComplex C).xPrevIso r).inv b, ?_⟩
      apply Subtype.ext
      have he := ConcreteCategory.congr_hom ((dualComplex C).xPrevIso_comp_dTo r) b
      exact he.trans hba
  · intro φ
    obtain ⟨a, ha⟩ := (φ.comp (cycleClass C k)).exists_extend
    have hac : a ∈ cycles (dualComplex C) k := by
      change (C.d ((ComplexShape.up ℕ).next k) k).hom.dualMap a = 0
      rw [CochainComplex.next]
      apply LinearMap.ext
      intro x
      let r : (ComplexShape.down ℕ).Rel (k + 1) k := rfl
      let x' := (C.xPrevIso r).inv x
      let z := (degreeShortComplex C k).moduleCatToCycles x'
      have hz : z ∈ boundaries C k := LinearMap.mem_range_self _ x'
      have hclass : cycleClass C k z = 0 := (Submodule.Quotient.mk_eq_zero (boundaries C k)).mpr hz
      have he := LinearMap.congr_fun ha z
      change a z.val = φ (cycleClass C k z) at he
      rw [hclass, map_zero] at he
      have hzx : z.val = (C.d (k + 1) k).hom x := by
        exact ConcreteCategory.congr_hom (C.xPrevIso_comp_dTo r) x
      change a ((C.d (k + 1) k).hom x) = 0
      rw [← hzx]
      exact he
    refine ⟨cycleClass (dualComplex C) k ⟨a, hac⟩, ?_⟩
    apply (boundaries C k).quot_hom_ext
    intro z
    exact LinearMap.congr_fun ha z


/-- The natural linear equivalence, whose forward map is the explicit evaluation
map and whose inverse is supplied by its bijectivity proof.
Source: Hatcher, pp. 191–198. -/
noncomputable def evaluationEquiv (k : ℕ) :
    cohomology C k ≃ₗ[K] Module.Dual K (degreeHomology C k) :=
  LinearEquiv.ofBijective (evaluation C k) (evaluation_bijective C k)

/-- The representative formula for the actual equivalence.
Source: Hatcher, pp. 191–192.
Proof: both quotient lifts agree with their defining maps on quotient classes.
Unfold the equivalence's forward map, the cohomology lift, the homology lift,
and the restriction: the resulting scalar is exactly the original a applied to z. -/
theorem evaluation_representative (k : ℕ) (a : cycles (dualComplex C) k)
    (z : cycles C k) :
    evaluationEquiv C k (cycleClass (dualComplex C) k a) (cycleClass C k z) =
      DFunLike.coe (F := Module.Dual K (C.X k)) a.val z.val := by
  rfl

/-- Naturality of evaluation for every chain map and every cohomology and homology
class. Source: Hatcher, p. 196.
Proof: choose a cocycle a and a cycle z representing the two classes. The induced
maps represent their images by a ∘ F_k and F_k z. The representative formula on
each side gives (a ∘ F_k)(z) = a(F_k z), a definitional equality. Both quotient
maps are surjective, so this equality holds for arbitrary classes. -/
theorem evaluation_naturality {D : ChainComplex (ModuleCat.{max u v} K) ℕ} (F : C ⟶ D)
    (k : ℕ) (a : cohomology D k) (z : degreeHomology C k) :
    evaluationEquiv C k (cohomologyMap C F k a) z =
      evaluationEquiv D k a (degreeHomologyMap F k z) := by
  obtain ⟨a, rfl⟩ := (boundaries (dualComplex D) k).mkQ_surjective a
  obtain ⟨z, rfl⟩ := (boundaries C k).mkQ_surjective z
  rfl

/-- Explicit unaugmented degree-zero conventions.
Source: Hatcher, pp. 197–198.
Proof: there is no allowed down-shape arrow leaving zero or up-shape arrow
entering zero. Mathlib's endpoint differentials are consequently zero. The kernel
of the zero outgoing map is all of C_0, and the range of the zero incoming map
in the dual complex is the zero subspace. No negative cochain space is introduced. -/
theorem zero_degree_conventions :
    cycles C 0 = ⊤ ∧ boundaries (dualComplex C) 0 = ⊥ := by
  constructor
  · apply Submodule.eq_top_iff'.mpr
    intro z
    change (C.dFrom 0).hom z = 0
    change (C.d 0 ((ComplexShape.down ℕ).next 0)).hom z = 0
    rw [ChainComplex.next_nat_zero]
    rw [C.shape 0 0 (by simp)]
    rfl
  · apply le_antisymm ?_ bot_le
    rintro a ⟨b, rfl⟩
    change (⟨((dualComplex C).dTo 0).hom b, _⟩ : cycles (dualComplex C) 0) = 0
    apply Subtype.ext
    have hz : (dualComplex C).dTo 0 = 0 := by
      apply HomologicalComplex.dTo_eq_zero
      simp [CochainComplex.prev_nat_zero]
    change ((dualComplex C).dTo 0).hom b = 0
    rw [hz]
    rfl

/-- The complete arbitrary-field Kronecker evaluation statement.
Source: Hatcher, evaluation pp. 191–193, Theorem 3.2 p. 195, naturality p. 196,
and field specialization pp. 197–198; DAG node
`linear.field_chain_kronecker_evaluation_g3`.
Proof: cocycles kill boundaries and coboundaries kill cycles, so restriction and
the two quotient universal properties give the displayed evaluation map. A
homology functional pulls back to cycles and extends to all chains, giving
surjectivity. A cocycle with zero evaluation kills cycles, hence in positive
degree factors through the image of the outgoing differential; extend that
functional to the previous chain group to exhibit a coboundary. In degree zero
all chains are cycles, so the cocycle is zero. This proves bijectivity without
finite dimension. The two quotient lifts give the representative formula.
For a chain map F, the two induced representatives are a composed with F_k and
F_k z; their evaluations agree by (a composed with F_k)(z) = a(F_k z).
Surjectivity of the quotient maps gives naturality for arbitrary classes. -/
theorem field_chain_kronecker_evaluation (k : ℕ) :
    Function.Bijective (evaluation C k) ∧
    (∀ (a : cycles (dualComplex C) k) (z : cycles C k),
      evaluationEquiv C k (cycleClass (dualComplex C) k a) (cycleClass C k z) =
        DFunLike.coe (F := Module.Dual K (C.X k)) a.val z.val) ∧
    (∀ (D : ChainComplex (ModuleCat.{max u v} K) ℕ) (F : C ⟶ D)
      (a : cohomology D k) (z : degreeHomology C k),
      evaluationEquiv C k (cohomologyMap C F k a) z =
        evaluationEquiv D k a (degreeHomologyMap F k z)) := by
  exact ⟨evaluation_bijective C k, evaluation_representative C k,
    fun D F a z ↦ evaluation_naturality C F k a z⟩


end HolomorphicAnosov.FieldChainKronecker
