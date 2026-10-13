import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.CoordinateCycle
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.AdditivePositiveLoop
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import HolomorphicAnosov.Topology.PathSingularSimplexMap
import HolomorphicAnosov.Topology.PathTransSingularTriangle
import HolomorphicAnosov.Topology.PathHomotopySingularTriangles
import HolomorphicAnosov.Topology.ModuleCatCycleClassEqOfBoundary
import HolomorphicAnosov.Topology.ModuleCatCycleClassEqZero
import HolomorphicAnosov.Topology.ModuleCatCycleClassNaturality
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.GroupTheory.Abelianization.Defs

noncomputable section
open CategoryTheory AlgebraicTopology
open scoped Simplicial
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
namespace HolomorphicAnosov.RationalSingularH1G3
open HolomorphicAnosov.Topology _root_.Topology


/-- Ordinary rational singular chains, with the rational coefficient module.
Source: Hatcher, pp. 108–109; the body is Mathlib's singular-set chain complex. -/
abbrev chains (X : Type) [TopologicalSpace X] :
    ChainComplex (ModuleCat ℚ) ℕ :=
  (TopCat.toSSet.obj (TopCat.of X)).chainComplex (ModuleCat.of ℚ (ℚ))




/-- The additive module of ordinary rational singular homology in degree one.
Source: Hatcher, p. 108; this is the native homology object of the above complex. -/
abbrev H1 (X : Type) [TopologicalSpace X] : Type :=
  (chains X).homology 1




/-- The ordinary singular H1 map of an actual continuous map.
Source: Hatcher, p. 168; the body is the native singular homology functor. -/
def homologyMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (g : C(X, Y)) : H1 X →ₗ[ℚ] H1 Y :=
  (((singularHomologyFunctor (ModuleCat ℚ) 1).obj
    (ModuleCat.of ℚ (ℚ))).map (TopCat.ofHom g)).hom




/-- A one-simplex with equal endpoint faces has zero boundary, for every coefficient.
Source: Hatcher, Algebraic Topology, Theorem 2A.1 p.166; this is the degree-one
alternating face differential and does not require the simplicial set to be singular. -/
theorem simplicial_one_simplex_isCycle
    (X : SSet) (R : ModuleCat ℚ) (s : X _⦋1⦌) (hs : X.δ 0 s = X.δ 1 s) (r : R) :
    (X.ιChainComplex (R := R) s).hom r ∈
      LinearMap.ker ((X.chainComplex R).sc 1).g.hom := by
  change ((X.chainComplex R).sc 1).g.hom ((X.ιChainComplex (R := R) s).hom r) = 0
  dsimp +instances only [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
    HomologicalComplex.shortComplexFunctor']
  change ((X.chainComplex R).d 1 ((ComplexShape.down ℕ).next 1)).hom
    ((X.ιChainComplex (R := R) s).hom r) =
      (0 : (X.chainComplex R).X ((ComplexShape.down ℕ).next 1))
  rw [ComplexShape.next_eq' (ComplexShape.down ℕ) (show (ComplexShape.down ℕ).Rel 1 0 from rfl)]
  have h := X.ιChainComplex_d (R := R) s
  have hzero : X.ιChainComplex (R := R) s ≫ (X.chainComplex R).d 1 0 = 0 := by
    rw [h]
    simp [Fin.sum_univ_two, hs]
  exact congrArg (fun f ↦ f.hom r) hzero




/-- Two triangles with a common diagonal and equal outer side edges have boundary
 equal to the difference of the other two edges.
Source: Hatcher, Algebraic Topology, Theorem 2A.1, p.166, homotopy square.
Proof: expand both alternating face sums. The two diagonal terms and the two
side-edge terms cancel; the remaining terms are the specified outer edges. -/
theorem simplicial_two_triangle_boundary
    (X : SSet) (R : ModuleCat ℚ) (s t : X _⦋2⦌)
    (hside : X.δ 0 s = X.δ 2 t) (hdiag : X.δ 1 s = X.δ 1 t) (r : R) :
    ((X.chainComplex R).d 2 1)
      ((X.ιChainComplex (R := R) s) r - (X.ιChainComplex (R := R) t) r) =
        (X.ιChainComplex (R := R) (X.δ 2 s)) r -
          (X.ιChainComplex (R := R) (X.δ 0 t)) r := by
  have hs := congrArg (fun f ↦ f.hom r) (X.ιChainComplex_d (R := R) s)
  have ht := congrArg (fun f ↦ f.hom r) (X.ιChainComplex_d (R := R) t)
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hs ht
  simp only [ModuleCat.comp_apply, ModuleCat.hom_add, ModuleCat.hom_zsmul,
    LinearMap.add_apply] at hs ht
  simp only [map_sub]
  change ((X.chainComplex R).d 2 1).hom ((X.ιChainComplex (R := R) s).hom r) -
    ((X.chainComplex R).d 2 1).hom ((X.ιChainComplex (R := R) t).hom r) = _
  rw [hs, ht]
  simp [hside, hdiag]
  abel




/-- The finite rational singular chain with coefficient one on the path simplex.
Source: Hatcher, pp. 108–109 and 166; this is the native coproduct generator. -/
def pathSingularChain {X : Type} [TopologicalSpace X] {a b : X} (α : Path a b) :
    (chains X).X 1 :=
  ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
    (R := ModuleCat.of ℚ (ℚ)) (pathSingularSimplex α)).hom 1




/-- A based loop is an actual degree-one cycle.

Source and proof: Hatcher, Theorem 2A.1, p. 166. The alternating face
differential of a one-simplex is its zeroth face minus its first face.
The interval equivalence identifies these with the endpoint and starting
point, respectively. Both endpoints of a based loop are the same point,
so the two native rational-one generators cancel. This is membership in
the actual kernel of the native differential, not a supplied cycle. -/
theorem loopSingularChain_isCycle {X : Type} [TopologicalSpace X]
    {x : X} (α : Path x x) :
    pathSingularChain α ∈ LinearMap.ker ((chains X).sc 1).g.hom  := by
  refine simplicial_one_simplex_isCycle (TopCat.toSSet.obj (TopCat.of X))
    (ModuleCat.of ℚ (ℚ)) (pathSingularSimplex α) ?_ 1
  simp only [pathSingularSimplex, TopCat.δ_zero_toSSetObj₁Equiv.symm,
    TopCat.δ_one_toSSetObj₁Equiv.symm]
  exact congrArg TopCat.toSSetObj₀Equiv.symm
    (((TopCat.pathEquiv (X := TopCat.of X)).symm α).hom₁.trans
      ((TopCat.pathEquiv (X := TopCat.of X)).symm α).hom₀.symm)




/-- The loop cycle projected to native ordinary singular homology.
Source: Hatcher, p. 166. Only its cycle proof is postponed; the cycle
data, kernel-to-native-cycles isomorphism, and quotient projection are explicit. -/
def loopSingularClass {X : Type} [TopologicalSpace X] {x : X} (α : Path x x) :
    H1 X :=
  (chains X).homologyπ 1
    (((chains X).sc 1).moduleCatCyclesIso.inv
      ⟨pathSingularChain α, loopSingularChain_isCycle α⟩)




/-- The sum of two composable path chains minus their concatenation is a boundary.
Source: Hatcher, Algebraic Topology, Theorem 2A.1 proof p.166. The concatenation
triangle has ordered faces second path, concatenation, first path. Apply the
native alternating face differential and reorder its three terms. -/
theorem pathTrans_singular_boundary {X : Type} [TopologicalSpace X]
    {x y z : X} (α : Path x y) (β : Path y z) :
    ∃ c : (chains X).X 2,
      ((chains X).d 2 1) c =
        pathSingularChain α + pathSingularChain β - pathSingularChain (α.trans β) := by
  obtain ⟨s, h0, h1, h2⟩ := pathTrans_singular_triangle α β
  let Y := TopCat.toSSet.obj (TopCat.of X)
  let R := ModuleCat.of ℚ (ℚ)
  refine ⟨(Y.ιChainComplex (R := R) s) (1 : R), ?_⟩
  have hb := congrArg (fun f ↦ f.hom (1 : R)) (Y.ιChainComplex_d (R := R) s)
  change ((Y.chainComplex R).d 2 1).hom ((Y.ιChainComplex (R := R) s).hom 1) = _ at hb
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hb
  change ((Y.chainComplex R).d 2 1).hom ((Y.ιChainComplex (R := R) s).hom 1) = _
  rw [hb]
  simp [Y, h0, h1, h2, pathSingularChain, R]
  abel




/-- Concatenation of based loops adds their native singular homology classes.
Source: Hatcher, Algebraic Topology, Theorem 2A.1 proof p.166. The concatenation
triangle bounds the sum of the loop chains minus the concatenation chain.
The native homology projection is linear, so equality modulo this boundary
gives the displayed addition law. -/
theorem loopSingularClass_trans {X : Type} [TopologicalSpace X]
    {x : X} (α β : Path x x) :
    loopSingularClass (α.trans β) = loopSingularClass α + loopSingularClass β := by
  obtain ⟨c, hc⟩ := pathTrans_singular_boundary α β
  have hex : ∃ c' : ((chains X).sc 1).X₁,
      ((chains X).sc 1).f c' =
        pathSingularChain α + pathSingularChain β - pathSingularChain (α.trans β) := by
    dsimp +instances only [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
      HomologicalComplex.shortComplexFunctor']
    rw [ComplexShape.prev_eq' (ComplexShape.down ℕ)
      (show (ComplexShape.down ℕ).Rel 2 1 from rfl)]
    exact ⟨c, hc⟩
  obtain ⟨c', hc'⟩ := hex
  let a : LinearMap.ker ((chains X).sc 1).g.hom :=
    ⟨pathSingularChain α, loopSingularChain_isCycle α⟩
  let b : LinearMap.ker ((chains X).sc 1).g.hom :=
    ⟨pathSingularChain β, loopSingularChain_isCycle β⟩
  have h := moduleCat_cycleClass_eq_of_boundary ((chains X).sc 1)
    (a + b) ⟨pathSingularChain (α.trans β), loopSingularChain_isCycle _⟩ c' hc'
  change _ = loopSingularClass (α.trans β) at h
  change ((chains X).sc 1).homologyπ.hom
    (((chains X).sc 1).moduleCatCyclesIso.inv.hom
      ((a : ((chains X).sc 1).moduleCatLeftHomologyData.K) + b)) = _ at h
  have hi := ((chains X).sc 1).moduleCatCyclesIso.inv.hom.map_add a b
  have hp := ((chains X).sc 1).homologyπ.hom.map_add
    (((chains X).sc 1).moduleCatCyclesIso.inv a)
    (((chains X).sc 1).moduleCatCyclesIso.inv b)
  exact h.symm.trans ((congrArg
    (fun z ↦ ((chains X).sc 1).homologyπ.hom z) hi).trans hp)




/-- Endpoint-fixed homotopies of loops preserve their native singular classes.

Source and proof: Hatcher, Theorem 2A.1, p.166. Triangulate the homotopy
square by its diagonal. The two singular triangles have equal diagonal
faces. Their side faces are both the constant basepoint since the loops
have the same basepoint. Thus their difference has boundary exactly the
initial loop minus the final loop. The native module homology quotient
identifies these two cycle classes. -/
theorem loopSingularClass_homotopic {X : Type} [TopologicalSpace X]
    {x : X} {α β : Path x x} (h : α.Homotopic β) :
    loopSingularClass α = loopSingularClass β := by
  obtain ⟨H⟩ := h
  obtain ⟨s, t, hside, hdiag, hs, ht⟩ := pathHomotopy_singular_triangles H
  let Y := TopCat.toSSet.obj (TopCat.of X)
  let R := ModuleCat.of ℚ (ℚ)
  let c := (Y.ιChainComplex (R := R) s) (1 : R) -
    (Y.ιChainComplex (R := R) t) (1 : R)
  have hb := simplicial_two_triangle_boundary Y R s t hside hdiag (1 : R)
  rw [hs, ht] at hb
  have hex : ∃ c' : ((chains X).sc 1).X₁,
      ((chains X).sc 1).f c' = pathSingularChain α - pathSingularChain β := by
    dsimp +instances only [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
      HomologicalComplex.shortComplexFunctor']
    rw [ComplexShape.prev_eq' (ComplexShape.down ℕ)
      (show (ComplexShape.down ℕ).Rel 2 1 from rfl)]
    exact ⟨c, hb⟩
  obtain ⟨c', hc'⟩ := hex
  exact moduleCat_cycleClass_eq_of_boundary ((chains X).sc 1)
    ⟨pathSingularChain α, loopSingularChain_isCycle α⟩
    ⟨pathSingularChain β, loopSingularChain_isCycle β⟩ c' hc'




/-- The constant path is the boundary of the constant singular triangle.
Source: Hatcher, Algebraic Topology, Theorem 2A.1 proof p.166. The alternating
boundary of the constant triangle is the constant edge minus itself plus itself.
This is the constant edge in the original unnormalized singular chain complex. -/
theorem constantPath_singular_boundary {X : Type} [TopologicalSpace X] (x : X) :
    ∃ c : (chains X).X 2,
      ((chains X).d 2 1) c = pathSingularChain (Path.refl x) := by
  let Y := TopCat.toSSet.obj (TopCat.of X)
  let R := ModuleCat.of ℚ (ℚ)
  let s : Y _⦋2⦌ := (TopCat.toSSetObjEquiv _ _).symm (ContinuousMap.const _ x)
  have hf (i : Fin 3) : Y.δ i s = pathSingularSimplex (Path.refl x) := by
    apply (TopCat.toSSetObjEquiv (TopCat.of X) _).injective
    apply ContinuousMap.ext
    intro p
    rfl
  refine ⟨(Y.ιChainComplex (R := R) s) (1 : R), ?_⟩
  have hb := congrArg (fun f ↦ f.hom (1 : R)) (Y.ιChainComplex_d (R := R) s)
  change ((Y.chainComplex R).d 2 1).hom ((Y.ιChainComplex (R := R) s).hom 1) =
    _ at hb
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hb
  change ((Y.chainComplex R).d 2 1).hom ((Y.ιChainComplex (R := R) s).hom 1) = _
  rw [hb]
  simp [hf, pathSingularChain, Y, R]




/-- The constant based loop has zero native singular homology class.
Source: Hatcher, Algebraic Topology, Theorem 2A.1 proof p.166.
The constant singular triangle has the constant loop as its boundary, so the
native cycle-to-homology projection identifies that loop cycle with zero. -/
theorem loopSingularClass_refl {X : Type} [TopologicalSpace X] (x : X) :
    loopSingularClass (Path.refl x) = 0 := by
  obtain ⟨c, hc⟩ := constantPath_singular_boundary x
  have hex : ∃ c' : ((chains X).sc 1).X₁,
      ((chains X).sc 1).f c' = pathSingularChain (Path.refl x) := by
    dsimp +instances only [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
      HomologicalComplex.shortComplexFunctor']
    rw [ComplexShape.prev_eq' (ComplexShape.down ℕ)
      (show (ComplexShape.down ℕ).Rel 2 1 from rfl)]
    exact ⟨c, hc⟩
  obtain ⟨c', hc'⟩ := hex
  have h := moduleCat_cycleClass_eq_of_boundary ((chains X).sc 1)
    ⟨pathSingularChain (Path.refl x), loopSingularChain_isCycle _⟩ 0 c' (by change _ = pathSingularChain (Path.refl x) - 0; rw [sub_zero]; exact hc')
  change loopSingularClass (Path.refl x) =
    ((chains X).sc 1).homologyπ
      (((chains X).sc 1).moduleCatCyclesIso.inv 0) at h
  rw [map_zero, map_zero] at h
  exact h




/-- A loop has zero singular H1 class exactly when its original one-chain bounds
a singular two-chain. Source: Hatcher, Algebraic Topology, p.167, first step of
the reverse kernel inclusion. Apply the native module cycle-class zero criterion
and identify the preceding degree of the degree-one short complex with two. -/
theorem loopSingularClass_eq_zero_iff {X : Type} [TopologicalSpace X]
    {x : X} (α : Path x x) :
    loopSingularClass α = 0 ↔
      ∃ c : (chains X).X 2,
        ((chains X).d 2 1) c = pathSingularChain α := by
  have h := moduleCat_cycleClass_eq_zero_iff ((chains X).sc 1)
    ⟨pathSingularChain α, loopSingularChain_isCycle α⟩
  change loopSingularClass α = 0 ↔ _ at h
  convert h using 1
  dsimp +instances only [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
    HomologicalComplex.shortComplexFunctor']
  rw [ComplexShape.prev_eq' (ComplexShape.down ℕ)
    (show (ComplexShape.down ℕ).Rel 2 1 from rfl)]



/-- A path chain plus its reversed-path chain is a boundary.
Source: Hatcher, Algebraic Topology, Theorem 2A.1 proof p.166. A path followed by
its reverse is homotopic relative endpoints to the constant loop, so its class
is zero and it bounds a two-chain. Add the concatenation triangle boundary. -/
theorem pathSymm_singular_boundary {X : Type} [TopologicalSpace X]
    {x y : X} (α : Path x y) :
    ∃ c : (chains X).X 2,
      ((chains X).d 2 1) c = pathSingularChain α + pathSingularChain α.symm := by
  have hz : loopSingularClass (α.trans α.symm) = 0 :=
    (loopSingularClass_homotopic (Path.Homotopic.trans_symm α)).trans (loopSingularClass_refl x)
  obtain ⟨c, hc⟩ := (loopSingularClass_eq_zero_iff _).1 hz
  obtain ⟨t, ht⟩ := pathTrans_singular_boundary α α.symm
  refine ⟨c + t, ?_⟩
  simp only [map_add, hc, ht]
  abel



/-- Transporting a loop along a connecting path changes its chain by a boundary.
Source: Hatcher, Algebraic Topology, Theorem 2A.1 proof p.167, basepoint transport
in the surjectivity proof. Use the two concatenation triangles, and cancel the
connecting path with its reverse using their singular two-chain boundary. -/
theorem pathConjugate_singular_boundary {X : Type} [TopologicalSpace X]
    {x y : X} (γ : Path x y) (α : Path y y) :
    ∃ c : (chains X).X 2,
      ((chains X).d 2 1) c =
        pathSingularChain ((γ.trans α).trans γ.symm) - pathSingularChain α := by
  obtain ⟨c₀, h₀⟩ := pathSymm_singular_boundary γ
  obtain ⟨c₁, h₁⟩ := pathTrans_singular_boundary γ α
  obtain ⟨c₂, h₂⟩ := pathTrans_singular_boundary (γ.trans α) γ.symm
  refine ⟨c₀ - c₁ - c₂, ?_⟩
  simp only [map_sub, h₀, h₁, h₂]
  abel



/-- Changing a loop's basepoint along a path preserves its singular H1 class.
Source: Hatcher, Algebraic Topology, Theorem 2A.1 proof p.167. The transported
loop and the original loop chains differ by the connecting-path triangle
boundary; therefore they have the same native homology class. -/
theorem loopSingularClass_conjugate {X : Type} [TopologicalSpace X]
    {x y : X} (γ : Path x y) (α : Path y y) :
    loopSingularClass ((γ.trans α).trans γ.symm) = loopSingularClass α := by
  have hex : ∃ c : ((chains X).sc 1).X₁,
      ((chains X).sc 1).f c =
        pathSingularChain ((γ.trans α).trans γ.symm) - pathSingularChain α := by
    dsimp +instances only [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
      HomologicalComplex.shortComplexFunctor']
    rw [ComplexShape.prev_eq' (ComplexShape.down ℕ)
      (show (ComplexShape.down ℕ).Rel 2 1 from rfl)]
    exact pathConjugate_singular_boundary γ α
  obtain ⟨c, hc⟩ := hex
  exact moduleCat_cycleClass_eq_of_boundary ((chains X).sc 1)
    ⟨pathSingularChain ((γ.trans α).trans γ.symm), loopSingularChain_isCycle _⟩
    ⟨pathSingularChain α, loopSingularChain_isCycle α⟩ c hc



/-- The native singular chain map sends a path generator to the mapped path
generator. Source: Hatcher, Algebraic Topology, p.111. Apply the coproduct-generator
chain-map formula and the original singular-simplex postcomposition identity. -/
theorem pathSingularChain_map {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {x y : X} (α : Path x y) (g : C(X, Y)) :
    ((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom g))
      (ModuleCat.of ℚ (ℚ))).f 1) (pathSingularChain α) =
      pathSingularChain (α.map g.continuous) := by
  have h := congrArg (fun f ↦ f.hom (1 : ModuleCat.of ℚ (ℚ)))
    (SSet.ι_chainComplexMap_f (TopCat.toSSet.obj (TopCat.of X)) (TopCat.toSSet.obj (TopCat.of Y)) (TopCat.toSSet.map (TopCat.ofHom g))
      (ModuleCat.of ℚ (ℚ)) (pathSingularSimplex α))
  simpa only [pathSingularSimplex_map, ModuleCat.hom_comp, LinearMap.comp_apply,
    pathSingularChain] using h



/-- Singular homology carries a loop's cycle class to the mapped loop's class.
Source: Hatcher, Algebraic Topology, p.111 and p.168. The chain map carries the
loop generator to the composed-loop generator, and the homology projection
commutes with this chain map. -/
theorem loopSingularClass_map {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} (α : Path x x) (g : C(X, Y)) :
    homologyMap g (loopSingularClass α) =
      loopSingularClass (α.map g.continuous) := by
  exact moduleCat_cycleClass_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) 1).map
      (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom g))
        (ModuleCat.of ℚ (ℚ))))
    ⟨pathSingularChain α, loopSingularChain_isCycle α⟩
    ⟨pathSingularChain (α.map g.continuous), loopSingularChain_isCycle _⟩
    (pathSingularChain_map α g)



/-- The explicit quotient map from the based fundamental group to singular H1.
Source: Hatcher, p. 166. The data are a quotient lift of the actual loop class. -/
def degreeOneHurewiczFunction {X : Type} [TopologicalSpace X] (x : X) :
    FundamentalGroup X x → H1 X :=
  Quotient.lift (fun α : Path x x ↦ loopSingularClass α)
    (fun _ _ h ↦ loopSingularClass_homotopic h)




/-- The degree-one Hurewicz quotient function sends the group identity to zero.
Source: Hatcher, Algebraic Topology, Theorem 2A.1 p.166. The identity is represented
by the constant based loop. The quotient lift evaluates to its singular class,
which vanishes because the constant triangle bounds the constant loop. -/
theorem degreeOneHurewiczFunction_one {X : Type} [TopologicalSpace X] (x : X) :
    degreeOneHurewiczFunction x 1 = 0 := by
  exact loopSingularClass_refl x



/-- The Hurewicz quotient function sends multiplication to addition.
Source: Hatcher, Algebraic Topology, Theorem 2A.1 p.166. Induct on both loop
representatives, use the concatenation triangle, and commute the two summands
because Mathlib's fundamental-group multiplication reverses path order. -/
theorem degreeOneHurewiczFunction_mul {X : Type} [TopologicalSpace X] (x : X)
    (a b : FundamentalGroup X x) :
    degreeOneHurewiczFunction x (a * b) =
      degreeOneHurewiczFunction x a + degreeOneHurewiczFunction x b := by
  induction a using Quotient.inductionOn with
  | h α =>
    induction b using Quotient.inductionOn with
    | h β =>
      change loopSingularClass (β.trans α) = loopSingularClass α + loopSingularClass β
      rw [loopSingularClass_trans, add_comm]



/-- The quotient function preserves the identity and multiplication additively.

Source and proof: Hatcher, p. 166. The constant loop bounds the constant
triangle, so its class is zero. For composable paths `a,b`, let `p=a.trans b`
and map the ordered triangle by `σ(t0,t1,t2)=p(t1/2+t2)`. Its three edges
are `b,p,a`, and its boundary is `b−p+a`. Hence the concatenation class
is the sum of the two path classes. Apply representative induction to
the fundamental-group quotient. Mathlib's multiplication concatenates
the representatives in the opposite order; commutativity of singular
H1 makes the resulting additive equality the displayed one. -/
theorem degreeOneHurewiczFunction_laws {X : Type} [TopologicalSpace X] (x : X) :
    degreeOneHurewiczFunction x 1 = 0 ∧
    ∀ a b : FundamentalGroup X x,
      degreeOneHurewiczFunction x (a * b) =
        degreeOneHurewiczFunction x a + degreeOneHurewiczFunction x b := by
  exact ⟨degreeOneHurewiczFunction_one x, degreeOneHurewiczFunction_mul x⟩




/-- The rational Hurewicz homomorphism, with a type tag for its additive codomain.
Source: Hatcher, p. 166. Its function is the concrete quotient lift above. -/
def degreeOneHurewicz {X : Type} [TopologicalSpace X] (x : X) :
    FundamentalGroup X x →* Multiplicative (H1 X) where
  toFun a := Multiplicative.ofAdd (degreeOneHurewiczFunction x a)
  map_one' := congrArg Multiplicative.ofAdd (degreeOneHurewiczFunction_laws x).1
  map_mul' a b := congrArg Multiplicative.ofAdd ((degreeOneHurewiczFunction_laws x).2 a b)



/-- The rational loop map is natural for an unbased continuous map, after any
path change of basepoint. The connecting path and its reverse cancel as singular
boundaries; the remaining loop is the postcomposition of the original loop.
Source: Hatcher, Theorem 2A.1, pp.166–168. -/
theorem degreeOneHurewicz_unbased_naturality
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y) (g : C(X, Y)) (δ : Path (g x) y)
    (a : FundamentalGroup X x) :
    degreeOneHurewiczFunction y
      (FundamentalGroup.fundamentalGroupMulEquivOfPath δ (FundamentalGroup.map g x a)) =
      homologyMap g (degreeOneHurewiczFunction x a) := by
  induction a using Quotient.inductionOn with
  | h α =>
    change loopSingularClass (δ.symm.trans ((α.map g.continuous).trans δ)) =
      homologyMap g (loopSingularClass α)
    rw [← loopSingularClass_homotopic (Path.Homotopic.trans_assoc δ.symm (α.map g.continuous) δ)]
    simpa only [Path.symm_symm] using
      (loopSingularClass_conjugate δ.symm (α.map g.continuous)).trans
        (loopSingularClass_map α g).symm

/-- The homomorphism from a finite winding lattice to rational homology expands
in its coordinate loop classes with the same integer coefficients. This is the
finite basis expansion in the source, followed by additivity of Hurewicz.
Source: Hatcher, Theorem 2A.1, p.166. -/
theorem degreeOneHurewicz_winding_expansion
    {X : Type} [TopologicalSpace X] (x : X) (n : ℕ)
    (w : FundamentalGroup X x ≃* Multiplicative (Fin n → ℤ))
    (γ : FundamentalGroup X x) :
    degreeOneHurewiczFunction x γ =
      ∑ j : Fin n, ((w γ).toAdd j : ℚ) •
        degreeOneHurewiczFunction x
          (w.symm (Multiplicative.ofAdd (Pi.single j (1 : ℤ)))) := by
  let F : (Fin n → ℤ) →+ H1 X := AddMonoidHom.toMultiplicative.symm
    ((degreeOneHurewicz x).comp w.symm.toMonoidHom)
  have hz : (w γ).toAdd = ∑ j : Fin n, (w γ).toAdd j • Pi.single j (1 : ℤ) := by
    ext i
    simp [Pi.single_apply]
  have he := congrArg F hz
  simp only [map_sum, map_zsmul] at he
  change degreeOneHurewiczFunction x (w.symm (w γ)) = _ at he
  rw [w.symm_apply_apply] at he
  simp only [Int.cast_smul_eq_zsmul]
  exact he

/-- In a rational basis given by the positive winding loops, the singular H1
matrix is the integer winding matrix with rational coefficients. No basepoint
preservation is required. Naturality identifies each image loop with its
basepoint-transported loop; the winding expansion gives its basis coefficients.
Source: Hatcher, Theorem 2A.1 and naturality, pp.166–168. -/
theorem homologyMap_matrix_of_winding
    {X : Type} [TopologicalSpace X] (x : X) (n : ℕ)
    (w : FundamentalGroup X x ≃* Multiplicative (Fin n → ℤ))
    (b : Module.Basis (Fin n) ℚ (H1 X))
    (hb : ∀ j, b j = degreeOneHurewiczFunction x
      (w.symm (Multiplicative.ofAdd (Pi.single j (1 : ℤ)))))
    (g : C(X, X)) (δ : Path (g x) x) (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : ∀ γ, (w (FundamentalGroup.fundamentalGroupMulEquivOfPath δ
      (FundamentalGroup.map g x γ))).toAdd = A.mulVec (w γ).toAdd) :
    LinearMap.toMatrix b b (homologyMap g) = A.map (Int.castRingHom ℚ) := by
  ext i j
  rw [LinearMap.toMatrix_apply, hb j,
    ← degreeOneHurewicz_unbased_naturality x x g δ,
    degreeOneHurewicz_winding_expansion x n w, hA]
  simp only [MulEquiv.apply_symm_apply, ← hb]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, map_sum, map_smul, Finsupp.single_apply]

end HolomorphicAnosov.RationalSingularH1G3

namespace HolomorphicAnosov.RationalSingularH1G3
open HolomorphicAnosov.Topology _root_.Topology
open HolomorphicAnosov.TorusRationalCupBasisKronecker

/-- The native rational coordinate cycle is exactly the Hurewicz image of the
corresponding positive winding generator. This fixes both sign and basis in the
rational comparison. Uniqueness of the explicitly normalized loop identifies
its singular simplex with the coordinate inclusion of the positive circle
simplex; naturality of the homology quotient then gives the equality.
Source: Hatcher, Theorem 2A.1 pp.166–168 and Example 3.16 p.216. -/
theorem coordinate_cycle_eq_winding (n : ℕ)
    (w : FundamentalGroup (UnitAddTorus (Fin n)) 0 ≃* Multiplicative (Fin n → ℤ))
    (hnorm : ∀ z : Fin n → ℤ, ∃ p : Path (0 : UnitAddTorus (Fin n)) 0,
      (∀ t j, p t j = (((t : ℝ) * (z j : ℝ) : ℝ) : UnitAddCircle)) ∧
      w (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)) = Multiplicative.ofAdd z)
    (z : LinearMap.ker ((chains UnitAddCircle).sc 1).g.hom)
    (hz : z.val = ((TopCat.toSSet.obj (TopCat.of UnitAddCircle)).ιChainComplex
      (R := ModuleCat.of ℚ ℚ) (TopCat.toSSetObj₁Equiv.symm additivePositiveLoop)) 1)
    (i : Fin n) :
    ((chains (UnitAddTorus (Fin n))).sc 1).moduleCatHomologyIso.inv
      (((chains (UnitAddTorus (Fin n))).sc 1).moduleCatLeftHomologyData.π
        (coordinateCycle n z i)) =
      degreeOneHurewiczFunction 0 (w.symm (Multiplicative.ofAdd (Pi.single i (1 : ℤ)))) := by
  obtain ⟨p, hp, hw⟩ := hnorm (Pi.single i 1)
  have hw' : w.symm (Multiplicative.ofAdd (Pi.single i (1 : ℤ))) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p) := by
    rw [← hw, w.symm_apply_apply]
  rw [hw']
  change _ = loopSingularClass p
  have hc : (coordinateCycle n z i).val = pathSingularChain p := by
    change (((SingularCochain.chainFunctor ℚ).map (coordinateInclusion n i)).f 1) z.val = _
    rw [hz]
    have h := congrArg (fun f ↦ f.hom (1 : ℚ))
      (SSet.ι_chainComplexMap_f (TopCat.toSSet.obj (TopCat.of UnitAddCircle))
        (TopCat.toSSet.obj (TopCat.of (UnitAddTorus (Fin n))))
        (TopCat.toSSet.map (coordinateInclusion n i)) (ModuleCat.of ℚ ℚ)
        (TopCat.toSSetObj₁Equiv.symm additivePositiveLoop))
    change _ = _ at h
    rw [show (((SingularCochain.chainFunctor ℚ).map (coordinateInclusion n i)).f 1)
      (((TopCat.toSSet.obj (TopCat.of UnitAddCircle)).ιChainComplex
        (R := ModuleCat.of ℚ ℚ) (TopCat.toSSetObj₁Equiv.symm additivePositiveLoop)) 1) =
      ((TopCat.toSSet.obj (TopCat.of (UnitAddTorus (Fin n)))).ιChainComplex
        (R := ModuleCat.of ℚ ℚ)
        ((TopCat.toSSet.map (coordinateInclusion n i)).app _
          (TopCat.toSSetObj₁Equiv.symm additivePositiveLoop))) 1 from h]
    congr 2
    congr 1
    have hs : (TopCat.toSSet.map (coordinateInclusion n i)).app _
        (TopCat.toSSetObj₁Equiv.symm additivePositiveLoop) =
        TopCat.toSSetObj₁Equiv.symm (additivePositiveLoop ≫ coordinateInclusion n i) := rfl
    rw [hs, pathSingularSimplex]
    congr 1
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro t
    funext j
    change (if j = i then ((t.down : ℝ) : UnitAddCircle) else 0) = p t.down j
    rw [hp]
    by_cases hj : j = i
    · simp [hj]
    · simp [hj]
  have ce : coordinateCycle n z i = ⟨pathSingularChain p, loopSingularChain_isCycle p⟩ :=
    Subtype.ext hc
  rw [ce]
  exact (congrArg (fun f ↦ f ⟨pathSingularChain p, loopSingularChain_isCycle p⟩)
    (((chains (UnitAddTorus (Fin n))).sc 1).moduleCatCyclesIso_inv_π)).symm

end HolomorphicAnosov.RationalSingularH1G3

namespace HolomorphicAnosov.RationalSingularH1G3
/-- Functoriality identifies the rational homology action of an iterate with
the corresponding power of the original action. -/
theorem homologyMap_iterate {X : Type} [TopologicalSpace X] (g : C(X, X)) (m : ℕ) :
    homologyMap (⟨(g : X → X)^[m], g.continuous.iterate m⟩ : C(X, X)) =
      homologyMap g ^ m := by
  let F := (singularHomologyFunctor (ModuleCat ℚ) 1).obj (ModuleCat.of ℚ ℚ)
  induction m with
  | zero =>
    change (F.map (𝟙 (TopCat.of X))).hom = 1
    rw [F.map_id]
    rfl
  | succ m ih =>
    have he : TopCat.ofHom (⟨(g : X → X)^[m + 1], g.continuous.iterate (m + 1)⟩ : C(X, X)) =
        TopCat.ofHom (⟨(g : X → X)^[m], g.continuous.iterate m⟩ : C(X, X)) ≫
          TopCat.ofHom g := by
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro x
      exact Function.iterate_succ_apply' _ _ _
    change (F.map (TopCat.ofHom _)).hom = _
    rw [he, F.map_comp]
    change (homologyMap g).comp
      (homologyMap (⟨(g : X → X)^[m], g.continuous.iterate m⟩ : C(X, X))) = _
    rw [ih, pow_succ']
    rfl
end HolomorphicAnosov.RationalSingularH1G3
