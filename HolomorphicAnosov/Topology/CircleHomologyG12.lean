import HolomorphicAnosov.Topology.TorusH1Pi1Naturality
import HolomorphicAnosov.Topology.CircleSingularCohomologyWindingBaseG10
import HolomorphicAnosov.Topology.LoopSingularClassMap
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import HolomorphicAnosov.Topology.Homology.SphereHighDegreeG15
import Mathlib.Analysis.Complex.Basic
import HolomorphicAnosov.Algebra.Homology.SplitDifferentialKernelG12
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Algebra.Module.ULift
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace HolomorphicAnosov.CircleHomology
open HolomorphicAnosov.Topology

def torusCircleHomeomorph : UnitAddTorus (Fin 1) ≃ₜ Circle :=
  (Homeomorph.piUnique (fun _ : Fin 1 => UnitAddCircle)).trans
    (AddCircle.homeomorphCircle (T := 1) one_ne_zero)

/-- The integral Hurewicz basis transports to the positive exponential loop on the circle. -/
theorem integral_basis :
    ∃ B : Module.Basis Unit ℤ (IntegralSingularH1 Circle),
      ∃ p : Path (0 : UnitAddTorus (Fin 1)) 0,
        (∀ t i, p t i = ((t : ℝ) : UnitAddCircle)) ∧
        B () = loopSingularClass (p.map torusCircleHomeomorph.continuous) := by
  obtain ⟨w,h,b,_,hp,hb,_⟩ := torus_h1_pi1_naturality 1
  obtain ⟨p,hp,_⟩ := hp (Pi.single 0 1)
  have hp' : ∀ t i, p t i = ((t : ℝ) : UnitAddCircle) := by
    intro t i
    have hi : i = 0 := Subsingleton.elim _ _
    simpa [hi] using hp t i
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ (ULift ℤ))
  let E := F.mapIso (TopCat.isoOfHomeo (X := TopCat.of (UnitAddTorus (Fin 1)))
    (Y := TopCat.of Circle) torusCircleHomeomorph)
  let l : IntegralSingularH1 (UnitAddTorus (Fin 1)) ≃ₗ[ℤ] IntegralSingularH1 Circle := E.toLinearEquiv
  let e : Fin 1 ≃ Unit := { toFun := fun _ => (), invFun := fun _ => 0, left_inv := fun _ => Subsingleton.elim _ _, right_inv := fun _ => Subsingleton.elim _ _ }
  refine ⟨(b.map l).reindex e, p, hp', ?_⟩
  rw [Module.Basis.reindex_apply, Module.Basis.map_apply]
  have he : e.symm () = 0 := Subsingleton.elim _ _
  rw [he, hb 0 p hp]
  exact loopSingularClass_map p ⟨torusCircleHomeomorph, torusCircleHomeomorph.continuous⟩

theorem integral_basis_simplex (p : Path (0 : UnitAddTorus (Fin 1)) 0)
    (hp : ∀ t i, p t i = ((t : ℝ) : UnitAddCircle)) :
    pathSingularSimplex (p.map torusCircleHomeomorph.continuous) =
      CircleSingularCohomology.positiveSimplex := by
  apply TopCat.toSSetObj₁Equiv.injective
  simp only [pathSingularSimplex, CircleSingularCohomology.positiveSimplex, Equiv.apply_symm_apply]
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro t
  change torusCircleHomeomorph (p t.down) = Circle.exp (2 * Real.pi * (t.down : ℝ))
  simp [torusCircleHomeomorph, AddCircle.homeomorphCircle_apply,
    AddCircle.toCircle_apply_mk, hp]

end HolomorphicAnosov.CircleHomology

open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace HolomorphicAnosov.CircleHomology

def circleSphereHomeomorph : Circle ≃ₜ {x : EuclideanSpace ℝ (Fin 2) // ‖x‖ = 1} :=
  Complex.orthonormalBasisOneI.repr.toHomeomorph.subtype (by
    intro z
    change z ∈ Metric.sphere (0 : ℂ) 1 ↔ ‖Complex.orthonormalBasisOneI.repr z‖ = 1
    simp)

/-- The circle has zero homology in degrees greater than one with arbitrary integer-module
coefficients. Transport the sphere vanishing theorem along the standard isometric coordinates. -/
theorem high_integral (R : ModuleCat ℤ) (n : ℕ) (hn : 2 ≤ n) :
    IsZero ((TopCat.toSSet.obj (TopCat.of Circle)).chainComplex R |>.homology n) := by
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj R
  exact (sphere_high_degree_integral_module 1 n (by omega) R).of_iso
    (F.mapIso (TopCat.isoOfHomeo (X := TopCat.of Circle)
      (Y := TopCat.of {x : EuclideanSpace ℝ (Fin 2) // ‖x‖ = 1}) circleSphereHomeomorph))

/-- Restriction of scalars is exact and faithful; integer-module vanishing therefore proves
circle homology vanishing over every field, in every characteristic. -/
theorem high (K : Type) [Field K] (n : ℕ) (hn : 2 ≤ n) :
    IsZero ((TopCat.toSSet.obj (TopCat.of Circle)).chainComplex (ModuleCat.of K K) |>.homology n) := by
  let X := TopCat.toSSet.obj (TopCat.of Circle)
  let R := ModuleCat.of K K
  let F := ModuleCat.restrictScalars (Int.castRingHom K)
  let G := F.mapHomologicalComplex (.down ℕ)
  let C := X.chainComplex R
  let e := (SSet.chainComplexFunctorObjCompMapIso F R).app X
  let h : F.obj (C.homology n) ≅ (X.chainComplex (F.obj R)).homology n :=
    ((C.sc n).mapHomologyIso F).symm ≪≫
      ((HomologicalComplex.homologyFunctorIso (ModuleCat ℤ) (.down ℕ) n).app
        (G.obj C)).symm ≪≫ HomologicalComplex.homologyMapIso e n
  have hz : IsZero (F.obj (C.homology n)) := (high_integral (F.obj R) n hn).of_iso h
  have hs : Subsingleton (F.obj (C.homology n)) := ModuleCat.subsingleton_of_isZero hz
  have hs' : Subsingleton (C.homology n) := hs
  exact ModuleCat.isZero_of_subsingleton _

end HolomorphicAnosov.CircleHomology

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct Simplicial ChangeOfRings
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace HolomorphicAnosov.CircleHomology
variable (K : Type) [Field K]
local notation "F" => ModuleCat.extendScalars (Int.castRingHom K)
attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryCoproducts
instance ext_additive : (F).Additive := Functor.additive_of_preservesBinaryBiproducts F

def coefficientIso : (F).obj (ModuleCat.of ℤ (ULift.{0} ℤ)) ≅ ModuleCat.of K K := by
  let : Algebra ℤ K := ((algebraMap K K).comp (Int.castRingHom K)).toAlgebra
  let : Module ℤ K := Module.compHom K (Int.castRingHom K)
  let : IsScalarTower ℤ K K := ⟨fun r x y => by simp [smul_eq_mul, mul_assoc]⟩
  exact ((ULift.moduleEquiv.{0,0,0} (R := ℤ) (M := ℤ)).baseChange ℤ K _ _ |>.trans
    (TensorProduct.AlgebraTensorModule.rid ℤ K K)).toModuleIso

@[simp] theorem coefficientIso_one :
    (coefficientIso K).hom ((1 : K) ⊗ₜ[ℤ,Int.castRingHom K] (1 : ULift.{0} ℤ)) = 1 := by
  let : Algebra ℤ K := ((algebraMap K K).comp (Int.castRingHom K)).toAlgebra
  let : Module ℤ K := Module.compHom K (Int.castRingHom K)
  let : IsScalarTower ℤ K K := ⟨fun r x y => by simp [smul_eq_mul, mul_assoc]⟩
  change (TensorProduct.AlgebraTensorModule.rid ℤ K K)
    ((ULift.moduleEquiv.{0,0,0} (R := ℤ) (M := ℤ)).baseChange ℤ K _ _
      ((1 : K) ⊗ₜ[ℤ,Int.castRingHom K] (1 : ULift.{0} ℤ))) = 1
  rw [LinearEquiv.baseChange_tmul]
  rw [TensorProduct.AlgebraTensorModule.rid_tmul]
  simp only [ULift.moduleEquiv_apply]
  exact @one_smul ℤ K _ (inferInstance : Module ℤ K).toMulAction (1 : K)

def scalarBasis {M : ModuleCat ℤ} (B : Module.Basis Unit ℤ M) :
    Module.Basis Unit K ((F).obj M) := by
  let : Algebra ℤ K := ((algebraMap K K).comp (Int.castRingHom K)).toAlgebra
  let : Module ℤ K := Module.compHom K (Int.castRingHom K)
  exact B.baseChange K

lemma scalarBasis_apply {M : ModuleCat ℤ} (B : Module.Basis Unit ℤ M) :
    scalarBasis K B () = (1 : K) ⊗ₜ[ℤ,Int.castRingHom K] B () := by
  let : Algebra ℤ K := ((algebraMap K K).comp (Int.castRingHom K)).toAlgebra
  let : Module ℤ K := Module.compHom K (Int.castRingHom K)
  exact B.baseChange_apply K ()

/-- Scalar extension carries a literal cycle class to the class of its tensor cycle. -/
theorem scalar_cycle_representative (S : ShortComplex (ModuleCat ℤ))
    [(F).PreservesLeftHomologyOf S]
    (z : LinearMap.ker S.g.hom)
    (b : LinearMap.ker (S.map F).g.hom)
    (hb : b.val = ((F).map S.moduleCatLeftHomologyData.i) ((1 : K) ⊗ₜ[ℤ,Int.castRingHom K] z)) :
    (S.moduleCatLeftHomologyData.map F).homologyIso.inv
      ((1 : K) ⊗ₜ[ℤ,Int.castRingHom K] S.moduleCatLeftHomologyData.π z) =
      (S.map F).moduleCatHomologyIso.inv
        ((S.map F).moduleCatLeftHomologyData.π b) := by
  let h := S.moduleCatLeftHomologyData.map F
  let a : h.K := (1 : K) ⊗ₜ[ℤ,Int.castRingHom K] z
  have hc : h.cyclesIso.inv a = (S.map F).moduleCatCyclesIso.inv b := by
    apply (ModuleCat.mono_iff_injective (S.map F).iCycles).mp inferInstance
    have h1 := congrArg (fun q => q a) h.cyclesIso_inv_comp_iCycles
    have h2 := congrArg (fun q => q b) (S.map F).moduleCatCyclesIso_inv_iCycles
    simp only [ConcreteCategory.comp_apply] at h1 h2
    exact h1.trans (hb.symm.trans h2.symm)
  have hp := congrArg (fun q => q a) h.π_comp_homologyIso_inv
  have hbπ := congrArg (fun q => q b) (S.map F).moduleCatCyclesIso_inv_π
  simp only [ConcreteCategory.comp_apply] at hp hbπ
  change h.homologyIso.inv (h.π a) = _
  rw [hp, hc]
  exact hbπ

end HolomorphicAnosov.CircleHomology
namespace HolomorphicAnosov.CircleHomology
open HolomorphicAnosov.Topology HolomorphicAnosov.Algebra.Homology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

lemma integral_homology_projective (n : ℕ) :
    Projective ((integralSingularChains Circle).homology n) := by
  have hR : Projective (ModuleCat.of ℤ (ULift ℤ)) :=
    ModuleCat.projective_of_free ((Module.Basis.singleton Unit ℤ).map ULift.moduleEquiv.symm)
  rcases n with _ | n
  · exact (asIso ((TopCat.of Circle).singularHomology₀ε (ModuleCat.of ℤ (ULift ℤ)))).retract.projective
  · rcases n with _ | n
    · obtain ⟨B,_⟩ := integral_basis
      exact ModuleCat.projective_of_free B
    · exact (high_integral (ModuleCat.of ℤ (ULift ℤ)) (n+2) (by omega)).projective

lemma circle_preservesHomology (K : Type) [Field K] :
    (ModuleCat.extendScalars (Int.castRingHom K)).PreservesLeftHomologyOf
      ((integralSingularChains Circle).sc 1) := by
  let : ∀ n, Projective ((integralSingularChains Circle).homology n) := integral_homology_projective
  let : Projective (ModuleCat.of ℤ (ULift ℤ)) :=
    ModuleCat.projective_of_free ((Module.Basis.singleton Unit ℤ).map ULift.moduleEquiv.symm)
  let : ∀ n, Projective ((integralSingularChains Circle).X n) := fun n => by
    change Projective (∐ fun _ : (TopCat.toSSet.obj (TopCat.of Circle)).obj _ => ModuleCat.of ℤ (ULift ℤ))
    infer_instance
  exact preservesChainHomology_of_projective _ _ 1

open CircleSingularCohomology in
theorem field_positive_basis (K : Type) [Field K]
    (z : chainCycles K circleSpace 1)
    (hz : z.val = simplexChain K circleSpace 1 positiveSimplex) :
    ∃ B : Module.Basis Unit K (chainClass K circleSpace 1),
      B () = cycleClass K circleSpace 1 z := by
  obtain ⟨BI,p,hp,hBI⟩ := integral_basis
  let X := TopCat.toSSet.obj (TopCat.of Circle)
  let R := ModuleCat.of ℤ (ULift ℤ)
  let C := integralSingularChains Circle
  let S := C.sc 1
  let F := ModuleCat.extendScalars (Int.castRingHom K)
  have : F.PreservesLeftHomologyOf S := circle_preservesHomology K
  let D := (F.mapHomologicalComplex (.down ℕ)).obj C
  let T := D.sc 1
  let J := ((SSet.chainComplexFunctorObjCompMapIso F R).app X) ≪≫
    ((SSet.chainComplexFunctor (ModuleCat K)).mapIso (coefficientIso K)).app X
  let H := S.moduleCatLeftHomologyData.map F
  let E : F.obj S.moduleCatLeftHomologyData.H ≅
      ((chain K circleSpace).sc 1).moduleCatLeftHomologyData.H :=
    H.homologyIso.symm ≪≫ HomologicalComplex.homologyMapIso J 1 ≪≫
      ((chain K circleSpace).sc 1).moduleCatHomologyIso
  let BI' : Module.Basis Unit ℤ S.moduleCatLeftHomologyData.H :=
    BI.map S.moduleCatHomologyIso.toLinearEquiv
  let B := (scalarBasis K BI').map E.toLinearEquiv
  let zi : LinearMap.ker S.g.hom :=
    ⟨pathSingularChain (p.map torusCircleHomeomorph.continuous), loopSingularChain_isCycle _⟩
  have hBI' : BI' () = S.moduleCatLeftHomologyData.π zi := by
    change S.moduleCatHomologyIso.hom (BI ()) = _
    rw [hBI]
    have h := congrArg (fun q => q zi) S.moduleCatCyclesIso_inv_π
    change S.homologyπ (S.moduleCatCyclesIso.inv zi) =
      S.moduleCatHomologyIso.inv (S.moduleCatLeftHomologyData.π zi) at h
    change S.moduleCatHomologyIso.hom (S.homologyπ (S.moduleCatCyclesIso.inv zi)) = _
    rw [h]
    exact S.moduleCatHomologyIso.inv_hom_id_apply _
  let zb : LinearMap.ker T.g.hom :=
    ⟨(F.map S.moduleCatLeftHomologyData.i) ((1 : K) ⊗ₜ[ℤ,Int.castRingHom K] zi), by
      change (F.map S.g) ((F.map S.moduleCatLeftHomologyData.i) _) = 0
      have h := congrArg (fun q => q ((1 : K) ⊗ₜ[ℤ,Int.castRingHom K] zi))
        (F.congr_map S.moduleCatLeftHomologyData.wi)
      simpa only [F.map_comp, F.map_zero, ConcreteCategory.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] using h⟩
  have hJ : (J.hom.f 1) zb.val = z.val := by
    rw [hz]
    change (J.hom.f 1) ((1 : K) ⊗ₜ[ℤ,Int.castRingHom K] zi.val) = _
    have hzi : zi.val = (X.ιChainComplex (R := R) positiveSimplex) 1 := by
      change pathSingularChain _ = _
      simp only [pathSingularChain, integral_basis_simplex p hp]
      rfl
    rw [hzi]
    have hm := congrArg (fun q => q ((1 : K) ⊗ₜ[ℤ,Int.castRingHom K] (1 : R)))
      (X.map_ιChainComplex_chainComplexFunctorObjCompMapIso_hom_app_f F positiveSimplex)
    change (((SSet.chainComplexFunctor (ModuleCat K)).map (coefficientIso K).hom).app X).f 1
      (((SSet.chainComplexFunctorObjCompMapIso F R).hom.app X).f 1
        ((1 : K) ⊗ₜ[ℤ,Int.castRingHom K] (X.ιChainComplex (R := R) positiveSimplex) 1)) = _
    change (((SSet.chainComplexFunctorObjCompMapIso F R).hom.app X).f 1)
      ((1 : K) ⊗ₜ[ℤ,Int.castRingHom K] (X.ιChainComplex (R := R) positiveSimplex) 1) =
      (X.ιChainComplex (R := F.obj R) positiveSimplex)
        ((1 : K) ⊗ₜ[ℤ,Int.castRingHom K] (1 : R)) at hm
    rw [hm]
    change _ = (X.ιChainComplex (R := ModuleCat.of K K) positiveSimplex) 1
    have hcoef : X.ιChainComplex (R := F.obj R) positiveSimplex ≫
        (((SSet.chainComplexFunctor (ModuleCat K)).map (coefficientIso K).hom).app X).f 1 =
        (coefficientIso K).hom ≫ X.ιChainComplex positiveSimplex := by
      simp [SSet.chainComplexFunctor, SSet.ιChainComplex]
    have he := congrArg (fun q => q ((1 : K) ⊗ₜ[ℤ,Int.castRingHom K] (1 : R))) hcoef
    change _ = (X.ιChainComplex (R := ModuleCat.of K K) positiveSimplex)
      ((coefficientIso K).hom ((1 : K) ⊗ₜ[ℤ,Int.castRingHom K] (1 : ULift ℤ))) at he
    exact he.trans (congrArg (fun q => (X.ιChainComplex (R := ModuleCat.of K K) positiveSimplex) q) (coefficientIso_one K))
  refine ⟨B, ?_⟩
  change E.hom (scalarBasis K BI' ()) = _
  rw [scalarBasis_apply, hBI']
  have hs := scalar_cycle_representative K S zi zb rfl
  change ((chain K circleSpace).sc 1).moduleCatHomologyIso.hom
    (HomologicalComplex.homologyMap J.hom 1
      (H.homologyIso.inv ((1 : K) ⊗ₜ[ℤ,Int.castRingHom K] S.moduleCatLeftHomologyData.π zi))) = _
  rw [hs]
  have hnat := moduleCat_cycleClass_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat K) (.down ℕ) 1).map J.hom) zb z hJ
  have hbπ := congrArg (fun q => q zb) T.moduleCatCyclesIso_inv_π
  have hzπ := congrArg (fun q => q z) ((chain K circleSpace).sc 1).moduleCatCyclesIso_inv_π
  simp only [ConcreteCategory.comp_apply] at hbπ hzπ
  change HomologicalComplex.homologyMap J.hom 1
    (T.homologyπ (T.moduleCatCyclesIso.inv zb)) =
      ((chain K circleSpace).sc 1).homologyπ
        (((chain K circleSpace).sc 1).moduleCatCyclesIso.inv z) at hnat
  rw [hbπ,hzπ] at hnat
  exact (congrArg (fun q => ((chain K circleSpace).sc 1).moduleCatHomologyIso.hom q) hnat).trans (by
    exact ((chain K circleSpace).sc 1).moduleCatHomologyIso.inv_hom_id_apply _)

end HolomorphicAnosov.CircleHomology

