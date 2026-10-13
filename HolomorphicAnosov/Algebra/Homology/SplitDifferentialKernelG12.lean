import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.MapHomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Abelian
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
noncomputable section

namespace HolomorphicAnosov.Algebra.Homology
universe u v
section Preadditive
variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]

/-- Source: Hatcher, Algebraic Topology, Theorem 3.2 and coefficient
discussion, pp.195–199. The idempotent 1 - g s factors through the kernel, giving a retraction of its inclusion. Applying the additive functor preserves the retraction and universal kernel lift. -/
theorem preservesKernel_of_generalizedInverse (F : C ⥤ D) [F.Additive]
    {X Y : C} (g : X ⟶ Y) [HasKernel g] (s : Y ⟶ X)
    (h : g ≫ s ≫ g = g) : PreservesLimit (parallelPair g 0) F := by
  let p : X ⟶ X := 𝟙 X - g ≫ s
  have hp : p ≫ g = 0 := by simp [p, sub_comp, Category.assoc, h]
  let r : X ⟶ kernel g := kernel.lift g p hp
  have hri : r ≫ kernel.ι g = p := kernel.lift_ι _ _ _
  have hir : kernel.ι g ≫ r = 𝟙 _ := by
    apply (cancel_mono (kernel.ι g)).mp
    simp [Category.assoc, hri, p, comp_sub]
  apply preservesLimit_of_preserves_limit_cone (kernelIsKernel g)
  refine (isLimitMapConeForkEquiv' F (kernel.condition g)).symm ?_
  refine KernelFork.IsLimit.ofι _ _ (fun t ht ↦ t ≫ F.map r) ?_ ?_
  · intro W t ht
    rw [Category.assoc, ← F.map_comp, hri]
    simp [p, F.map_sub, F.map_comp, comp_sub, ← Category.assoc, ht]
  · intro W t ht m hm
    have hh := hm =≫ F.map r
    simpa [Category.assoc, ← F.map_comp, hir] using hh

/-- Source: Hatcher, Algebraic Topology, Theorem 3.2 and coefficient
discussion, pp.195–199. The preceding kernel result preserves cycles. Finite-colimit preservation preserves the cokernel defining left homology. -/
theorem preservesLeftHomology_of_generalizedInverse (F : C ⥤ D) [F.Additive]
    [PreservesFiniteColimits F] (S : ShortComplex C) [HasKernel S.g]
    (s : S.X₃ ⟶ S.X₂) (h : S.g ≫ s ≫ S.g = S.g) :
    F.PreservesLeftHomologyOf S := by
  let := preservesKernel_of_generalizedInverse F S.g s h
  exact ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩⟩


end Preadditive

set_option backward.defeqAttrib.useBackward true
section Abelian
variable {C : Type*} [Category C] [Abelian C]

/-- Source: Hatcher, Algebraic Topology, Theorem 3.2 and coefficient
discussion, pp.195–199. Projectivity of the target splits the short exact sequence, making the kernel a retract of the projective source. -/
theorem projectiveKernel_of_epi {X Y : C} [Projective X] [Projective Y]
    (f : X ⟶ Y) [Epi f] : Projective (kernel f) := by
  let S := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
  have h : S.ShortExact :=
    { exact := S.exact_of_f_is_kernel (kernelIsKernel f) }
  let s := h.splittingOfProjective
  exact (show Retract (kernel f) X from ⟨kernel.ι f, s.r, s.f_r⟩).projective

/-- Source: Hatcher, Algebraic Topology, Theorem 3.2 and coefficient
discussion, pp.195–199. The image is the kernel of the split cokernel projection and hence projective. Split the surjection onto that image, then compose with the image retraction. -/
theorem exists_generalizedInverse_of_projectiveCokernel {X Y : C} (f : X ⟶ Y)
    [Projective Y] [Projective (cokernel f)] : ∃ s : Y ⟶ X, f ≫ s ≫ f = f := by
  have hp : Projective (Abelian.image f) := projectiveKernel_of_epi (cokernel.π f)
  let S := ShortComplex.mk (kernel.ι (cokernel.π f)) (cokernel.π f)
    (kernel.condition (cokernel.π f))
  have h : S.ShortExact :=
    { exact := S.exact_of_f_is_kernel (kernelIsKernel _) }
  let s := h.splittingOfProjective
  let t := Projective.factorThru (𝟙 (Abelian.image f)) (Abelian.factorThruImage f)
  refine ⟨s.r ≫ t, ?_⟩
  have ht : t ≫ Abelian.factorThruImage f = 𝟙 _ := by simp [t]
  calc
    f ≫ (s.r ≫ t) ≫ f =
        Abelian.factorThruImage f ≫ (Abelian.image.ι f ≫ s.r) ≫
          (t ≫ Abelian.factorThruImage f) ≫ Abelian.image.ι f := by
      simp only [Category.assoc, Abelian.image.fac]
      simp only [← Category.assoc, Abelian.image.fac]
    _ = f := by
      have hs : Abelian.image.ι f ≫ s.r = 𝟙 _ := s.f_r
      rw [hs, ht]
      change Abelian.factorThruImage f ≫ 𝟙 (Abelian.image f) ≫
        𝟙 (Abelian.image f) ≫ Abelian.image.ι f = f
      simp only [Category.id_comp]
      exact Abelian.image.fac f


/-- Source: Hatcher, Algebraic Topology, Theorem 3.2 and coefficient
discussion, pp.195–199. Split the short exact sequence and lift each of the two summand components through any epimorphism. Their sum lifts the morphism from the middle object. -/
theorem projectiveMiddle_of_shortExact (S : ShortComplex C) (h : S.ShortExact)
    [Projective S.X₁] [Projective S.X₃] : Projective S.X₂ := by
  let s := h.splittingOfProjective
  refine ⟨fun f e he ↦ ?_⟩
  refine ⟨s.r ≫ Projective.factorThru (S.f ≫ f) e +
    S.g ≫ Projective.factorThru (s.s ≫ f) e, ?_⟩
  simp only [add_comp, Category.assoc, Projective.factorThru_comp]
  rw [← Category.assoc, ← Category.assoc, ← add_comp, s.id, Category.id_comp]

/-- Source: Hatcher, Algebraic Topology, Theorem 3.2 and coefficient
discussion, pp.195–199. The outgoing image is projective as the kernel of a surjection between projectives. The incoming cokernel is an extension of this image by homology, so is projective. -/
theorem projectiveCokernel_of_projectiveHomology (S : ShortComplex C)
    [Projective S.X₃] [Projective (cokernel S.g)] [Projective S.homology] :
    Projective (cokernel S.f) := by
  have : Projective (Abelian.image S.g) := projectiveKernel_of_epi (cokernel.π S.g)
  have : Projective (Abelian.coimage S.g) := (Abelian.coimageIsoImage S.g).retract.projective
  let q := S.cokernelToAbelianCoimage
  have hfac : q ≫ Abelian.factorThruCoimage S.g = cokernel.desc S.f S.g S.zero := by
    apply (cancel_epi (cokernel.π S.f)).mp
    simp [q]
  let e : kernel q ≅ kernel (cokernel.desc S.f S.g S.zero) :=
    (kernelCompMono q (Abelian.factorThruCoimage S.g)).symm ≪≫ kernelIsoOfEq hfac
  let h := ShortComplex.RightHomologyData.ofHasCokernelOfHasKernel S
  have : Projective (kernel (cokernel.desc S.f S.g S.zero)) := by
    change Projective h.H
    exact h.homologyIso.symm.retract.projective
  have : Projective (kernel q) := e.retract.projective
  let T := ShortComplex.mk (kernel.ι q) q (kernel.condition q)
  have hT : T.ShortExact := { exact := T.exact_of_f_is_kernel (kernelIsKernel q) }
  exact projectiveMiddle_of_shortExact T hT


/-- Source: Hatcher, Algebraic Topology, Theorem 3.2 and coefficient
discussion, pp.195–199. At degree zero the differential cokernel equals homology. Inductively apply projectiveCokernel_of_projectiveHomology to the next three-term complex. -/
theorem projectiveChainCokernel (K : ChainComplex C ℕ)
    [∀ n, Projective (K.X n)] [∀ n, Projective (K.homology n)] (n : ℕ) :
    Projective (cokernel (K.d (n + 1) n)) := by
  induction n with
  | zero =>
    let S := K.sc' 1 0 0
    let h := ShortComplex.RightHomologyData.ofHasCokernel S (by
      change K.d 0 0 = 0
      exact K.shape _ _ (by simp [ComplexShape.down_Rel]))
    have he : Projective S.homology := (K.homologyIsoSc' 1 0 0
      ((ComplexShape.down ℕ).prev_eq' (by rfl))
      ((ComplexShape.down ℕ).next_eq_self' 0 (by intro k; simp [ComplexShape.down_Rel]))).symm.retract.projective
    change Projective (cokernel (K.d 1 0))
    change Projective h.H
    exact h.homologyIso.symm.retract.projective
  | succ n ih =>
    let S := K.sc' (n + 2) (n + 1) n
    let e := K.homologyIsoSc' (n + 2) (n + 1) n
      ((ComplexShape.down ℕ).prev_eq' (by rfl))
      ((ComplexShape.down ℕ).next_eq' (by rfl))
    have hX3 : Projective S.X₃ := by change Projective (K.X n); infer_instance
    let : Projective S.X₃ := hX3
    let : Projective (cokernel S.g) := ih
    have hH : Projective S.homology := e.symm.retract.projective
    let : Projective S.homology := hH
    exact projectiveCokernel_of_projectiveHomology S


/-- Source: Hatcher, Algebraic Topology, Theorem 3.2 and coefficient
discussion, pp.195–199. Induction makes the differential cokernel projective; split the image factorization. Off the allowed chain shape the differential and its generalized inverse are zero. -/
theorem exists_chainDifferential_generalizedInverse (K : ChainComplex C ℕ)
    [∀ n, Projective (K.X n)] [∀ n, Projective (K.homology n)] (i j : ℕ) :
    ∃ s : K.X j ⟶ K.X i, K.d i j ≫ s ≫ K.d i j = K.d i j := by
  by_cases h : (ComplexShape.down ℕ).Rel i j
  · have hi : j + 1 = i := h
    subst i
    have := projectiveChainCokernel K j
    exact exists_generalizedInverse_of_projectiveCokernel _
  · rw [K.shape i j h]
    exact ⟨0, by simp⟩

/-- Source: Hatcher, Algebraic Topology, Theorem 3.2 and coefficient
discussion, pp.195–199. Apply left-homology preservation to the generalized inverse of the outgoing differential at each degree. -/
theorem preservesChainHomology_of_projective (K : ChainComplex C ℕ)
    [∀ n, Projective (K.X n)] [∀ n, Projective (K.homology n)]
    {D : Type*} [Category D] [Preadditive D] (F : C ⥤ D) [F.Additive]
    [PreservesFiniteColimits F] (n : ℕ) : F.PreservesLeftHomologyOf (K.sc n) := by
  obtain ⟨s, hs⟩ := exists_chainDifferential_generalizedInverse K n
    ((ComplexShape.down ℕ).next n)
  exact preservesLeftHomology_of_generalizedInverse F (K.sc n) s hs


/-- Source: Hatcher, Algebraic Topology, Theorem 3.2 and coefficient
discussion, pp.195–199. Install homology preservation from the preceding theorem and apply the canonical short-complex homology comparison isomorphism. -/
noncomputable def mapChainHomologyIso_of_projective (K : ChainComplex C ℕ)
    [∀ n, Projective (K.X n)] [∀ n, Projective (K.homology n)]
    {D : Type*} [Category D] [Abelian D] (F : C ⥤ D) [F.Additive]
    [PreservesFiniteColimits F] (n : ℕ) :
    ((F.mapHomologicalComplex (.down ℕ)).obj K).homology n ≅ F.obj (K.homology n) := by
  have := preservesChainHomology_of_projective K F n
  exact (K.sc n).mapHomologyIso F

end Abelian

section Simplicial
universe w
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasCoproducts.{w} C] [HasCoproducts.{w} D]
/-- Source: Hatcher, Algebraic Topology, Theorem 3.2 and coefficient
discussion, pp.195–199. Mathlib SSet.chainComplexFunctorObjCompMapIso identifies coefficient transport with transport of the chain complex. Combine its induced homology isomorphism with mapChainHomologyIso_of_projective. -/
noncomputable def mapSimplicialHomologyIso_of_projective (X : SSet.{w}) (R : C)
    [∀ n, Projective ((X.chainComplex R).X n)]
    [∀ n, Projective ((X.chainComplex R).homology n)]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F]
    [∀ T : Type w, PreservesColimitsOfShape (Discrete T) F] (n : ℕ) :
    (X.chainComplex (F.obj R)).homology n ≅ F.obj ((X.chainComplex R).homology n) :=
  (HomologicalComplex.homologyMapIso
    ((SSet.chainComplexFunctorObjCompMapIso F R).app X) n).symm ≪≫
    mapChainHomologyIso_of_projective (X.chainComplex R) F n
end Simplicial

section ScalarExtension
attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryCoproducts

/-- Source: Hatcher, Algebraic Topology, Theorem 3.2 and coefficient
discussion, pp.195–199. Extension of scalars is a left adjoint, hence preserves coproducts and finite colimits, and is additive. Chain modules are coproducts of the projective coefficient module. Apply mapSimplicialHomologyIso_of_projective. -/
noncomputable def scalarExtensionSimplicialHomologyIso
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (X : SSet.{u}) (M : ModuleCat.{u} R) [Projective M]
    [∀ n, Projective ((X.chainComplex M).homology n)] (n : ℕ) :
    (X.chainComplex ((ModuleCat.extendScalars f).obj M)).homology n ≅
      (ModuleCat.extendScalars f).obj ((X.chainComplex M).homology n) := by
  let F := ModuleCat.extendScalars f
  letI : F.Additive := Functor.additive_of_preservesBinaryBiproducts F
  letI : ∀ n, Projective ((X.chainComplex M).X n) := fun n ↦ by
    change Projective (∐ fun _ : X.obj (Opposite.op (SimplexCategory.mk n)) ↦ M)
    infer_instance
  exact mapSimplicialHomologyIso_of_projective X M F n
end ScalarExtension

end HolomorphicAnosov.Algebra.Homology
