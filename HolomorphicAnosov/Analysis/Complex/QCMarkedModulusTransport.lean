import HolomorphicAnosov.Analysis.Complex.MarkedConformalModulus

/-!
# Conformal transport and uniqueness of marked modulus

Source: Lehto–Virtanen, *Quasiconformal Mappings in the Plane* (1973),
I.§§2.3–2.4, pp.14–15. Same-mark rectangle rigidity gives uniqueness; a
continuous injective compact-closure extension transports rectangle witnesses.
DAG node: `analysis.qc_marked_modulus_transport_g20`.
-/

namespace HolomorphicAnosov
open Set Analysis.MarkedRectangle

/-- Two conformal rectangle models with the same ordered boundary marks have
the same ratio. Compose one interior map with the other's holomorphic inverse;
their closure maps match the four corners. Rectangle rigidity makes this
composition a positive similarity, whose side ratios coincide. Source:
Lehto–Virtanen I.§2.3–2.4, pp.14–15. -/
theorem HasMarkedConformalModulus.unique {Q : Set ℂ} {p : Fin 4 → ℂ} {m n : ℝ}
    (hm : HasMarkedConformalModulus Q p m) (hn : HasMarkedConformalModulus Q p n) :
    m = n := by
  obtain ⟨a,b,ha,hb,rfl,F,Fi,hF,hFi,hbij,hmaps,hFiF,hFFi,e,he,hp⟩ := hm
  obtain ⟨A,B,hA,hB,rfl,G,Gi,hG,hGi,hGbij,hGmaps,hGiG,hGGi,eG,heG,hpG⟩ := hn
  obtain ⟨c,hc,hA',hB',hcF,hratio⟩ := RectangleModelPreparation.unique_model
    ha hb hA hB p F G Gi hF hGi hbij hGbij hGmaps hGiG hGGi e eG he heG hp hpG
  exact hratio.symm

/-- Conformal changes with the same continuous closure map preserve marked
modulus. Compose a source rectangle model with the given map and compose the
holomorphic inverses in reverse order. Compactness identifies the image of
the source closure with the closure of the image; injectivity makes this
restriction a homeomorphism. Its composition with the original closure model
has precisely the transported four marks. Source: Lehto–Virtanen I.§2.4. -/
theorem qc_marked_modulus_image {Q : Set ℂ} {p : Fin 4 → ℂ} {m : ℝ}
    (hmod : HasMarkedConformalModulus Q p m) (hcompact : IsCompact (closure Q))
    (f fi : ℂ → ℂ) (hfc : ContinuousOn f (closure Q)) (hinj : InjOn f (closure Q))
    (hf : DifferentiableOn ℂ f Q) (hfi : DifferentiableOn ℂ fi (f '' Q))
    (hleft : ∀ z ∈ Q, fi (f z) = z) :
    HasMarkedConformalModulus (f '' Q) (fun i ↦ f (p i)) m := by
  have hclosure : f '' closure Q = closure (f '' Q) :=
    Subset.antisymm hfc.image_closure
      (closure_minimal (image_mono subset_closure) (hcompact.image_of_continuousOn hfc).isClosed)
  have : CompactSpace (closure Q) := isCompact_iff_compactSpace.mp hcompact
  let k : closure Q → ℂ := fun z ↦ f z
  have hkc : Continuous k := hfc.domRestrict
  have hki : Function.Injective k := fun z w h ↦ Subtype.ext (hinj z.property w.property h)
  have hkr : range k = closure (f '' Q) := by
    rw [← hclosure]
    ext z
    exact ⟨fun ⟨w,hw⟩ ↦ ⟨w,w.property,hw⟩,fun ⟨w,hw,he⟩ ↦ ⟨⟨w,hw⟩,he⟩⟩
  let e := (hkc.isClosedEmbedding hki).isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hkr)
  have he (z : closure Q) : (e z : ℂ) = f z := rfl
  obtain ⟨a,b,ha,hb,hm,F,Fi,hF,hFi,hbij,hmaps,hFiF,hFFi,E,hE,hp⟩ := hmod
  have hfbij : BijOn f Q (f '' Q) :=
    ⟨mapsTo_image _ _,hinj.mono subset_closure,surjOn_image _ _⟩
  have hfimap : MapsTo fi (f '' Q) Q := by
    rintro z ⟨w,hw,rfl⟩
    rwa [hleft w hw]
  refine ⟨a,b,ha,hb,hm,f ∘ F,Fi ∘ fi,hf.comp hF hbij.mapsTo,
    hFi.comp hfi hfimap,hfbij.comp hbij,hmaps.comp hfimap,?_,?_,E.trans e,?_,?_⟩
  · intro z hz
    dsimp only [Function.comp_apply]
    rw [hleft _ (hbij.mapsTo hz),hFiF z hz]
  · rintro z ⟨w,hw,rfl⟩
    dsimp only [Function.comp_apply]
    rw [hleft w hw,hFFi w hw]
  · intro z hz
    change f (E z) = f (F z)
    rw [hE z hz]
  · intro i z hz
    change f (E z) = f (p i)
    rw [hp i z hz]

/-- The identity map gives the literal width/height modulus of a positive
rectangle, with its ordinary ordered corners. -/
theorem qc_identity_rectangle_modulus {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    HasMarkedConformalModulus (OpenRectangle a b) (RectangleCorner a b) (a / b) := by
  let e : ClosedRectangle a b ≃ₜ closure (OpenRectangle a b) :=
    Homeomorph.setCongr (RectangleModelPreparation.closure_openRectangle ha hb).symm
  refine ⟨a,b,ha,hb,rfl,id,id,differentiable_id.differentiableOn,
    differentiable_id.differentiableOn,bijOn_id _,mapsTo_id _,fun _ _ ↦ rfl,
    fun _ _ ↦ rfl,e,fun _ _ ↦ rfl,?_⟩
  intro i z hz
  exact hz

end HolomorphicAnosov

