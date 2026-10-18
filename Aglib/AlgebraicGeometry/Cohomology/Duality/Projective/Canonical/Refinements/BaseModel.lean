/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.GeneratorOverlap
public import
  Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.NormalBase
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Contraction.Naturality

/-!
# Original canonical model arrows under an actual base determinant square

The same ordinary closed-adjoint model has the same original inverse normal
map in two base descriptions. Native evaluation contraction carries the
actual determinant square to the actual canonical model square.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u w
namespace AlgebraicGeometry.Scheme.Modules

/-- The original model isomorphism with its intrinsic normal sheaf made explicit.
At the reflexive ideal and degree identifications this is the original map itself. -/
def regularListCanonicalModelIsoAt
    {R A : CommRingCat.{u}} (α : R ⟶ A)
    (s : List A) (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    {L : (Spec A).Modules} [L.IsQuasicoherent] [HasExt.{w} (ModuleCat.{u} A)]
    (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A) (J : InjectiveResolution L)
    {Q : (Spec (regularListQuotientRing s)).Modules}
    (Δ : tensorSheaf (Spec (regularListQuotientRing s))
      (regularListNormalAt (Ideal.ofList s) s.length) Q ≅
        (pullback (Spec.map (regularListQuotientMap s))).obj L) :
    (closedImmersionRightAdjointRegularListResolutionComplex s J).homology
      (s.length : ℤ) ≅ Q :=
  regularListCanonicalModelTopHomologyIso s hs e α J Δ

private theorem modelIsoAt_hom
    {R A : CommRingCat.{u}} (α : R ⟶ A)
    (s : List A) (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    {L : (Spec A).Modules} [L.IsQuasicoherent] [HasExt.{w} (ModuleCat.{u} A)]
    (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A) (J : InjectiveResolution L)
    {Q : (Spec (regularListQuotientRing s)).Modules}
    (Δ : tensorSheaf (Spec (regularListQuotientRing s))
      (regularListNormalAt (Ideal.ofList s) s.length) Q ≅
        (pullback (Spec.map (regularListQuotientMap s))).obj L) :
    (regularListCanonicalModelIsoAt α s hs e J Δ).hom =
      (closedImmersionRightAdjointRegularListResolutionTopHomologyIso s hs J e).hom ≫
      (closedImmersionRegularListInverseNormalLineIso α s hs e).hom ≫
      (normalDeterminantContractionIso
        (closedImmersionRegularListNormalLineBundle α s hs)
        (closedImmersionRegularListNormalFrameIso α s hs)
        (closedImmersionRegularListNormalDualFrameIso α s hs) Δ).hom := rfl

/-- The literal equation between the two original model arrows, on the same coefficient
sheaf and injective resolution. Naming it shares the native sheaf types during checking. -/
def RegularListCanonicalModelBaseSquare
    {R S A : CommRingCat.{u}} (α : R ⟶ A) (β : S ⟶ A)
    (s : List A) (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    {L : (Spec A).Modules} [L.IsQuasicoherent]
    [HasExt.{w} (ModuleCat.{u} A)]
    (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A) (J : InjectiveResolution L)
    {Q Q' : (Spec (regularListQuotientRing s)).Modules}
    (Δ : tensorSheaf (Spec (regularListQuotientRing s))
      (regularListNormalAt (Ideal.ofList s) s.length) Q ≅
        (pullback (Spec.map (regularListQuotientMap s))).obj L)
    (Δ' : tensorSheaf (Spec (regularListQuotientRing s))
      (regularListNormalAt (Ideal.ofList s) s.length) Q' ≅
        (pullback (Spec.map (regularListQuotientMap s))).obj L)
    (a : Q ⟶ Q')
    : Prop :=
    (regularListCanonicalModelIsoAt α s hs e J Δ).hom ≫ a =
      (regularListCanonicalModelIsoAt β s hs e J Δ').hom

private theorem modelSquare_viaIdentity {C : Type*} [Category C]
    {H Q Q' : C} {f : H ⟶ Q} {g k : H ⟶ Q'} {a : Q ⟶ Q'}
    (hs : f ≫ a = g) (hb : g ≫ 𝟙 Q' = k) : f ≫ a = k :=
  hs.trans ((Category.comp_id g).symm.trans hb)

private theorem modelContractionSquare {Z : Scheme.{u}} (C : LineBundle Z)
    (eC : C.val ≅ SheafOfModules.unit Z.ringCatSheaf)
    (eD : (dualLineBundle Z C).val ≅ SheafOfModules.unit Z.ringCatSheaf)
    {P Q Q' H K : Z.Modules}
    (Δ : tensorSheaf Z C.val Q ≅ P) (Δ' : tensorSheaf Z C.val Q' ≅ P)
    (a : Q ⟶ Q') (h : Δ.hom = (moduleTensorLeftFunctor Z C.val).map a ≫ Δ'.hom)
    (t : H ≅ K) (v : K ≅ tensorSheaf Z (dualLineBundle Z C).val P) :
    (t ≪≫ v ≪≫ normalDeterminantContractionIso C eC eD Δ).hom ≫ a =
      (t ≪≫ v ≪≫ normalDeterminantContractionIso C eC eD Δ').hom := by
  have hΔ : Δ.hom ≫ 𝟙 P = (moduleTensorLeftFunctor Z C.val).map a ≫ Δ'.hom :=
    (Category.comp_id Δ.hom).trans h
  have hc := normalDeterminantContractionIso_naturality C eC eD Δ Δ' a (𝟙 P) hΔ
  rw [(moduleTensorLeftFunctor Z (dualLineBundle Z C).val).map_id P,
    Category.id_comp] at hc
  simpa only [Iso.trans_hom, Category.assoc] using
    congrArg (fun k => t.hom ≫ v.hom ≫ k) hc.symm

private theorem modelFramedIso_congr {Z : Scheme.{u}} {N : Z.Modules}
    (eC eC' : N ≅ SheafOfModules.unit Z.ringCatSheaf)
    (eD eD' : dualSheaf Z N ≅ SheafOfModules.unit Z.ringCatSheaf)
    {P Q H K : Z.Modules} (Δ : tensorSheaf Z N Q ≅ P)
    (t : H ≅ K) (v v' : K ≅ tensorSheaf Z (dualSheaf Z N) P) (hv : v = v')
    {f f' : H ⟶ Q}
    (hf : f = t.hom ≫ v.hom ≫
      (normalDeterminantContractionIso (lineBundleOfUnitFrame Z eC) eC eD Δ).hom)
    (hf' : f' = t.hom ≫ v'.hom ≫
      (normalDeterminantContractionIso (lineBundleOfUnitFrame Z eC') eC' eD' Δ).hom) :
    f ≫ 𝟙 Q = f' := by
  cases hv
  have hc : normalDeterminantContractionIso (lineBundleOfUnitFrame Z eC) eC eD Δ =
      normalDeterminantContractionIso (lineBundleOfUnitFrame Z eC') eC' eD' Δ := by
    simpa only [lineBundleOfUnitFrame] using
      normalDeterminantContractionIso_independent_frames
        (lineBundleOfUnitFrame Z eC) eC eD Δ eC' eD'
  rw [Category.comp_id, hf, hf', hc]

private theorem modelIso_base
    {R S A : CommRingCat.{u}} (α : R ⟶ A) (β : S ⟶ A)
    (s : List A) (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    {L : (Spec A).Modules} [L.IsQuasicoherent] [HasExt.{w} (ModuleCat.{u} A)]
    (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A) (J : InjectiveResolution L)
    {Q : (Spec (regularListQuotientRing s)).Modules}
    (Δ : tensorSheaf (Spec (regularListQuotientRing s))
      (regularListNormalAt (Ideal.ofList s) s.length) Q ≅
        (pullback (Spec.map (regularListQuotientMap s))).obj L) :
    RegularListCanonicalModelBaseSquare α β s hs e J Δ Δ (𝟙 Q) :=
  modelFramedIso_congr
    (closedImmersionRegularListNormalFrameIso α s hs)
    (closedImmersionRegularListNormalFrameIso β s hs)
    (closedImmersionRegularListNormalDualFrameIso α s hs)
    (closedImmersionRegularListNormalDualFrameIso β s hs)
    Δ
    (closedImmersionRightAdjointRegularListResolutionTopHomologyIso s hs J e)
    (closedImmersionRegularListInverseNormalLineIso α s hs e)
    (closedImmersionRegularListInverseNormalLineIso β s hs e)
    (regularListInverseNormalLineIso_base α β s hs e)
    (modelIsoAt_hom α s hs e J Δ)
    (modelIsoAt_hom β s hs e J Δ)

private theorem modelIso_sameBaseSquare
    {R A : CommRingCat.{u}} (α : R ⟶ A)
    (s : List A) (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    {L : (Spec A).Modules} [L.IsQuasicoherent] [HasExt.{w} (ModuleCat.{u} A)]
    (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A) (J : InjectiveResolution L)
    {Q Q' : (Spec (regularListQuotientRing s)).Modules}
    (Δ : tensorSheaf (Spec (regularListQuotientRing s))
      (regularListNormalAt (Ideal.ofList s) s.length) Q ≅
        (pullback (Spec.map (regularListQuotientMap s))).obj L)
    (Δ' : tensorSheaf (Spec (regularListQuotientRing s))
      (regularListNormalAt (Ideal.ofList s) s.length) Q' ≅
        (pullback (Spec.map (regularListQuotientMap s))).obj L)
    (a : Q ⟶ Q')
    (h : Δ.hom = (moduleTensorLeftFunctor (Spec (regularListQuotientRing s))
      (regularListNormalAt (Ideal.ofList s) s.length)).map a ≫ Δ'.hom) :
    (regularListCanonicalModelIsoAt α s hs e J Δ).hom ≫ a =
      (regularListCanonicalModelIsoAt α s hs e J Δ').hom :=
  modelContractionSquare (closedImmersionRegularListNormalLineBundle α s hs)
    (closedImmersionRegularListNormalFrameIso α s hs)
    (closedImmersionRegularListNormalDualFrameIso α s hs) Δ Δ' a h
    (closedImmersionRightAdjointRegularListResolutionTopHomologyIso s hs J e)
    (closedImmersionRegularListInverseNormalLineIso α s hs e)

/-- The original canonical model arrows retain an actual commuting base determinant square. -/
theorem regularListCanonicalModelTopHomologyIso_baseSquare
    {R S A : CommRingCat.{u}} (α : R ⟶ A) (β : S ⟶ A)
    (s : List A) (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    {L : (Spec A).Modules} [L.IsQuasicoherent]
    [HasExt.{w} (ModuleCat.{u} A)]
    (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A) (J : InjectiveResolution L)
    {Q Q' : (Spec (regularListQuotientRing s)).Modules}
    (Δ : tensorSheaf (Spec (regularListQuotientRing s))
      (regularListNormalAt (Ideal.ofList s) s.length) Q ≅
        (pullback (Spec.map (regularListQuotientMap s))).obj L)
    (Δ' : tensorSheaf (Spec (regularListQuotientRing s))
      (regularListNormalAt (Ideal.ofList s) s.length) Q' ≅
        (pullback (Spec.map (regularListQuotientMap s))).obj L)
    (a : Q ⟶ Q')
    (h : Δ.hom = (moduleTensorLeftFunctor (Spec (regularListQuotientRing s))
      (regularListNormalAt (Ideal.ofList s) s.length)).map a ≫ Δ'.hom) :
    RegularListCanonicalModelBaseSquare α β s hs e J Δ Δ' a :=
  modelSquare_viaIdentity
    (modelIso_sameBaseSquare α s hs e J Δ Δ' a h)
    (modelIso_base α β s hs e J Δ')

private theorem cancelModelPresentation {C : Type*} [Category C]
    {X H Q : C} {m : X ≅ H} {e f : H ≅ Q} {e' f' : X ≅ Q}
    (he : m ≪≫ e = e') (hf : m ≪≫ f = f') (h : e'.hom = f'.hom) :
    e.hom = f.hom := by
  apply (cancel_epi m.hom).mp
  exact (congrArg Iso.hom he).trans (h.trans (congrArg Iso.hom hf).symm)

/-- The actual canonical model arrow is independent of its coefficient frame, with the same
original coefficient sheaf, resolution and determinant. The native derived comparison cancels. -/
theorem regularListCanonicalModelTopHomologyIso_coefficient_independent
    {R A : CommRingCat.{u}} (α : R ⟶ A)
    (s : List A) (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    {L : (Spec A).Modules} [L.IsQuasicoherent] [HasExt.{w} (ModuleCat.{u} A)]
    (e f : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A) (J : InjectiveResolution L)
    {Q : (Spec (regularListQuotientRing s)).Modules}
    (Δ : tensorSheaf (Spec (regularListQuotientRing s))
      (regularListNormalAt (Ideal.ofList s) s.length) Q ≅
        (pullback (Spec.map (regularListQuotientMap s))).obj L) :
    (regularListCanonicalModelIsoAt α s hs e J Δ).hom =
      (regularListCanonicalModelIsoAt α s hs f J Δ).hom := by
  let : HasDerivedCategory.{u + 1} (Spec A).Modules := HasDerivedCategory.standard _
  let : HasDerivedCategory.{u + 1} (Spec (regularListQuotientRing s)).Modules :=
    HasDerivedCategory.standard _
  exact cancelModelPresentation
    (regularListCanonicalModelTopHomologyIso_native s hs e α J Δ)
    (regularListCanonicalModelTopHomologyIso_native s hs f α J Δ)
    (regularListCanonicalMapAt_coefficient_independent
      (Ideal.ofList s) e f s.length α Δ s hs rfl rfl)

end AlgebraicGeometry.Scheme.Modules
