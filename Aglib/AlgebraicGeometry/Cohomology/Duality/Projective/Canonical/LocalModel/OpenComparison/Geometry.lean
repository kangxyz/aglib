/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.OpenComparison
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.Insertion.OpenNormal
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.CoefficientOpen
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.AmbientConormal.Coefficient

/-!
# The original canonical model arrows on an actual affine open square

The actual ordered-normal and determinant squares give the original
insertion square. The original mixed square gives the coefficient-section
image. Only the original source homology map and its native class image
remain to be instantiated by the ambient and principal producers.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u w z
namespace AlgebraicGeometry.Scheme.Modules

private theorem modelFrameDiagram
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {M Q P U : C} {M' Q' P' U' : D}
    (f : M ⟶ Q) (f' : M' ⟶ Q') (I : Q ≅ P) (I' : Q' ≅ P')
    (A : M ≅ U) (A' : M' ≅ U') (E : P ≅ U) (E' : P' ≅ U')
    (u : F.obj U ≅ U') (a : F.obj Q ⟶ Q') (b : F.obj P ⟶ P')
    (T : F.obj M ⟶ M')
    (hf : f ≫ I.hom = A.hom ≫ E.inv) (hf' : f' ≫ I'.hom = A'.hom ≫ E'.inv)
    (hI : F.map I.hom ≫ b = a ≫ I'.hom)
    (hA : F.map A.hom ≫ u.hom = T ≫ A'.hom)
    (hE : u.inv ≫ F.map E.inv ≫ b = E'.inv) : F.map f ≫ a = T ≫ f' := by
  have he : F.map E.inv ≫ b = u.hom ≫ E'.inv := by
    have h := congrArg (fun k => u.hom ≫ k) hE
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h
  apply (cancel_mono I'.hom).mp
  calc
    (F.map f ≫ a) ≫ I'.hom = F.map f ≫ (a ≫ I'.hom) := Category.assoc _ _ _
    _ = F.map f ≫ (F.map I.hom ≫ b) := congrArg (fun k => F.map f ≫ k) hI.symm
    _ = F.map (f ≫ I.hom) ≫ b := by
      rw [F.map_comp, Category.assoc]
    _ = F.map (A.hom ≫ E.inv) ≫ b := congrArg (fun k => F.map k ≫ b) hf
    _ = F.map A.hom ≫ (F.map E.inv ≫ b) := by
      rw [F.map_comp, Category.assoc]
    _ = F.map A.hom ≫ (u.hom ≫ E'.inv) :=
      congrArg (fun k => F.map A.hom ≫ k) he
    _ = (T ≫ A'.hom) ≫ E'.inv := by rw [← Category.assoc, hA]
    _ = T ≫ (f' ≫ I'.hom) := by rw [Category.assoc, hf']
    _ = (T ≫ f') ≫ I'.hom := (Category.assoc _ _ _).symm

private def modelUnitFrameInDegree
    {A : CommRingCat.{u}} (s : List A) (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    {L : (Spec A).Modules} [L.IsQuasicoherent] (J : InjectiveResolution L)
    (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A) [HasExt.{w} (ModuleCat.{u} A)]
    (c : ℕ) (hc : s.length = c) :
    (closedImmersionRightAdjointRegularListResolutionComplex s J).homology (c : ℤ) ≅
      SheafOfModules.unit (Spec (regularListQuotientRing s)).ringCatSheaf :=
  (eqToIso (congrArg (fun k : ℕ =>
    (closedImmersionRightAdjointRegularListResolutionComplex s J).homology (k : ℤ)) hc)).symm ≪≫
    closedImmersionRightAdjointRegularListResolutionTopHomologyIso s hs J e

private theorem modelUnitFrameInDegree_class
    {A : CommRingCat.{u}} (s : List A) (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    {L : (Spec A).Modules} [L.IsQuasicoherent] (J : InjectiveResolution L)
    (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A) [HasExt.{w} (ModuleCat.{u} A)]
    (c : ℕ) (hc : s.length = c) (U : (Spec (regularListQuotientRing s)).Opens) :
    (modelUnitFrameInDegree s hs J e c hc).hom.val.app (op U)
      (regularListModelTopClassInDegree s hs J e c hc (1 : A) U) =
      (1 : Γ(Spec (regularListQuotientRing s), U)) := by
  let H := eqToIso (congrArg (fun k : ℕ =>
    (closedImmersionRightAdjointRegularListResolutionComplex s J).homology (k : ℤ)) hc)
  let F := closedImmersionRightAdjointRegularListResolutionTopHomologyIso s hs J e
  have h := H.hom_inv_id_assoc F.hom
  exact (congrArg (fun k => k.val.app (op U)
    (regularListModelTopClass s hs J e (1 : A) U)) h).trans
      (regularListModelTopClass_one s hs J e U)

private theorem commonNormalModel_insert
    {R A : CommRingCat.{u}} (α : R ⟶ A) (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    {L : (Spec A).Modules} [L.IsQuasicoherent] (J : InjectiveResolution L)
    (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A) [HasExt.{w} (ModuleCat.{u} A)]
    (c : ℕ) (hc : s.length = c) {Q : (Spec (regularListQuotientRing s)).Modules}
    (Δ : tensorSheaf _ (regularListNormalLineInDegree α s hs c hc).val Q ≅
      (pullback (Spec.map (regularListQuotientMap s))).obj L) :
    (regularListCanonicalModelTopHomologyIsoCommonNormal α s hs J e c hc Δ).hom ≫
        (normalDeterminantInsertionIso (regularListNormalLineInDegree α s hs c hc)
          (canonicalAffineNormalFrameInDegree α (regularListQuotientMap s)
            Ideal.Quotient.mk_surjective s hs Ideal.mk_ker.symm c hc) Δ).hom =
      (modelUnitFrameInDegree s hs J e c hc).hom ≫
        (closedImmersionRegularListCoefficientFrameIso s e).inv := by
  let H := eqToIso (congrArg (fun k : ℕ =>
    (closedImmersionRightAdjointRegularListResolutionComplex s J).homology (k : ℤ)) hc)
  let D := regularListDeterminantFromCommonNormal α s hs c hc Δ
  let f := regularListCanonicalModelTopHomologyIso s hs e α J D
  let I := normalDeterminantInsertionIso (closedImmersionRegularListNormalLineBundle α s hs)
    (closedImmersionRegularListNormalFrameIso α s hs) D
  have hi := congrArg Iso.hom (regularListInsertionFromCommonNormal α s hs c hc Δ)
  have h := regularListCanonicalModelTopHomologyIso_insert s hs e α J D
  calc
    _ = (H.inv ≫ f.hom) ≫ I.hom := congrArg
      (fun k => (H.inv ≫ f.hom) ≫ k) hi.symm
    _ = H.inv ≫ (f.hom ≫ I.hom) := Category.assoc _ _ _
    _ = H.inv ≫ ((closedImmersionRightAdjointRegularListResolutionTopHomologyIso
        s hs J e).hom ≫ (closedImmersionRegularListCoefficientFrameIso s e).inv) :=
      congrArg (fun k => H.inv ≫ k) h
    _ = _ := (Category.assoc _ _ _).symm

section ActualOpen
variable {R A A' : CommRingCat.{u}} (α : R ⟶ A) (s : List A) (t : List A')
  (hs : RingTheory.Sequence.IsWeaklyRegular A s)
  (ht : RingTheory.Sequence.IsWeaklyRegular A' t)
  (φ : A ⟶ A') (ψ : regularListQuotientRing s ⟶ regularListQuotientRing t)
  [IsOpenImmersion (Spec.map φ)] [IsOpenImmersion (Spec.map ψ)]
  (h : φ ≫ regularListQuotientMap t = regularListQuotientMap s ≫ ψ)
  (hA : α.hom.FormallySmooth)
  (hB : (α ≫ regularListQuotientMap s).hom.FormallySmooth)
  (hA' : (α ≫ φ).hom.FormallySmooth)
  (hB' : ((α ≫ φ) ≫ regularListQuotientMap t).hom.FormallySmooth)
  {d : ℕ} (bA : Module.Basis (Fin (s.length + d)) A (CommRingCat.KaehlerDifferential α))
  (bA' : Module.Basis (Fin (s.length + d)) A' (CommRingCat.KaehlerDifferential (α ≫ φ)))
  (bQ : Module.Basis (Fin d) (regularListQuotientRing s)
    (CommRingCat.KaehlerDifferential (α ≫ regularListQuotientMap s)))
  (bQ' : Module.Basis (Fin d) (regularListQuotientRing t)
    (CommRingCat.KaehlerDifferential ((α ≫ φ) ≫ regularListQuotientMap t)))
  (hc : t.length = s.length)
  {L : (Spec A).Modules} [L.IsQuasicoherent]
  (J : InjectiveResolution L) (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A)
  (E : L ≅ moduleExteriorPower (Spec A)
    (relativeDifferentialSheaf (Spec.map α)) (s.length + d))
  [HasExt.{w} (ModuleCat.{u} A)] [HasExt.{z} (ModuleCat.{u} A')]

local instance : (L.restrict (Spec.map φ)).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec A').ringCatSheaf).prop_of_iso
    ((restrictFunctorIsoPullback (Spec.map φ)).symm.app L)
    (isQuasicoherent_pullback φ L)

local notation "q" => regularListQuotientMap s
local notation "q'" => regularListQuotientMap t
local notation "p" => Spec.map ψ
local notation "j" => Spec.map φ
local notation "H" => canonicalAmbientClosedSquare φ q q' ψ h
local notation "J'" => affineOpenRestrictedInjectiveResolution φ J
local notation "e'" => regularListOpenCoefficientFrame φ e (affineRestrictGlobalSectionsIso φ L)
local notation "E'" => Functor.mapIso (restrictFunctor j) E ≪≫
  canonicalAmbientTopOpenIso α φ (s.length + d)
local notation "D" => regularListCanonicalCoefficientDeterminantAt α s hs s.length d
  hA hB bA bQ rfl E
local notation "D'" => regularListCanonicalCoefficientDeterminantAt (α ≫ φ) t ht s.length d
  hA' hB' bA' bQ' hc E'
local notation "Q" => regularListTangentTopAt α (Ideal.ofList s) d
local notation "Q'" => regularListTangentTopAt (α ≫ φ) (Ideal.ofList t) d
local notation "aQ" => canonicalExteriorOpenMap p
  (relativeDifferentialSheaf (Spec.map (α ≫ q)))
  (relativeDifferentialSheaf (Spec.map ((α ≫ φ) ≫ q'))) d
  (Iso.hom (canonicalAmbientConormalTangentIso α φ q q' ψ h))
local notation "bP" =>
  NatTrans.app (Iso.hom
    (pullbackOpenSquare p (Spec.map q') (Spec.map q) j H)) L

omit [L.IsQuasicoherent] [HasExt.{w} (ModuleCat.{u} A)]
  [HasExt.{z} (ModuleCat.{u} A')] in
private theorem geometryInsertionSquare
    (hst : ∀ i : Fin s.length, φ (s.get i) = t.get (Fin.cast hc.symm i)) :
    (restrictFunctor p).map
        (normalDeterminantInsertionIso (closedImmersionRegularListNormalLineBundle α s hs)
          (closedImmersionRegularListNormalFrameIso α s hs) D).hom ≫ bP =
      aQ ≫ (normalDeterminantInsertionIso
        (regularListNormalLineInDegree (α ≫ φ) t ht s.length hc)
        (canonicalAffineNormalFrameInDegree (α ≫ φ) q' Ideal.Quotient.mk_surjective
          t ht Ideal.mk_ker.symm s.length hc) D').hom := by
  have hΔ := canonicalAmbientCoefficientDeterminant α s t hs ht φ ψ h
    hA hB hA' hB' bA bA' bQ bQ' hc E
  exact regularListNormalInsertion_open α (α ≫ φ) s t hs ht hc φ ψ H
    hst D D' aQ bP hΔ

private theorem geometryModelFrameSquare
    (T : ((closedImmersionRightAdjointRegularListResolutionComplex s J).homology
        (s.length : ℤ)).restrict p ⟶
      (closedImmersionRightAdjointRegularListResolutionComplex t J').homology (s.length : ℤ))
    (hClass : T.val.app (op ⊤)
        (regularListModelTopClass s hs J e (1 : A) (p ''ᵁ ⊤)) =
      regularListModelTopClassInDegree t ht J' e' s.length hc (1 : A') ⊤) :
    (restrictFunctor p).map
        (closedImmersionRightAdjointRegularListResolutionTopHomologyIso s hs J e).hom ≫
        (restrictUnitIso p).hom =
      T ≫ (modelUnitFrameInDegree t ht J' e' s.length hc).hom := by
  apply regularListModelTopClass_hom_ext_open s hs J e p
  let W := p ''ᵁ (⊤ : (Spec (regularListQuotientRing t)).Opens)
  have hL := (congrArg ((p).appIso ⊤).hom.hom
    (regularListModelTopClass_one s hs J e W)).trans (map_one ((p).appIso ⊤).hom.hom)
  have hR := (congrArg
    ((modelUnitFrameInDegree t ht J' e' s.length hc).hom.val.app (op ⊤)) hClass).trans
      (modelUnitFrameInDegree_class t ht J' e' s.length hc ⊤)
  exact hL.trans hR.symm

/-- Equality of the actual canonical model arrows on the given literal open square. -/
def CanonicalRegularListModelOpenSquare
    (T : ((closedImmersionRightAdjointRegularListResolutionComplex s J).homology
        (s.length : ℤ)).restrict p ⟶
      (closedImmersionRightAdjointRegularListResolutionComplex t J').homology (s.length : ℤ)) :
    Prop :=
  (restrictFunctor p).map (regularListCanonicalModelTopHomologyIso s hs e α J D).hom ≫ aQ =
    T ≫ (regularListCanonicalModelTopHomologyIsoCommonNormal
      (α ≫ φ) t ht J' e' s.length hc D').hom

/-- The actual original source class image identifies the canonical model arrows.
Normal, determinant and coefficient compatibility are proved by their native producers. -/
theorem regularListCanonicalModelTopHomologyIso_open_of_modelTopClass
    (hst : ∀ i : Fin s.length, φ (s.get i) = t.get (Fin.cast hc.symm i))
    (T : ((closedImmersionRightAdjointRegularListResolutionComplex s J).homology
        (s.length : ℤ)).restrict p ⟶
      (closedImmersionRightAdjointRegularListResolutionComplex t J').homology (s.length : ℤ))
    (hClass : T.val.app (op ⊤)
        (regularListModelTopClass s hs J e (1 : A) (p ''ᵁ ⊤)) =
      regularListModelTopClassInDegree t ht J' e' s.length hc (1 : A') ⊤) :
    CanonicalRegularListModelOpenSquare α s t hs ht φ ψ h hA hB hA' hB'
      bA bA' bQ bQ' hc J e E T := by
  have hI := geometryInsertionSquare α s t hs ht φ ψ h
    hA hB hA' hB' bA bA' bQ bQ' hc E hst
  have hFrame := geometryModelFrameSquare s t hs ht φ ψ hc J e T hClass
  have hCoefficient := regularListCoefficientFrame_open s t φ ψ H e
  exact modelFrameDiagram (restrictFunctor p)
    (regularListCanonicalModelTopHomologyIso s hs e α J D).hom
    (regularListCanonicalModelTopHomologyIsoCommonNormal
      (α ≫ φ) t ht J' e' s.length hc D').hom
    (normalDeterminantInsertionIso (closedImmersionRegularListNormalLineBundle α s hs)
      (closedImmersionRegularListNormalFrameIso α s hs) D)
    (normalDeterminantInsertionIso (regularListNormalLineInDegree (α ≫ φ) t ht s.length hc)
      (canonicalAffineNormalFrameInDegree (α ≫ φ) q' Ideal.Quotient.mk_surjective
        t ht Ideal.mk_ker.symm s.length hc) D')
    (closedImmersionRightAdjointRegularListResolutionTopHomologyIso s hs J e)
    (modelUnitFrameInDegree t ht J' e' s.length hc)
    (closedImmersionRegularListCoefficientFrameIso s e)
    (closedImmersionRegularListCoefficientFrameIso t e')
    (restrictUnitIso p) aQ bP T
    (regularListCanonicalModelTopHomologyIso_insert s hs e α J D)
    (commonNormalModel_insert (α ≫ φ) t ht J' e' s.length hc D')
    hI hFrame hCoefficient

end ActualOpen
end AlgebraicGeometry.Scheme.Modules
