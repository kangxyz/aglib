/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.BaseDeterminant
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Conormal.Determinant.Localization
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.GeneratorOverlap
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.DeterminantSquare.Definition

/-!
# Original wedge transport in an actual conormal square

The original determinant concatenates the normal columns before the tangent
lifts. Actual commuting conormal arrows therefore preserve that same wedge.
Only the genuine equality of the two normal degrees is transported.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules.Differentials

universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The original native determinant transported only through its actual exterior degree. -/
def canonicalConormalDeterminantInDegree
    {R A B : CommRingCat.{u}} (α : R ⟶ A) (σ : A ⟶ B)
    (hσ : Function.Surjective σ) (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hker : Ideal.ofList s = RingHom.ker σ.hom)
    (hA : α.hom.FormallySmooth) (hB : (α ≫ σ).hom.FormallySmooth)
    {d : ℕ} (bQ : Module.Basis (Fin d) B
      (CommRingCat.KaehlerDifferential (α ≫ σ))) (c : ℕ) (hc : s.length = c) :
    tensorSheaf (Spec B)
        (moduleExteriorPower (Spec B)
          ((pullback (Spec.map σ)).obj (Hom.idealModule (Spec.map σ))) c)
        (moduleExteriorPower (Spec B) (relativeConormalAffineComplex α σ hσ).X₃ d) ≅
      moduleExteriorPower (Spec B) (relativeConormalAffineComplex α σ hσ).X₂ (c + d) :=
  (eqToIso (congrArg (fun k => tensorSheaf (Spec B)
    (moduleExteriorPower (Spec B)
      ((pullback (Spec.map σ)).obj (Hom.idealModule (Spec.map σ))) k)
    (moduleExteriorPower (Spec B) (relativeConormalAffineComplex α σ hσ).X₃ d)) hc)).symm ≪≫
    relativeConormalAffineDeterminantIso α σ hσ s hs hker hA hB bQ ≪≫
    eqToIso (congrArg (fun k => moduleExteriorPower (Spec B)
      (relativeConormalAffineComplex α σ hσ).X₂ (k + d)) hc)

/-- Degree transport preserves the original arbitrary-section normal-first wedge formula. -/
theorem canonicalConormalDeterminantInDegree_sectionWedge
    {R A B : CommRingCat.{u}} (α : R ⟶ A) (σ : A ⟶ B)
    (hσ : Function.Surjective σ) (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hker : Ideal.ofList s = RingHom.ker σ.hom)
    (hA : α.hom.FormallySmooth) (hB : (α ≫ σ).hom.FormallySmooth)
    {d : ℕ} (bQ : Module.Basis (Fin d) B
      (CommRingCat.KaehlerDifferential (α ≫ σ))) (c : ℕ) (hc : s.length = c)
    (U : (Spec B).Opens)
    (v : Fin c → ((pullback (Spec.map σ)).obj (Hom.idealModule (Spec.map σ))).val.obj (op U))
    (w : Fin d → (relativeConormalAffineComplex α σ hσ).X₂.val.obj (op U)) :
    let N := (pullback (Spec.map σ)).obj (Hom.idealModule (Spec.map σ))
    let C := relativeConormalAffineComplex α σ hσ
    (canonicalConormalDeterminantInDegree α σ hσ s hs hker hA hB bQ c hc).hom.val.app (op U)
      (moduleTensorSection (Spec B) _ _ U
        ((SheafOfModulesOfCommRing.exteriorPowerMk (Spec B).sheaf N c).app (op U) v)
        ((SheafOfModulesOfCommRing.exteriorPowerMk (Spec B).sheaf C.X₃ d).app (op U)
          (fun j => C.g.val.app (op U) (w j)))) =
      (SheafOfModulesOfCommRing.exteriorPowerMk (Spec B).sheaf C.X₂ (c + d)).app (op U)
        (Fin.append (fun j => C.f.val.app (op U)
          ((relativeConormalAffineIdealPullbackIso α σ hσ).hom.val.app (op U) (v j))) w) := by
  subst c
  simpa only [canonicalConormalDeterminantInDegree, eqToIso_refl, Iso.refl_symm,
    Iso.refl_trans, Iso.trans_refl] using
      relativeConormalAffineDeterminantIso_sectionWedge α σ hσ s hs hker hA hB bQ U v w

private abbrev nativeFreeModule (X : Scheme.{u}) (U : X.Opens) (d : ℕ) :
    Module (X.sheaf.obj.obj (op U))
      ((SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin d))).val.obj (op U)) := by
  change Module (X.ringCatSheaf.obj.obj (op U)) _
  infer_instance

private theorem canonicalTopFrame_inverse_freeSection {X : Scheme.{u}} {N : X.Modules}
    {c : ℕ} (e : N ≅ SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin c)))
    (U : X.Opens) :
    (((moduleExteriorPowerFunctor X c).mapIso e) ≪≫
      SheafOfModulesOfCommRing.exteriorTopFreeIso X.sheaf c).hom.val.app (op U)
      ((SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf N c).app (op U)
        (fun i => e.inv.val.app (op U)
          ((SheafOfModules.freeSection (R := X.ringCatSheaf) (ULift.up i)).val (op U)))) =
      (1 : Γ(X, U)) := by
  let := nativeFreeModule X U c
  let v := fun i => e.inv.val.app (op U)
    ((SheafOfModules.freeSection (R := X.ringCatSheaf) (ULift.up i)).val (op U))
  let b := SheafOfModulesOfCommRing.freeFinSectionsBasis X.sheaf c (op U)
  have h₁ := congrArg
    ((SheafOfModulesOfCommRing.exteriorTopFreeHom X.sheaf c).val.app (op U))
    (SheafOfModulesOfCommRing.exteriorPowerFunctor_map_mk X.sheaf e.hom c (op U) v)
  have h₂ := SheafOfModulesOfCommRing.exteriorTopFreeHom_mk X.sheaf c (op U)
    (fun i => e.hom.val.app (op U) (v i))
  have hv : (fun i => e.hom.val.app (op U) (v i)) = b := by
    funext i
    exact (congrArg (fun f => f.val.app (op U)
      ((SheafOfModules.freeSection (R := X.ringCatSheaf) (ULift.up i)).val (op U)))
      e.inv_hom_id).trans
        (SheafOfModulesOfCommRing.freeFinSectionsBasis_apply X.sheaf c (op U) i).symm
  exact h₁.trans (h₂.trans ((congrArg b.det.toFun hv).trans (Module.Basis.det_self b)))

private theorem isoAfter_inv {C : Type*} [Category C] {X Y Y' : C}
    (e : Y ≅ Y') (f : X ⟶ Y) (g : X ⟶ Y') (h : f ≫ e.hom = g) :
    f = g ≫ e.inv := by
  rw [← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The actual native quotient map on a displayed ideal. -/
abbrev canonicalConormalQuotientMap {A : CommRingCat.{u}} (I : Ideal A) :
    A ⟶ CommRingCat.of (A ⧸ I) := CommRingCat.ofHom (Ideal.Quotient.mk I)

/-- The original geometric normal sheaf on that literal quotient. -/
abbrev canonicalConormalNormalSheaf {A : CommRingCat.{u}} (I : Ideal A) :=
  (pullback (Spec.map (canonicalConormalQuotientMap I))).obj
    (Hom.idealModule (Spec.map (canonicalConormalQuotientMap I)))

/-- The original pulled ambient differential sheaf on that literal quotient. -/
abbrev canonicalConormalMiddleSheaf {R A : CommRingCat.{u}} (α : R ⟶ A) (I : Ideal A) :=
  (pullback (Spec.map (canonicalConormalQuotientMap I))).obj
    (relativeDifferentialSheaf (Spec.map α))

/-- The same native determinant on raw quotient heads retains its arbitrary-section wedge law. -/
theorem canonicalConormalDeterminantAt_sectionWedge
    {R A : CommRingCat.{u}} (α : R ⟶ A) (I : Ideal A) (c d : ℕ)
    (hA : α.hom.FormallySmooth)
    (hB : (α ≫ canonicalConormalQuotientMap I).hom.FormallySmooth)
    (bQ : Module.Basis (Fin d) (CommRingCat.of (A ⧸ I))
      (CommRingCat.KaehlerDifferential (α ≫ canonicalConormalQuotientMap I)))
    (s : List A) (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hI : Ideal.ofList s = I) (hc : s.length = c)
    (U : (Spec (CommRingCat.of (A ⧸ I))).Opens)
    (v : Fin c → (canonicalConormalNormalSheaf I).val.obj (op U))
    (w : Fin d → (canonicalConormalMiddleSheaf α I).val.obj (op U)) :
    let K := relativeConormalAffineComplex α (canonicalConormalQuotientMap I)
      Ideal.Quotient.mk_surjective
    let eN := relativeConormalAffineIdealPullbackIso α (canonicalConormalQuotientMap I)
      Ideal.Quotient.mk_surjective
    (regularListConormalDeterminantAt α I c d hA hB bQ s hs hI hc).hom.val.app (op U)
      (moduleTensorSection (Spec (CommRingCat.of (A ⧸ I))) (regularListNormalAt I c)
        (regularListTangentTopAt α I d) U
        ((SheafOfModulesOfCommRing.exteriorPowerMk (Spec (CommRingCat.of (A ⧸ I))).sheaf
          (canonicalConormalNormalSheaf I) c).app (op U) v)
        ((SheafOfModulesOfCommRing.exteriorPowerMk (Spec (CommRingCat.of (A ⧸ I))).sheaf
          (relativeDifferentialSheaf (Spec.map (α ≫ canonicalConormalQuotientMap I))) d).app (op U)
          (fun i => K.g.val.app (op U) (w i)))) =
      (SheafOfModulesOfCommRing.exteriorPowerMk (Spec (CommRingCat.of (A ⧸ I))).sheaf
        (canonicalConormalMiddleSheaf α I) (c + d)).app (op U)
        (Fin.append (fun i => K.f.val.app (op U) (eN.hom.val.app (op U) (v i))) w) := by
  subst I c
  exact relativeConormalAffineDeterminantIso_sectionWedge α (regularListQuotientMap s)
    Ideal.Quotient.mk_surjective s hs Ideal.mk_ker.symm hA hB bQ U v w

/-- The original normal and tangent bases give a genuine unit frame and actual tangent lifts.
No formal smoothness or source nontriviality is used to construct this source test. -/
theorem canonicalConormalSourceWedgeFrame
    {R A : CommRingCat.{u}} (α : R ⟶ A) (I : Ideal A) (c d : ℕ)
    (s : List A) (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hI : Ideal.ofList s = I) (hc : s.length = c)
    (bQ : Module.Basis (Fin d) (CommRingCat.of (A ⧸ I))
      (CommRingCat.KaehlerDifferential (α ≫ canonicalConormalQuotientMap I)))
    (U : (Spec (CommRingCat.of (A ⧸ I))).Opens) :
    let B := CommRingCat.of (A ⧸ I)
    let K := relativeConormalAffineComplex α (canonicalConormalQuotientMap I)
      Ideal.Quotient.mk_surjective
    ∃ (eS : tensorSheaf (Spec B) (regularListNormalAt I c)
          (regularListTangentTopAt α I d) ≅ SheafOfModules.unit (Spec B).ringCatSheaf)
      (v : Fin c → (canonicalConormalNormalSheaf I).val.obj (op U))
      (w : Fin d → (canonicalConormalMiddleSheaf α I).val.obj (op U)),
      eS.hom.val.app (op U)
        (moduleTensorSection (Spec B) (regularListNormalAt I c)
          (regularListTangentTopAt α I d) U
          ((SheafOfModulesOfCommRing.exteriorPowerMk (Spec B).sheaf
            (canonicalConormalNormalSheaf I) c).app (op U) v)
          ((SheafOfModulesOfCommRing.exteriorPowerMk (Spec B).sheaf
            (relativeDifferentialSheaf (Spec.map (α ≫ canonicalConormalQuotientMap I))) d).app
              (op U)
              (fun i => K.g.val.app (op U) (w i)))) = (1 : Γ(Spec B, U)) := by
  subst I c
  intro B K
  let q := regularListQuotientMap s
  let M := (ModuleCat.extendScalars q.hom).obj (CommRingCat.KaehlerDifferential α)
  let eM := relativeConormalAffineMiddleIso α q
  let eQ := relativeDifferentialAffineIso (α ≫ q)
  let eC := relativeConormalAffineGeometricFreeIso α q Ideal.Quotient.mk_surjective
    s hs Ideal.mk_ker.symm
  let G := relativeConormalAffineLinearG α q Ideal.Quotient.mk_surjective
  have hsurj : Function.Surjective G := (ModuleCat.epi_iff_surjective _).mp
    (relativeConormalAffineLinearComplex_epi α q Ideal.Quotient.mk_surjective)
  choose w hw using fun i => hsurj (bQ i)
  let v := fun i => eC.inv.val.app (op U)
    ((SheafOfModules.freeSection (R := (Spec B).ringCatSheaf) (ULift.up i)).val (op U))
  let ww := fun i => eM.inv.val.app (op U) (tilde.toOpen M U (w i))
  let normal := (SheafOfModulesOfCommRing.exteriorPowerMk (Spec B).sheaf
    (canonicalConormalNormalSheaf (Ideal.ofList s)) s.length).app (op U) v
  let tangent := (SheafOfModulesOfCommRing.exteriorPowerMk (Spec B).sheaf
    (relativeDifferentialSheaf (Spec.map (α ≫ q))) d).app (op U)
      (fun i => K.g.val.app (op U) (ww i))
  let nFrame := (moduleExteriorPowerFunctor (Spec B) s.length).mapIso eC ≪≫
    SheafOfModulesOfCommRing.exteriorTopFreeIso (Spec B).sheaf s.length
  let qFrame := affineRelativeTopFrame (α ≫ q) d bQ
  let eS := ((SheafOfModulesOfCommRing.tensorFunctor (Spec B).sheaf).mapIso nFrame).app
      (regularListTangentTopAt α (Ideal.ofList s) d) ≪≫
    (SheafOfModulesOfCommRing.tensorLeftUnitIso (Spec B).sheaf).app
      (regularListTangentTopAt α (Ideal.ofList s) d) ≪≫ qFrame
  refine ⟨eS, v, ww, ?_⟩
  have hG : eM.inv ≫ K.g = (tilde.functor B).map G ≫ eQ.inv :=
    isoAfter_inv eQ (eM.inv ≫ K.g) ((tilde.functor B).map G)
      ((Category.assoc _ _ _).trans
        (relativeConormalAffineComplex_g_middle α q Ideal.Quotient.mk_surjective))
  have hGsection (i : Fin d) : K.g.val.app (op U) (ww i) =
      eQ.inv.val.app (op U)
        (tilde.toOpen (CommRingCat.KaehlerDifferential (α ≫ q)) U (bQ i)) := by
    have h₀ := congrArg (fun f : tilde M ⟶ relativeDifferentialSheaf (Spec.map (α ≫ q)) =>
      f.val.app (op U) (tilde.toOpen M U (w i))) hG
    have h₁ := ConcreteCategory.congr_hom (tilde.toOpen_map_app G U) (w i)
    exact h₀.trans (congrArg (eQ.inv.val.app (op U))
      (h₁.trans (congrArg (tilde.toOpen _ U) (hw i))))
  have hTangent := congrArg
    ((SheafOfModulesOfCommRing.exteriorPowerMk (Spec B).sheaf
      (relativeDifferentialSheaf (Spec.map (α ≫ q))) d).app (op U)) (funext hGsection)
  have hn : nFrame.hom.val.app (op U) normal = (1 : Γ(Spec B, U)) :=
    canonicalTopFrame_inverse_freeSection eC U
  have hq : qFrame.hom.val.app (op U) tangent = (1 : Γ(Spec B, U)) :=
    (congrArg (qFrame.hom.val.app (op U)) hTangent).trans
      (canonicalAffineTopFrame_basis (α ≫ q) d bQ U)
  let Qtop := regularListTangentTopAt α (Ideal.ofList s) d
  let : Module Γ(Spec B, U) (Qtop.val.obj (op U)) := by
    change Module ((Spec B).ringCatSheaf.obj.obj (op U)) _
    infer_instance
  have ht := tensorToUnit_section nFrame.hom Qtop U normal tangent
  change qFrame.hom.val.app (op U)
    (((tensorToUnit nFrame.hom).app Qtop).val.app (op U)
      (moduleTensorSection (Spec B) _ _ U normal tangent)) = _
  exact (congrArg (qFrame.hom.val.app (op U))
    (ht.trans ((congrArg (fun r : Γ(Spec B, U) => r • tangent) hn).trans
      (one_smul Γ(Spec B, U) tangent)))).trans hq

end AlgebraicGeometry.Scheme.Modules
