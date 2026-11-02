/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.ShortExact
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.HigherDirectImage.Comparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.HigherDirectImage.AffineFrobeniusTests
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.OriginalPresheafCoefficients

/-! # The original higher-image comparison intertwines Frobenius

The canonical affine component and original sheafification-unit coefficient law
identify the actual semilinear coefficient action with the original étale
higher-image map. The original module, cohomology groups, and comparison remain
unchanged throughout.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry.Scheme.Cohomology

universe u w s e v

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

attribute [local instance] HasExt.standard hasSheafifyLarge Scheme.Modules.isQuasicoherent_unit
  moduleComparisonEnoughSmall moduleComparisonEnoughRaised
  moduleComparisonAbWRaised moduleComparisonTypeWRaised
  instIsQuasicoherentOpensCarrierCarrierCommRingCatObjModulesRightDerivedPushforward_aglib

/-- Compose both original component values and their complete coefficient law
before any concrete geometric group, comparison, or operator is supplied. -/
private theorem comparisonValue_values
    {G B C D K L : Type*}
    {e : G → K} {l : G → B} {c : B → C} {t : C → D} {r : D → K}
    (he : AffineValueFunctionConstruction e l c t r)
    (k : K → L) (F : L → L)
    (x y : G) (bx byv : B) (hx : l x = bx) (hy : l y = byv)
    (hvalue : OriginalCohomologyCoefficientValueEquation k F t r (c bx) (c byv)) :
    OriginalCohomologyCoefficientValueEquation k F e id x y := by
  dsimp only [AffineValueFunctionConstruction] at he
  subst e
  change k (r (t (c (l y)))) = F (k (r (t (c (l x)))))
  rw [hx, hy]
  exact hvalue

/-- Recover the original component from its complete value-equivalence law,
without unfolding that equivalence or its coefficient-unit construction. -/
private theorem component_of_value_equation
    {G K L : AddCommGrpCat.{v}} (e : G ≃+ K)
    (h : G ⟶ L) (k : K ⟶ L) (F : L ⟶ L)
    (hh : h = AddCommGrpCat.ofHom e.toAddMonoidHom ≫ k)
    (x y : G)
    (hvalue : OriginalCohomologyCoefficientValueEquation k F e.toEquiv.toFun id x y) :
    OriginalCohomologyCoefficientValueEquation (id : L → L) F h id x y := by
  subst h
  dsimp only [OriginalCohomologyCoefficientValueEquation] at hvalue ⊢
  exact hvalue

/-- Lift a complete restricted intertwining law through the same faithful
functor and its proved original comparison isomorphism. -/
private theorem intertwining_of_restriction
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) [F.Faithful]
    {X Y : C} (E : X ≅ Y) (E' : F.obj X ≅ F.obj Y)
    (he : F.mapIso E = E') {a : X ⟶ X} {b : Y ⟶ Y}
    (h : F.map a ≫ E'.hom = E'.hom ≫ F.map b) : a ≫ E.hom = E.hom ≫ b := by
  apply F.map_injective
  rw [F.map_comp, F.map_comp]
  change F.map a ≫ (F.mapIso E).hom = (F.mapIso E).hom ≫ F.map b
  rw [he]
  exact h

/-- Compose an original intertwining square with a coefficient map and its
proved coefficient square before specializing the functor or its objects. -/
private theorem intertwining_comp_map
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y : C} {Q : D} {g : X ⟶ X} {t : X ⟶ Y} {h : Y ⟶ Y}
    {e : Q ⟶ F.obj X} {a : Q ⟶ Q}
    (ht : g ≫ t = t ≫ h) (he : a ≫ e = e ≫ F.map g) :
    a ≫ (e ≫ F.map t) = (e ≫ F.map t) ≫ F.map h := by
  calc
    a ≫ (e ≫ F.map t) = (a ≫ e) ≫ F.map t := (Category.assoc _ _ _).symm
    _ = (e ≫ F.map g) ≫ F.map t := congrArg (fun z => z ≫ F.map t) he
    _ = e ≫ F.map (g ≫ t) := by rw [Functor.map_comp, Category.assoc]
    _ = e ≫ F.map (t ≫ h) := congrArg (fun z => e ≫ F.map z) ht
    _ = (e ≫ F.map t) ≫ F.map h := by rw [Functor.map_comp, Category.assoc]

/-- Subtract the original identities from a whole coefficient square before
specializing its additive functor or geometric maps. -/
private theorem intertwining_sub_map_id
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] {X : C} {Q : D}
    {a : Q ⟶ Q} {b : X ⟶ X} {e : Q ⟶ F.obj X}
    (h : a ≫ e = e ≫ F.map b) :
    (a - 𝟙 Q) ≫ e = e ≫ F.map (b - 𝟙 X) := by
  rw [F.map_sub, F.map_id, Preadditive.sub_comp, Preadditive.comp_sub,
    Category.id_comp, Category.comp_id, h]

section ComparisonComponent

variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
  (M : X.Modules) [M.IsQuasicoherent] (q : ℕ)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s}
    (Sheaf ((smallEtaleTopology X).over ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [∀ U : S.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (Limits.pullback U.hom f))]

local instance (U : S.AffineEtale) : Etale ((Scheme.AffineEtale.Spec S).obj U).hom :=
  ((Scheme.AffineEtale.Spec S).obj U).prop

/-- The actual affine-restricted component is the original value equivalence followed by
its original higher-image sheafification unit, before evaluating any section. -/
private theorem originalRestriction_affine_component (U : S.AffineEtale) :
    (higherDirectImageAffineRestrictionIso.{u, w, s, e} f M q).hom.hom.app (op U) =
      AddCommGrpCat.ofHom
        (higherDirectImageAffineValueEquiv.{u, w, s, e} f M q U).toAddMonoidHom ≫
      (originalCohomologyToHigherDirectImage f (additiveCoefficient X M) q).app
        (op ((Scheme.AffineEtale.Spec S).obj U)) := by
  have hu := NatTrans.congr_app
    (higherDirectImageAffineRestrictionIso_unit.{u, w, s, e} f M q) (op U)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.op_obj, unop_op] at hu
  have hv := congrArg (fun k => k ≫
      (originalCohomologyToHigherDirectImage f (additiveCoefficient X M) q).app
        (op ((Scheme.AffineEtale.Spec S).obj U)))
    (higherDirectImageAffinePresheafIso_hom_app.{u, w, s, e} f M q U)
  exact hu.trans hv

end ComparisonComponent

section OriginalComparisonValues

variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
  (M : X.Modules) [M.IsQuasicoherent] (q : ℕ)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s}
    (Sheaf ((smallEtaleTopology X).over ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [∀ U : S.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (Limits.pullback U.hom f))]

local instance (U : S.AffineEtale) : Etale ((Scheme.AffineEtale.Spec S).obj U).hom :=
  ((Scheme.AffineEtale.Spec S).obj U).prop

/-- Transport the complete original cohomology equation through the canonical
comparison and its original coefficient unit, before specializing the coefficient
module, coefficient endomorphism, or affine section values. -/
private theorem originalAffineValue_coefficient_values
    (U : S.AffineEtale) (g : additiveCoefficient X M ⟶ additiveCoefficient X M)
    (x y : (moduleSpecΓFunctor (R := U.left.unop)).obj
      ((Scheme.Modules.pullback (X := Spec U.left.unop) (Y := S)
        ((Scheme.AffineEtale.Spec S).obj U).hom).obj
        (((Scheme.Modules.pushforward f).rightDerived q).obj M)))
    (hxy : AffineCohomologyCoefficientValues.{u, e} f
      ((Scheme.AffineEtale.Spec S).obj U).hom M q g x y) :
    let V := (Scheme.AffineEtale.Spec S).obj U
    let eV := higherDirectImageAffineValueEquiv.{u, w, s, e} f M q U
    let k := (originalCohomologyToHigherDirectImage f (additiveCoefficient X M) q).app (op V)
    OriginalCohomologyCoefficientValueEquation k
      (((higherDirectImage f q).map g).hom.app (op V))
      eV.toEquiv.toFun id (ULift.up x) (ULift.up y) := by
  let V := (Scheme.AffineEtale.Spec S).obj U
  dsimp only [AffineCohomologyCoefficientValues] at hxy
  have hv := fibreProductCohomologyToHigherDirectImage_coefficient_values.{u, w, s, e}
    f V g q hxy
  let : Small.{u + 1}
      (Sheaf.LargeCohomology.H.{w, u + 1, u, u + 1} (smallEtaleTopology X)
        (additiveCoefficient X M) q ((siteBaseChange f).obj V)) :=
    originalCohomologyPresheaf_small f (additiveCoefficient X M) q (op V)
  let eV := higherDirectImageAffineValueEquiv.{u, w, s, e} f M q U
  let k := (originalCohomologyToHigherDirectImage f (additiveCoefficient X M) q).app (op V)
  have heV := higherDirectImageAffineValueEquiv_function.{u, w, s, e} f M q U
  have finish := comparisonValue_values heV k
    (((higherDirectImage f q).map g).hom.app (op V))
    (ULift.up x) (ULift.up y) x y rfl rfl
  dsimp only [Functor.id_obj, Functor.fromPUnit, Functor.const_obj_obj,
    Scheme.AffineEtale.Spec_obj_left, AddEquiv.toFun_eq_coe] at hv finish
  have hfinal := finish hv
  dsimp only [Functor.id_obj, Functor.fromPUnit, Functor.const_obj_obj,
    Scheme.AffineEtale.Spec_obj_left, AddEquiv.toFun_eq_coe] at hfinal ⊢
  dsimp only [V, eV, k] at hfinal ⊢
  exact hfinal

/-- The complete original coefficient law for the global comparison follows
from its opaque original affine value equivalence and canonical component. -/
private theorem originalRestriction_affine_values
    (U : S.AffineEtale) (g : additiveCoefficient X M ⟶ additiveCoefficient X M)
    (x y : (moduleSpecΓFunctor (R := U.left.unop)).obj
      ((Scheme.Modules.pullback (X := Spec U.left.unop) (Y := S)
        ((Scheme.AffineEtale.Spec S).obj U).hom).obj
        (((Scheme.Modules.pushforward f).rightDerived q).obj M)))
    (hxy : AffineCohomologyCoefficientValues.{u, e} f
      ((Scheme.AffineEtale.Spec S).obj U).hom M q g x y) :
    let E := higherDirectImageAffineRestrictionIso.{u, w, s, e} f M q
    OriginalCohomologyCoefficientValueEquation id
      (((EtaleAffineBasis.abelianRestriction S).map ((higherDirectImage f q).map g)).hom.app (op U))
      (E.hom.hom.app (op U)) id (ULift.up x) (ULift.up y) := by
  let V := (Scheme.AffineEtale.Spec S).obj U
  let Q := ((Scheme.Modules.pushforward f).rightDerived q).obj M
  let G : AddCommGrpCat.{u + 1} :=
    ((EtaleAffineBasis.abelianRestriction S).obj (additiveCoefficient S Q)).obj.obj (op U)
  let K : AddCommGrpCat.{u + 1} :=
    (smallOriginalCohomologyPresheaf f (additiveCoefficient X M) q).obj (op V)
  let L : AddCommGrpCat.{u + 1} :=
    ((EtaleAffineBasis.abelianRestriction S).obj
      ((higherDirectImage f q).obj (additiveCoefficient X M))).obj.obj (op U)
  have hv := originalAffineValue_coefficient_values.{u, w, s, e} f M q U g x y hxy
  dsimp only at hv
  have hc := originalRestriction_affine_component.{u, w, s, e} f M q U
  have hfinal := component_of_value_equation (G := G) (K := K) (L := L)
    (higherDirectImageAffineValueEquiv.{u, w, s, e} f M q U) _
    ((originalCohomologyToHigherDirectImage f (additiveCoefficient X M) q).app (op V))
    (((EtaleAffineBasis.abelianRestriction S).map
      ((higherDirectImage f q).map g)).hom.app (op U)) hc
    (ULift.up x) (ULift.up y) hv
  exact hfinal

end OriginalComparisonValues

section GlobalComparison

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of A)) [QuasiCompact f] [QuasiSeparated f] (q : ℕ)
  (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : (Spec (CommRingCat.of A)).Etale, HasExt.{s}
    (Sheaf ((smallEtaleTopology X).over ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [∀ U : (Spec (CommRingCat.of A)).Etale,
    HasExt.{e} (AbelianSheaf.{u, u + 1} (Limits.pullback U.hom f))]

local instance (U : (Spec (CommRingCat.of A)).AffineEtale) :
    Etale ((Scheme.AffineEtale.Spec (Spec (CommRingCat.of A))).obj U).hom :=
  ((Scheme.AffineEtale.Spec (Spec (CommRingCat.of A))).obj U).prop

/-- The genuine semilinear Frobenius on the native higher-image module
intertwines with the original étale higher-image map under the actual comparison. -/
theorem higherDirectImageComparison_frobenius :
    let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
    let Q := ((Scheme.Modules.pushforward f).rightDerived q).obj O
    let Ψ := affineFrobenius (CommRingCat.of A) Q p hp hA
      (higherDirectImageFrobenius.{u, w} f q p hp hA)
    let E := higherDirectImageComparison.{u, w, s, e} f O q
    Ψ ≫ E.hom = E.hom ≫ (higherDirectImage f q).map
      (unitFrobenius X p hp (higherDirectImage_primeCast_source f p hA)) := by
  let S := Spec (CommRingCat.of A)
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let Q := ((Scheme.Modules.pushforward f).rightDerived q).obj O
  let Ψ := affineFrobenius (CommRingCat.of A) Q p hp hA
    (higherDirectImageFrobenius.{u, w} f q p hp hA)
  let E := higherDirectImageAffineRestrictionIso.{u, w, s, e} f O q
  apply intertwining_of_restriction (EtaleAffineBasis.abelianRestriction S)
    (higherDirectImageComparison.{u, w, s, e} f O q) E
    (higherDirectImageComparison_restrict.{u, w, s, e} f O q)
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro x
  let V := (Scheme.AffineEtale.Spec S).obj U.unop
  have hs := higherDirectImageAffineSectionsEquiv_affineTest_frobenius.{u, w, e}
    f q U.unop p hp hA x.down
  dsimp only [AffineCohomologyFrobenius] at hs
  have hfinal := originalRestriction_affine_values.{u, w, s, e}
    f O q U.unop
    (unitFrobenius X p hp (higherDirectImage_primeCast_source f p hA)) _ _ hs
  dsimp only [OriginalCohomologyCoefficientValueEquation] at hfinal
  simp only [ULift.up_down] at hfinal
  change (E.hom.hom.app U) (Ψ.hom.app (op V) x) =
    (((EtaleAffineBasis.abelianRestriction S).map ((higherDirectImage f q).map
      (unitFrobenius X p hp (higherDirectImage_primeCast_source f p hA)))).hom.app U)
      (E.hom.hom.app U x)
  exact hfinal

/-- The same genuine semilinear Frobenius intertwines with the original
structure-sheaf higher-image map after the original unit/structure comparison. -/
theorem higherDirectImageComparison_structureFrobenius :
    let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
    let Q := ((Scheme.Modules.pushforward f).rightDerived q).obj O
    let Ψ := affineFrobenius (CommRingCat.of A) Q p hp hA
      (higherDirectImageFrobenius.{u, w} f q p hp hA)
    let E := higherDirectImageComparison.{u, w, s, e} f O q
    let c := E.hom ≫ (higherDirectImage f q).map (additiveUnitStructureIso X).hom
    Ψ ≫ c = c ≫ (higherDirectImage f q).map
      (structureFrobenius X p hp (higherDirectImage_primeCast_source f p hA)) := by
  have h := intertwining_comp_map (higherDirectImage f q)
    (unitFrobenius_structure X p hp (higherDirectImage_primeCast_source f p hA))
    (higherDirectImageComparison_frobenius.{u, w, s, e} f q p hp hA)
  exact h

/-- The original Artin–Schreier higher-image map is intertwined with the
actual semilinear Frobenius minus identity by the original comparison iso. -/
theorem higherDirectImageComparison_artinSchreierMap :
    let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
    let Q := ((Scheme.Modules.pushforward f).rightDerived q).obj O
    let Ψ := affineFrobenius (CommRingCat.of A) Q p hp hA
      (higherDirectImageFrobenius.{u, w} f q p hp hA)
    let E := higherDirectImageComparison.{u, w, s, e} f O q ≪≫
      (higherDirectImage f q).mapIso (additiveUnitStructureIso X)
    (Ψ - 𝟙 _) ≫ E.hom = E.hom ≫ (higherDirectImage f q).map
      (artinSchreierMap X p hp (higherDirectImage_primeCast_source f p hA)) := by
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} X)
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1}
    (Spec (CommRingCat.of A)))
  have h := intertwining_sub_map_id (higherDirectImage f q)
    (higherDirectImageComparison_structureFrobenius.{u, w, s, e} f q p hp hA)
  exact h

end GlobalComparison

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
