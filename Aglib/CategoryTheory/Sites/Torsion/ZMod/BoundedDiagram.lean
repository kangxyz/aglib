/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsion.ZMod.Presentation
public import Aglib.CategoryTheory.Sites.Torsion.Annihilator.ZMod
public import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Canonical genuine scalar conversion of original bounded diagrams

The original underlying sheaf functor factors through the same full killed
subcategory. Canonical scalar conversion is an equivalence, including modulus
zero. The original cocone lifts to that full category, is mapped by canonical
conversion, and is extended through the exact native fully faithful preimage
of its original scalar comparison. Every underlying leg is retained.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory.Limits

namespace CategoryTheory.TorsionZMod.BoundedDiagram

universe u v a b

attribute [local instance] TorsionZMod.sheafUnderlying_full

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (n : ℕ)

/-- The native original scalar-forgetting functor, at the unchanged value universe. -/
abbrev underlying : Sheaf J (ModuleCat.{max u v} (ZMod n)) ⥤
    Sheaf J AddCommGrpCat.{max u v} :=
  sheafCompose J (forget₂ (ModuleCat.{max u v} (ZMod n)) AddCommGrpCat.{max u v})

/-- The actual canonical scalar conversion of the original bounded coefficients. -/
abbrev scalarLift : Presentation.Coefficient J n ⥤ Sheaf J (ModuleCat.{max u v} (ZMod n)) :=
  sheafFunctor.{u, v, max u v} J n

/-- Forgetting scalars after canonical conversion recovers the original
coefficient objects and maps through the native comparison. -/
abbrev scalarLiftUnderlyingIso :
    scalarLift J n ⋙ underlying J n ≅ Presentation.inclusion J n :=
  sheafFunctorUnderlyingIso.{u, v, max u v} J n

/-- The supplied genuine module structures land in the original bounded
coefficient category by their literal identity-annihilation equation. -/
def genuineCoefficientFunctor :
    Sheaf J (ModuleCat.{max u v} (ZMod n)) ⥤ Presentation.Coefficient J n :=
  (killedSheaves J n).lift (underlying J n)
    (sheafUnderlying_nsmul_id J n)

/-- The factorization through the original bounded coefficient inclusion
retains the original underlying functor literally. -/
def genuineCoefficientUnderlyingIso :
    genuineCoefficientFunctor J n ⋙ Presentation.inclusion J n ≅
      underlying J n :=
  (killedSheaves J n).liftCompιIso
    (underlying J n) (sheafUnderlying_nsmul_id J n)

/-- The actual underlying-coefficient factor is an equivalence, including
modulus zero. Essential surjectivity uses canonical scalar conversion. -/
instance genuineCoefficientFunctor_isEquivalence :
    (genuineCoefficientFunctor J n).IsEquivalence where
  faithful := Functor.Faithful.of_comp_iso (genuineCoefficientUnderlyingIso J n)
  full := Functor.Full.of_comp_faithful_iso (genuineCoefficientUnderlyingIso J n)
  essSurj := {
    mem_essImage F := ⟨(scalarLift J n).obj F, ⟨ObjectProperty.isoMk _
      (sheafUnderlyingIso J n F.obj F.property)⟩⟩ }

/-- The canonical scalar conversion is itself an equivalence. Its original
underlying comparison proves full faithfulness; the supplied genuine
module objects are recovered by full scalar forgetting. -/
instance scalarLift_isEquivalence : (scalarLift J n).IsEquivalence where
  faithful := Functor.Faithful.of_comp_iso (scalarLiftUnderlyingIso J n)
  full := Functor.Full.of_comp_faithful_iso (scalarLiftUnderlyingIso J n)
  essSurj := {
    mem_essImage M := ⟨(genuineCoefficientFunctor J n).obj M,
      ⟨(underlying J n).preimageIso
        (sheafUnderlyingIso J n
          ((underlying J n).obj M) (sheafUnderlying_nsmul_id J n M))⟩⟩ }

/-- The actual equivalence uses canonical conversion as its forward functor. -/
def genuineModuleEquivalence :
    Presentation.Coefficient J n ≌ Sheaf J (ModuleCat.{max u v} (ZMod n)) :=
  (scalarLift J n).asEquivalence

/-- The original genuine-module underlying functor preserves all original
colimits of the coefficient/index size, for every modulus. -/
instance genuineUnderlying_preservesColimits
    [HasSheafify J AddCommGrpCat.{max u v}] :
    PreservesColimitsOfSize.{max u v, max u v} (underlying J n) := by
  have : PreservesColimitsOfSize.{max u v, max u v}
      (genuineCoefficientFunctor J n ⋙ Presentation.inclusion J n) := inferInstance
  exact preservesColimits_of_natIso (genuineCoefficientUnderlyingIso J n)

/-- Canonical conversion of the original underlying coefficient is
isomorphic to the supplied genuine module sheaf, through the native
underlying comparison. -/
def canonicalModuleIso (M : Sheaf J (ModuleCat.{max u v} (ZMod n))) :
    (scalarLift J n).obj ((genuineCoefficientFunctor J n).obj M) ≅ M :=
  (underlying J n).preimageIso
    (sheafUnderlyingIso J n
      ((underlying J n).obj M) (sheafUnderlying_nsmul_id J n M))

/-- The underlying isomorphism is exactly the native original scalar comparison. -/
theorem canonicalModuleIso_underlying_hom (M : Sheaf J (ModuleCat.{max u v} (ZMod n))) :
    (underlying J n).map (canonicalModuleIso J n M).hom =
      (scalarLiftUnderlyingIso J n).hom.app ((genuineCoefficientFunctor J n).obj M) := by
  exact (underlying J n).map_preimage _

section CoconeTransport

variable {I : Type a} [Category.{b} I] (M : Sheaf J (ModuleCat.{max u v} (ZMod n)))
    (D : I ⥤ Presentation.Coefficient J n)
    (ι : D ⋙ Presentation.inclusion J n ⟶
      (Functor.const I).obj ((underlying J n).obj M))

/-- The original diagram's actual underlying comparison after canonical
scalar conversion, with no change of its index or arrows. -/
def scalarLiftDiagramUnderlyingIso :
    (D ⋙ scalarLift J n) ⋙ underlying J n ≅ D ⋙ Presentation.inclusion J n :=
  NatIso.ofComponents (fun i => (scalarLiftUnderlyingIso J n).app (D.obj i))
    (fun f => (scalarLiftUnderlyingIso J n).hom.naturality (D.map f))

/-- Lift the literal original cocone into its actual full coefficient category. -/
def originalCoefficientCocone : Cocone D where
  pt := (genuineCoefficientFunctor J n).obj M
  ι := {
    app i := ObjectProperty.homMk (ι.app i)
    naturality := by
      intro i j f
      apply ObjectProperty.hom_ext
      exact ι.naturality f }

/-- Reflection through the original full inclusion retains the supplied
original colimit, without replacing its cocone maps. -/
def originalCoefficientCoconeIsColimit
    (hι : IsColimit (Cocone.mk ((underlying J n).obj M) ι)) :
    IsColimit (originalCoefficientCocone J n M D ι) := by
  apply isColimitOfReflects (Presentation.inclusion J n)
  exact hι

/-- Apply canonical scalar conversion to the original cocone and use its
native comparison to make the point the original genuine module sheaf. -/
def genuinePresentationCocone : Cocone (D ⋙ scalarLift J n) :=
  ((scalarLift J n).mapCocone (originalCoefficientCocone J n M D ι)).extend
    (canonicalModuleIso J n M).hom

/-- The actual transported cocone with original genuine point is a colimit. -/
def genuinePresentationCoconeIsColimit
    (hι : IsColimit (Cocone.mk ((underlying J n).obj M) ι)) :
    IsColimit (genuinePresentationCocone J n M D ι) := by
  have hPres : PreservesColimitsOfShape I (scalarLift J n) :=
    ((genuineModuleEquivalence J n).toAdjunction.leftAdjoint_preservesColimits :
      PreservesColimitsOfSize.{b, a} (scalarLift J n)).preservesColimitsOfShape
  have hD : PreservesColimit D (scalarLift J n) := hPres.preservesColimit
  exact IsColimit.extendIso (canonicalModuleIso J n M).hom
    (hD.preserves (originalCoefficientCoconeIsColimit J n M D ι hι)).some

/-- Every original cocone map is recovered through the native scalar comparison. -/
theorem genuinePresentationCocone_underlying_ι (i : I) :
    (underlying J n).map ((genuinePresentationCocone J n M D ι).ι.app i) =
      (scalarLiftUnderlyingIso J n).hom.app (D.obj i) ≫ ι.app i := by
  let f : D.obj i ⟶ (genuineCoefficientFunctor J n).obj M :=
    ObjectProperty.homMk (ι.app i)
  change (underlying J n).map
      ((scalarLift J n).map f ≫
        (canonicalModuleIso J n M).hom) = _
  rw [Functor.map_comp, canonicalModuleIso_underlying_hom]
  exact (scalarLiftUnderlyingIso J n).hom.naturality f

/-- The underlying transported cocone is actually isomorphic to the original
cocone precomposed with its native diagram comparison. The point map is identity. -/
def genuinePresentationUnderlyingCoconeIso :
    (underlying J n).mapCocone (genuinePresentationCocone J n M D ι) ≅
      (Cocone.precompose (scalarLiftDiagramUnderlyingIso J n D).hom).obj
        (Cocone.mk ((underlying J n).obj M) ι) :=
  Cocone.ext (Iso.refl _) (by
    intro i
    change (underlying J n).map
        ((genuinePresentationCocone J n M D ι).ι.app i) ≫
          𝟙 ((underlying J n).obj M) =
      (scalarLiftUnderlyingIso J n).hom.app (D.obj i) ≫ ι.app i
    exact (Category.comp_id _).trans
      (genuinePresentationCocone_underlying_ι J n M D ι i))

end CoconeTransport

end CategoryTheory.TorsionZMod.BoundedDiagram
