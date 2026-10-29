/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.OfCommRing
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Whiskering

/-!
# Tensor products of sheaves of modules over commutative rings

The tensor bifunctor is the existing pointwise tensor of module presheaves followed by
module sheafification. Its maps in both variables are the original sheafified tensor maps.
The left unit comparison is the original presheaf unitor followed by the sheafification
counit. Site, morphism, and coefficient universes remain independent; composition of the
commutative ring sheaf with the forgetful functor is an explicit hypothesis.
-/


/-!
Source: `Quillen/Algebra/Category/ModuleCat/Sheaf/Tensor.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Selection: whole_general_prerequisite; source ranges [[1, 118]].
Actual objects, maps, universes and hypotheses are preserved.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory


namespace SheafOfModulesOfCommRing

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf J CommRingCat.{u}) [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Forget a module sheaf to the original commutative-ring module presheaf. -/
abbrev toPresheaf : SheafOfModulesOfCommRing R ⥤ PresheafOfModulesOfCommRing.{u} R.obj :=
  SheafOfModules.forget ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)

/-- The original module sheafification over the underlying ring sheaf. -/
abbrev associatedSheaf : PresheafOfModulesOfCommRing.{u} R.obj ⥤
    SheafOfModulesOfCommRing R :=
  PresheafOfModules.sheafification
    (R := ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (𝟙 _)

/-- Tensoring is original pointwise tensor followed by module sheafification. -/
def tensorLeftFunctor (M : SheafOfModulesOfCommRing R) :
    SheafOfModulesOfCommRing R ⥤ SheafOfModulesOfCommRing R :=
  toPresheaf R ⋙ tensorLeft ((toPresheaf R).obj M) ⋙ associatedSheaf R

/-- The actual sheafified tensor bifunctor. -/
def tensorFunctor : SheafOfModulesOfCommRing R ⥤
    SheafOfModulesOfCommRing R ⥤ SheafOfModulesOfCommRing R :=
  toPresheaf R ⋙ curriedTensor (PresheafOfModulesOfCommRing.{u} R.obj) ⋙
    (Functor.whiskeringLeft _ _ _).obj (toPresheaf R) ⋙
    (Functor.whiskeringRight _ _ _).obj (associatedSheaf R)

/-- The original second-variable tensor functor is the object component. -/
theorem tensorFunctor_obj (M : SheafOfModulesOfCommRing R) :
    (tensorFunctor R).obj M = tensorLeftFunctor R M := rfl

/-- The second-variable map is the sheafification of its original tensor map. -/
theorem tensorLeftFunctor_map (M : SheafOfModulesOfCommRing R)
    {N P : SheafOfModulesOfCommRing R} (f : N ⟶ P) :
    (tensorLeftFunctor R M).map f =
      (associatedSheaf R).map (𝟙 ((toPresheaf R).obj M) ⊗ₘ (toPresheaf R).map f) := rfl

/-- The first-variable map is the sheafification of its original tensor map. -/
theorem tensorFunctor_map_app {M N : SheafOfModulesOfCommRing R} (f : M ⟶ N)
    (P : SheafOfModulesOfCommRing R) :
    ((tensorFunctor R).map f).app P =
      (associatedSheaf R).map ((toPresheaf R).map f ⊗ₘ 𝟙 ((toPresheaf R).obj P)) := rfl

/-- Tensoring with the original structure module is naturally the identity. -/
def tensorLeftUnitIso : tensorLeftFunctor R
    (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ≅
      𝟭 (SheafOfModulesOfCommRing R) :=
  Functor.isoWhiskerLeft (toPresheaf R)
      (Functor.isoWhiskerRight (leftUnitorNatIso
        (PresheafOfModulesOfCommRing.{u} R.obj)) (associatedSheaf R)) ≪≫
    asIso (PresheafOfModules.sheafificationAdjunction
      (R := ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (𝟙 _)).counit

/-- The unit comparison retains the original presheaf unitor and sheafification counit. -/
theorem tensorLeftUnitIso_hom_app (M : SheafOfModulesOfCommRing R) :
    (tensorLeftUnitIso R).hom.app M =
      (associatedSheaf R).map (λ_ ((toPresheaf R).obj M)).hom ≫
        (PresheafOfModules.sheafificationAdjunction
          (R := ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
          (𝟙 _)).counit.app M := rfl

/-- The first-variable tensor map is natural in the original second-variable maps. -/
theorem tensorFunctor_naturality {M N P Q : SheafOfModulesOfCommRing R}
    (f : M ⟶ N) (g : P ⟶ Q) :
    (tensorLeftFunctor R M).map g ≫ ((tensorFunctor R).map f).app Q =
      ((tensorFunctor R).map f).app P ≫ (tensorLeftFunctor R N).map g :=
  ((tensorFunctor R).map f).naturality g

/-- The inverse unit comparison retains the original inverse counit and presheaf unitor. -/
theorem tensorLeftUnitIso_inv_app (M : SheafOfModulesOfCommRing R) :
    (tensorLeftUnitIso R).inv.app M =
      inv ((PresheafOfModules.sheafificationAdjunction
        (R := ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
        (𝟙 _)).counit.app M) ≫
      (associatedSheaf R).map (λ_ ((toPresheaf R).obj M)).inv := by
  simp [tensorLeftUnitIso]

/-- The actual presheaf braiding followed by module sheafification. -/
def tensorBraiding (M N : SheafOfModulesOfCommRing R) :
    (tensorLeftFunctor R M).obj N ≅ (tensorLeftFunctor R N).obj M :=
  (associatedSheaf R).mapIso
    (CategoryTheory.BraidedCategory.braiding ((toPresheaf R).obj M) ((toPresheaf R).obj N))

end SheafOfModulesOfCommRing
