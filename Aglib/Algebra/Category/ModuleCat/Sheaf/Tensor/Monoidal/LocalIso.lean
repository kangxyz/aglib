/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.Tensor.Monoidal.Objects
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.CategoryTheory.Localization.Monoidal.Basic

/-! # The actual localization class of ringed-site module presheaves

These localization and unit facts do not assume tensor stability. The later
coherence construction explicitly requires that this actual class is monoidal.
The module carrier remains the ring carrier universe, independently of the
site object and morphism universes.
-/

@[expose] public noncomputable section

universe uC vC uR

open CategoryTheory MonoidalCategory

namespace SheafOfModulesOfCommRing

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{uR} RingCat.{uR})]
  (R : Sheaf J CommRingCat.{uR}) [HasSheafify J AddCommGrpCat.{uR}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{uR}]

/-- The original local-isomorphism class on module presheaves. -/
abbrev presheafLocalIso : MorphismProperty (PresheafOfModulesOfCommRing.{uR} R.obj) :=
  J.W.inverseImage (PresheafOfModules.toPresheaf
    ((sheafCompose J (forget₂ CommRingCat.{uR} RingCat.{uR})).obj R).obj)

/-- The actual module sheafification detects precisely this localization class. -/
theorem presheafLocalIso_iff {P Q : PresheafOfModulesOfCommRing.{uR} R.obj} (f : P ⟶ Q) :
    presheafLocalIso R f ↔ IsIso ((associatedSheaf R).map f) := by
  have h := PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
    (J := J) (R := (sheafCompose J (forget₂ CommRingCat.{uR} RingCat.{uR})).obj R) (𝟙 _)
  exact Iff.of_eq (congrArg
    (fun V : MorphismProperty (PresheafOfModulesOfCommRing.{uR} R.obj) => V f) h)

/-- The original module-sheafification unit is a local isomorphism. -/
theorem presheafLocalIso_unit (P : PresheafOfModulesOfCommRing.{uR} R.obj) :
    presheafLocalIso R ((associatedSheafUnit R).app P) := by
  rw [presheafLocalIso_iff]
  have hε : IsIso ((PresheafOfModules.sheafificationAdjunction
      (R := (sheafCompose J (forget₂ CommRingCat.{uR} RingCat.{uR})).obj R)
      (𝟙 _)).counit.app ((associatedSheaf R).obj P)) :=
    inferInstanceAs (IsIso (sheafifyForgetIso R ((associatedSheaf R).obj P)).hom)
  exact @isIso_of_comp_hom_eq_id _ _ _ _ _ hε _
    ((PresheafOfModules.sheafificationAdjunction
      (R := (sheafCompose J (forget₂ CommRingCat.{uR} RingCat.{uR})).obj R)
      (𝟙 _)).left_triangle_components P)

/-- Local isomorphisms are exactly the maps inducing bijections into actual sheaves. -/
theorem presheafLocalIso_iff_bijective {P Q : PresheafOfModulesOfCommRing.{uR} R.obj}
    (f : P ⟶ Q) :
    presheafLocalIso R f ↔ ∀ N : SheafOfModulesOfCommRing R,
      Function.Bijective (fun g : Q ⟶ N.val => f ≫ g) := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat.{uR} RingCat.{uR})).obj R) (𝟙 _)
  refine (presheafLocalIso_iff R f).trans ((isIso_iff_coyoneda_map_bijective _).trans
    (forall_congr' fun N => ?_))
  have key : (fun g : Q ⟶ N.val => f ≫ g) =
      (adj.homEquiv P N) ∘ (fun x => (associatedSheaf R).map f ≫ x) ∘
        (adj.homEquiv Q N).symm := by
    funext g
    exact ((adj.homEquiv_naturality_left f ((adj.homEquiv Q N).symm g)).trans
      (congrArg (fun y => f ≫ y) ((adj.homEquiv Q N).apply_symm_apply g))).symm
  rw [key]
  exact ((Equiv.comp_bijective _ (adj.homEquiv P N)).trans
    (Equiv.bijective_comp (adj.homEquiv Q N).symm _)).symm

instance presheafLocalIso_respectsIso : (presheafLocalIso R).RespectsIso :=
  inferInstanceAs (J.W.inverseImage (PresheafOfModules.toPresheaf
    ((sheafCompose J (forget₂ CommRingCat.{uR} RingCat.{uR})).obj R).obj)).RespectsIso

instance presheafLocalIso_isMultiplicative : (presheafLocalIso R).IsMultiplicative :=
  inferInstanceAs (J.W.inverseImage (PresheafOfModules.toPresheaf
    ((sheafCompose J (forget₂ CommRingCat.{uR} RingCat.{uR})).obj R).obj)).IsMultiplicative

/-- Native module sheafification is a localization at the actual local isomorphisms. -/
instance isLocalization_associatedSheaf :
    (associatedSheaf R).IsLocalization (presheafLocalIso R) := by
  change (PresheafOfModules.sheafification.{uR}
    (R := (sheafCompose J (forget₂ CommRingCat.{uR} RingCat.{uR})).obj R)
    (𝟙 _)).IsLocalization (J.W.inverseImage (PresheafOfModules.toPresheaf
      ((sheafCompose J (forget₂ CommRingCat.{uR} RingCat.{uR})).obj R).obj))
  rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
    (J := J) (R := (sheafCompose J (forget₂ CommRingCat.{uR} RingCat.{uR})).obj R) (𝟙 _)]
  exact (PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat.{uR} RingCat.{uR})).obj R)
    (𝟙 _)).isLocalization

end SheafOfModulesOfCommRing
