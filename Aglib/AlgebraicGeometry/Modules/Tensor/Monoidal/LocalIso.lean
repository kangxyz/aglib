/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.PresheafTensor
public import Aglib.Algebra.Category.ModuleCat.Sheaf.TensorPushforward
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.CategoryTheory.Localization.Monoidal.Basic

/-!
# Local isomorphisms of module presheaves are stable under tensor products

For a scheme `X`, `Scheme.Modules.presheafLocalIso X` is the class of morphisms of module
presheaves over the structure sheaf whose underlying morphisms of abelian presheaves are in
`GrothendieckTopology.W`, i.e. become isomorphisms after sheafification. Equivalently, module
sheafification `SheafOfModulesOfCommRing.associatedSheaf X.sheaf` sends them to isomorphisms
(`presheafLocalIso_iff`), and precomposition with them is bijective on morphisms into the
underlying presheaf of every module sheaf (`presheafLocalIso_iff_bijective`). The
sheafification unit `SheafOfModulesOfCommRing.associatedSheafUnit X.sheaf` lies in the class
(`presheafLocalIso_unit`), and module sheafification is a localization at the class
(`isLocalization_associatedSheaf`).

The class is monoidal (`MorphismProperty.IsMonoidal`) for Mathlib's pointwise tensor product
on `PresheafOfModulesOfCommRing X.sheaf.obj`. Stability under `P ◁ -`
(`presheafLocalIso_whiskerLeft`) follows from the tensor–Hom bijection
`InternalHom.PresheafSource.tensorHomEquiv` into the presheaf-source Hom sheaf, as in
Mathlib's `GrothendieckTopology.W.whiskerLeft` for presheaves with values in a closed monoidal
category. Stability under `- ▷ Q` (`presheafLocalIso_whiskerRight`) follows through the
symmetric braiding. No hypothesis is imposed on the scheme or the module presheaves.

Declarations whose proofs mix the coefficient rings `X.sheaf.obj ⋙ forget₂ CommRingCat RingCat`
and `X.ringCatSheaf.obj` set `backward.isDefEq.respectTransparency false` locally: these rings
agree only after unfolding the semireducible `sheafCompose`. Consumers need no such option to
find the instances, for `presheafLocalIso X` or for its unfolded expression.
-/

@[expose] public section

noncomputable section
open CategoryTheory MonoidalCategory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
universe u

/-- Morphisms of module presheaves on `X` that become isomorphisms after sheafification. -/
abbrev presheafLocalIso (X : Scheme.{u}) :
    MorphismProperty (PresheafOfModulesOfCommRing.{u} X.sheaf.obj) :=
  (Opens.grothendieckTopology X).W.inverseImage (PresheafOfModules.toPresheaf X.ringCatSheaf.obj)

variable {X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- A morphism of module presheaves is a local isomorphism if and only if its module
sheafification is an isomorphism. -/
theorem presheafLocalIso_iff {P Q : PresheafOfModulesOfCommRing.{u} X.sheaf.obj} (f : P ⟶ Q) :
    presheafLocalIso X f ↔ IsIso ((SheafOfModulesOfCommRing.associatedSheaf X.sheaf).map f) := by
  have h := PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
    (J := Opens.grothendieckTopology X) (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)
  exact Iff.of_eq (congrArg
    (fun (V : MorphismProperty (_root_.PresheafOfModules.{u} X.ringCatSheaf.obj)) => V f) h)

set_option backward.isDefEq.respectTransparency false in
/-- The unit of module sheafification is a local isomorphism. -/
theorem presheafLocalIso_unit (P : PresheafOfModulesOfCommRing.{u} X.sheaf.obj) :
    presheafLocalIso X ((SheafOfModulesOfCommRing.associatedSheafUnit X.sheaf).app P) := by
  rw [presheafLocalIso_iff]
  exact isIso_of_comp_hom_eq_id _ ((PresheafOfModules.sheafificationAdjunction
    (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).left_triangle_components P)

set_option backward.isDefEq.respectTransparency false in
/-- A morphism of module presheaves is a local isomorphism if and only if precomposition
with it is bijective on morphisms into the underlying presheaf of every module sheaf. -/
theorem presheafLocalIso_iff_bijective {P Q : PresheafOfModulesOfCommRing.{u} X.sheaf.obj}
    (f : P ⟶ Q) :
    presheafLocalIso X f ↔ ∀ N : X.Modules, Function.Bijective (fun g : Q ⟶ N.val => f ≫ g) := by
  let adj := PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
    (𝟙 X.ringCatSheaf.obj)
  refine (presheafLocalIso_iff f).trans ((isIso_iff_coyoneda_map_bijective _).trans
    (forall_congr' fun N => ?_))
  have key : (fun g : Q ⟶ N.val => f ≫ g) =
      (adj.homEquiv P N) ∘ (fun x => (SheafOfModulesOfCommRing.associatedSheaf X.sheaf).map f ≫ x) ∘
        (adj.homEquiv Q N).symm := by
    funext g
    exact ((adj.homEquiv_naturality_left f ((adj.homEquiv Q N).symm g)).trans
      (congrArg (fun y => f ≫ y) ((adj.homEquiv Q N).apply_symm_apply g))).symm
  rw [key]
  exact ((Equiv.comp_bijective _ (adj.homEquiv P N)).trans
    (Equiv.bijective_comp (adj.homEquiv Q N).symm _)).symm

set_option backward.isDefEq.respectTransparency false in
/-- Local isomorphisms of module presheaves are stable under `P ◁ -`. -/
theorem presheafLocalIso_whiskerLeft (P : PresheafOfModulesOfCommRing.{u} X.sheaf.obj)
    {Q₁ Q₂ : PresheafOfModulesOfCommRing.{u} X.sheaf.obj} (g : Q₁ ⟶ Q₂)
    (hg : presheafLocalIso X g) : presheafLocalIso X (P ◁ g) := by
  rw [presheafLocalIso_iff_bijective] at hg ⊢
  intro N
  have key : (fun h : P ⊗ Q₂ ⟶ N.val => P ◁ g ≫ h) =
      (InternalHom.PresheafSource.tensorHomEquiv X P Q₁ N).symm ∘
        (fun k => g ≫ k) ∘ (InternalHom.PresheafSource.tensorHomEquiv X P Q₂ N) := by
    funext h
    apply (InternalHom.PresheafSource.tensorHomEquiv X P Q₁ N).injective
    exact (InternalHom.PresheafSource.tensorHomEquiv_whiskerLeft_comp g h).trans
      ((InternalHom.PresheafSource.tensorHomEquiv X P Q₁ N).apply_symm_apply _).symm
  rw [key, Equiv.comp_bijective, Equiv.bijective_comp]
  exact hg (InternalHom.PresheafSource.sheaf X P N)

set_option backward.isDefEq.respectTransparency false in
/-- Local isomorphisms of module presheaves are closed under isomorphisms of arrows. -/
instance presheafLocalIso_respectsIso : (presheafLocalIso X).RespectsIso :=
  inferInstanceAs ((Opens.grothendieckTopology X).W.inverseImage
    (_root_.PresheafOfModules.toPresheaf X.ringCatSheaf.obj)).RespectsIso

/-- Local isomorphisms of module presheaves are stable under `- ▷ Q`. -/
theorem presheafLocalIso_whiskerRight {P₁ P₂ : PresheafOfModulesOfCommRing.{u} X.sheaf.obj}
    (f : P₁ ⟶ P₂) (hf : presheafLocalIso X f) (Q : PresheafOfModulesOfCommRing.{u} X.sheaf.obj) :
    presheafLocalIso X (f ▷ Q) :=
  ((presheafLocalIso X).arrow_mk_iso_iff (Arrow.isoMk (β_ P₁ Q) (β_ P₂ Q)
    (BraidedCategory.braiding_naturality_left f Q).symm)).2 (presheafLocalIso_whiskerLeft Q f hf)

set_option backward.isDefEq.respectTransparency false in
/-- Local isomorphisms of module presheaves are closed under identities and composition. -/
instance presheafLocalIso_isMultiplicative : (presheafLocalIso X).IsMultiplicative :=
  inferInstanceAs ((Opens.grothendieckTopology X).W.inverseImage
    (_root_.PresheafOfModules.toPresheaf X.ringCatSheaf.obj)).IsMultiplicative

/-- Local isomorphisms of module presheaves are stable under tensor products. -/
instance presheafLocalIso_isMonoidal : (presheafLocalIso X).IsMonoidal where
  whiskerLeft P _ _ g hg := presheafLocalIso_whiskerLeft P g hg
  whiskerRight f hf Q := presheafLocalIso_whiskerRight f hf Q

-- Mathlib's instance is stated on the `X.ringCatSheaf.obj` spelling of module presheaves; matching
-- it with the commutative-ring spelling needs the transparency override.
variable (X) in
set_option backward.isDefEq.respectTransparency false in
/-- Module sheafification is a localization at the local isomorphisms of module presheaves. -/
instance isLocalization_associatedSheaf :
    (SheafOfModulesOfCommRing.associatedSheaf X.sheaf).IsLocalization (presheafLocalIso X) :=
  inferInstanceAs
    ((_root_.PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 _)).IsLocalization _)

end AlgebraicGeometry.Scheme.Modules
