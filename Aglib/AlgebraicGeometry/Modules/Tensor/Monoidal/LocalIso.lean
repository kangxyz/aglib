/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.PresheafTensor
public import Aglib.Algebra.Category.ModuleCat.Sheaf.Tensor.Monoidal.LocalIso
public import Aglib.Algebra.Category.ModuleCat.Sheaf.Tensor.Monoidal.Stability
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
symmetric braiding. These stability results and the monoidality instance specialize the actual
generic supplier in the native `(u,u,u)` universe sector. No hypothesis is imposed on the
scheme or the module presheaves.

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
  SheafOfModulesOfCommRing.presheafLocalIso X.sheaf

variable {X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- A morphism of module presheaves is a local isomorphism if and only if its module
sheafification is an isomorphism. -/
theorem presheafLocalIso_iff {P Q : PresheafOfModulesOfCommRing.{u} X.sheaf.obj} (f : P ⟶ Q) :
    presheafLocalIso X f ↔ IsIso ((SheafOfModulesOfCommRing.associatedSheaf X.sheaf).map f) := by
  exact SheafOfModulesOfCommRing.presheafLocalIso_iff X.sheaf f

set_option backward.isDefEq.respectTransparency false in
/-- The unit of module sheafification is a local isomorphism. -/
theorem presheafLocalIso_unit (P : PresheafOfModulesOfCommRing.{u} X.sheaf.obj) :
    presheafLocalIso X ((SheafOfModulesOfCommRing.associatedSheafUnit X.sheaf).app P) := by
  exact SheafOfModulesOfCommRing.presheafLocalIso_unit X.sheaf P

set_option backward.isDefEq.respectTransparency false in
/-- A morphism of module presheaves is a local isomorphism if and only if precomposition
with it is bijective on morphisms into the underlying presheaf of every module sheaf. -/
theorem presheafLocalIso_iff_bijective {P Q : PresheafOfModulesOfCommRing.{u} X.sheaf.obj}
    (f : P ⟶ Q) :
    presheafLocalIso X f ↔ ∀ N : X.Modules, Function.Bijective (fun g : Q ⟶ N.val => f ≫ g) := by
  exact SheafOfModulesOfCommRing.presheafLocalIso_iff_bijective X.sheaf f

set_option backward.isDefEq.respectTransparency false in
/-- Local isomorphisms of module presheaves are stable under `P ◁ -`. -/
theorem presheafLocalIso_whiskerLeft (P : PresheafOfModulesOfCommRing.{u} X.sheaf.obj)
    {Q₁ Q₂ : PresheafOfModulesOfCommRing.{u} X.sheaf.obj} (g : Q₁ ⟶ Q₂)
    (hg : presheafLocalIso X g) : presheafLocalIso X (P ◁ g) := by
  exact SheafOfModulesOfCommRing.presheafLocalIso_whiskerLeft.{u, u, u}
    (C := X.Opens) (J := _root_.Opens.grothendieckTopology X) X.sheaf P g hg

set_option backward.isDefEq.respectTransparency false in
/-- Local isomorphisms of module presheaves are closed under isomorphisms of arrows. -/
instance presheafLocalIso_respectsIso : (presheafLocalIso X).RespectsIso :=
  SheafOfModulesOfCommRing.presheafLocalIso_respectsIso X.sheaf

set_option backward.isDefEq.respectTransparency false in
/-- Local isomorphisms of module presheaves are stable under `- ▷ Q`. -/
theorem presheafLocalIso_whiskerRight {P₁ P₂ : PresheafOfModulesOfCommRing.{u} X.sheaf.obj}
    (f : P₁ ⟶ P₂) (hf : presheafLocalIso X f) (Q : PresheafOfModulesOfCommRing.{u} X.sheaf.obj) :
    presheafLocalIso X (f ▷ Q) :=
  SheafOfModulesOfCommRing.presheafLocalIso_whiskerRight.{u, u, u}
    (C := X.Opens) (J := _root_.Opens.grothendieckTopology X) X.sheaf Q f hf

set_option backward.isDefEq.respectTransparency false in
/-- Local isomorphisms of module presheaves are closed under identities and composition. -/
instance presheafLocalIso_isMultiplicative : (presheafLocalIso X).IsMultiplicative :=
  SheafOfModulesOfCommRing.presheafLocalIso_isMultiplicative X.sheaf

set_option backward.isDefEq.respectTransparency false in
/-- Local isomorphisms of module presheaves are stable under tensor products. -/
instance presheafLocalIso_isMonoidal : (presheafLocalIso X).IsMonoidal :=
  SheafOfModulesOfCommRing.presheafLocalIso_isMonoidal.{u, u, u}
    (C := X.Opens) (J := _root_.Opens.grothendieckTopology X) X.sheaf

-- Mathlib's instance is stated on the `X.ringCatSheaf.obj` spelling of module presheaves; matching
-- it with the commutative-ring spelling needs the transparency override.
variable (X) in
set_option backward.isDefEq.respectTransparency false in
/-- Module sheafification is a localization at the local isomorphisms of module presheaves. -/
instance isLocalization_associatedSheaf :
    (SheafOfModulesOfCommRing.associatedSheaf X.sheaf).IsLocalization (presheafLocalIso X) :=
  SheafOfModulesOfCommRing.isLocalization_associatedSheaf X.sheaf

end AlgebraicGeometry.Scheme.Modules
