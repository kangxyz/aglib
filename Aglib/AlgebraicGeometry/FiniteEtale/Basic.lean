/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# The category of finite etale schemes over a scheme

Objects are actual finite etale morphisms to an arbitrary scheme. Arrows are all
morphisms over that scheme. No surjectivity is imposed, so empty covers are allowed.
The canonical full subcategory maps fully faithfully to the existing small etale site.

Source: R5Lab/AlgebraicGeometry/FiniteEtale/Basic.lean
at R5 revision 2f9ca464b192cff865858dda70b2d8e5dca8b3df.
SHA256: 448735e35852bb729246eb18dcba2285554c59e506ec1d3bf966e36207719c48
Selection: the finite-etale object property, full subcategory and actual forgetful/site maps.
Actual objects, maps, universes and hypotheses are retained.
-/
@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u

namespace AlgebraicGeometry.Scheme

/-- The property of a scheme over `X` being finite and étale. -/
def finiteEtaleProperty (X : Scheme.{u}) : ObjectProperty (Over X) :=
  fun Y => IsFinite Y.hom ∧ Etale Y.hom

/-- The full subcategory of `Over X` consisting of finite étale morphisms. -/
abbrev FiniteEtale (X : Scheme.{u}) := (finiteEtaleProperty X).FullSubcategory

namespace FiniteEtale

instance {X : Scheme.{u}} (Y : FiniteEtale X) : IsFinite Y.obj.hom := Y.property.1
instance {X : Scheme.{u}} (Y : FiniteEtale X) : Etale Y.obj.hom := Y.property.2

/-- Construct a finite étale cover from its structural scheme morphism. -/
abbrev mk {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Etale f] : FiniteEtale X :=
  ⟨Over.mk f, by exact ⟨‹IsFinite f›, ‹Etale f›⟩⟩

/-- The fully faithful inclusion into schemes over `X`. -/
def forget (X : Scheme.{u}) : FiniteEtale X ⥤ Over X := (finiteEtaleProperty X).ι

instance (X : Scheme.{u}) : (forget X).Full := ObjectProperty.full_ι _
instance (X : Scheme.{u}) : (forget X).Faithful := ObjectProperty.faithful_ι _

/-- Forget the structural morphism to `X`. -/
def forgetToScheme (X : Scheme.{u}) : FiniteEtale X ⥤ Scheme.{u} :=
  forget X ⋙ Over.forget X

instance (X : Scheme.{u}) : (forgetToScheme X).Faithful := by
  dsimp [forgetToScheme]
  infer_instance

@[simp] theorem forgetToScheme_obj (X : Scheme.{u}) (Y : FiniteEtale X) :
    (forgetToScheme X).obj Y = Y.obj.left := rfl

@[simp] theorem forgetToScheme_map {X : Scheme.{u}} {Y Z : FiniteEtale X} (f : Y ⟶ Z) :
    (forgetToScheme X).map f = f.hom.left := rfl

/-- The fully faithful inclusion into the category underlying the small étale site. -/
def toEtale (X : Scheme.{u}) : FiniteEtale X ⥤ X.Etale where
  obj Y := Scheme.Etale.mk Y.obj.hom
  map f := MorphismProperty.Over.homMk f.hom.left (Over.w f.hom) (by trivial)

/-- Forgetting from the small etale site recovers the actual inclusion into `Over X`. -/
def toEtaleForgetIso (X : Scheme.{u}) : toEtale X ⋙ Scheme.Etale.forget X ≅ forget X :=
  Iso.refl _

instance (X : Scheme.{u}) : (toEtale X).Full :=
  Functor.Full.of_comp_faithful_iso (toEtaleForgetIso X)

instance (X : Scheme.{u}) : (toEtale X).Faithful :=
  Functor.Faithful.of_comp_iso (toEtaleForgetIso X)

@[simp] theorem toEtale_obj_hom (X : Scheme.{u}) (Y : FiniteEtale X) :
    ((toEtale X).obj Y).hom = Y.obj.hom := rfl

end FiniteEtale

end AlgebraicGeometry.Scheme
