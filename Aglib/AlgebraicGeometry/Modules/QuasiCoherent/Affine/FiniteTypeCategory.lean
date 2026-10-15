/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Category.ModuleCat.Finite
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Abelian.Transfer
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
/-!
# Quasicoherent sheaves of finite type on affine schemes

We use the actual full subcategory of quasicoherent `𝒪_{Spec R}`-modules and
its equivalence with `R`-modules. Coherence on a noetherian affine scheme is
expressed by finite generation of the global-sections module. In particular,
these objects contain an actual sheaf on `Spec R`, and their morphisms are
actual morphisms of sheaves.

The coherent objects form a Serre class in quasicoherent sheaves. No claim
is made that they form a Serre class in all sheaves of modules: arbitrary
subsheaves need not be quasicoherent. General non-affine noetherian schemes
and the comparison with locally finitely presented sheaves require further
local-to-global results.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.ExactCategory
open ModuleCat
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent

variable (R : CommRingCat.{u})

/-- The actual quasicoherent sheaves on `Spec R`. -/
abbrev AffineQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory

instance affineQuasicoherent_hasFiniteLimits : HasFiniteLimits (AffineQuasicoherent R) where
  out _ := Adjunction.hasLimitsOfShape_of_equivalence (tildeEquiv (R := R)).inverse

/-- Quasicoherent sheaves on an affine scheme are an abelian category. -/
instance instAbelianAffineQuasicoherent : Abelian (AffineQuasicoherent R) :=
  abelianOfEquivalence (tildeEquiv (R := R)).inverse

/-- The condition that the global-sections module of an affine quasicoherent
sheaf is finite. This becomes coherence when the base ring is noetherian. -/
def affineFiniteType : ObjectProperty (AffineQuasicoherent R) :=
  (finiteModule R).inverseImage (tildeEquiv (R := R)).inverse

@[simp]
lemma affineFiniteType_iff (M : AffineQuasicoherent R) :
    affineFiniteType R M ↔ Module.Finite R (moduleSpecΓFunctor.obj M.obj) := Iff.rfl

instance affineFiniteType_isoClosed : (affineFiniteType R).IsClosedUnderIsomorphisms := by
  change ((finiteModule R).inverseImage (tildeEquiv (R := R)).inverse).IsClosedUnderIsomorphisms
  infer_instance

/-- Quasicoherent sheaves on `Spec R` whose global-sections module is finite.
This full subcategory is defined over every ring; its abelian and Serre
properties below assume the ring is noetherian. -/
abbrev AffineFiniteType (R : CommRingCat.{u}) :=
  (affineFiniteType R).FullSubcategory

/-- The fully faithful inclusion into all sheaves of modules on `Spec R`. -/
def affineFiniteTypeToModules : AffineFiniteType R ⥤ (Spec R).Modules :=
  (affineFiniteType R).ι ⋙ (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).ι

instance : (affineFiniteTypeToModules R).Full := inferInstanceAs (Functor.Full (_ ⋙ _))
instance : (affineFiniteTypeToModules R).Faithful := inferInstanceAs (Functor.Faithful (_ ⋙ _))

instance (M : AffineFiniteType R) :
    ((affineFiniteTypeToModules R).obj M).IsQuasicoherent := M.obj.property

instance (M : AffineFiniteType R) :
    Module.Finite R (moduleSpecΓFunctor.obj ((affineFiniteTypeToModules R).obj M)) := M.property

/-- Global sections and tilde identify affine quasicoherent sheaves of finite
type with finite `R`-modules, over any ring. -/
def affineFiniteTypeModuleEquivalence : AffineFiniteType R ≌ FiniteModule.{u, u} R :=
  (tildeEquiv (R := R)).symm.congrFullSubcategory rfl

/-- Affine quasicoherent sheaves of finite type have a small model in the
universe of the base ring, using actual finite module representatives. -/
instance affineFiniteType_essentiallySmall : EssentiallySmall.{u} (AffineFiniteType R) :=
  essentiallySmall_of_fully_faithful (affineFiniteTypeModuleEquivalence R).functor

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent
