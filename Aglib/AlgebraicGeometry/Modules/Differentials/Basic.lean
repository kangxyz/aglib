/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/- Interface migration basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original mathematical and construction source identities are retained. -/
/-!
# Actual differentials of schemes over a field

The differential presheaf is mathlib's universal Kähler differential module
on the actual structure sections relative to the canonical constant map.
Its module-sheafification is constructed explicitly and proved to represent
F-derivations with values in every actual structure-module sheaf. The
canonical map f*Ω_Y/F → Ω_X/F is induced by the structural pullback of
sections; its adjoint sends d(a) to d(f# a), preserves identities, and composes.

No smoothness, rank, degree, cohomology, or Riemann–Hurwitz premise is used in
these constructions. In particular, no arbitrary sheaf of differentials is
supplied. Smooth local rank and canonical degree are downstream obligations.
Source correspondence: Stacks01UQ, Definition29.33.1, with the universal
derivation construction in Modules17.28; inspected2026-10-09.
Application K2-018#prop:k2018-arithmetic-characters, expose.tex lines341–445,
source e73d98b1b5c1e5abcdebf7d058e436d792b87982; frozen engineering basis
7f86e4a1763cc4ec35e9b0a8acd659750355a0de and unchanged pins.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.OverField
namespace AlgebraicGeometry.Scheme.Modules.Differentials
universe u
variable {F : Type u} [Field F]

/-- Canonical constants on every actual Zariski open. -/
def constantsPresheafMap (X : FScheme F) :
    (Functor.const X.left.Opensᵒᵖ).obj (CommRingCat.of F) ⟶ X.left.presheaf where
  app U := CommRingCat.ofHom (constantSection X U.unop)
  naturality U V i := by
    ext a
    exact (map_constantSection X i.unop a).symm

/-- Sectionwise Kähler differential modules with their canonical restrictions. -/
abbrev differentialPresheaf (X : FScheme F) : X.left.PresheafOfModules :=
  PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'
    (constantsPresheafMap X)

/-- The actual sheafification of the structure-module differential presheaf. -/
def differentialSheaf (X : FScheme F) : X.left.Modules :=
  (_root_.PresheafOfModules.sheafification (𝟙 X.left.ringCatSheaf.obj)).obj (differentialPresheaf X)

/-- The universal sectionwise derivation. -/
def presheafDerivation (X : FScheme F) :
    PresheafOfModulesOfCommRing.Derivation' (differentialPresheaf X) (constantsPresheafMap X) :=
  PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation' (constantsPresheafMap X)

/-- The actual presheaf universal property, inherited from Kähler differentials. -/
def presheafDerivationUniversal (X : FScheme F) : (presheafDerivation X).Universal :=
  PresheafOfModulesOfCommRing.DifferentialsConstruction.isUniversal' (constantsPresheafMap X)

end AlgebraicGeometry.Scheme.Modules.Differentials
namespace AlgebraicGeometry.Scheme.Modules.Differentials
universe u
variable {F : Type u} [Field F]
/-- Presheaf linear maps are precisely actual F-derivations. -/
def presheafDifferentialHomEquiv (X : FScheme F) (M : X.left.PresheafOfModules) :
    (differentialPresheaf X ⟶ M) ≃
      PresheafOfModulesOfCommRing.Derivation' M (constantsPresheafMap X) where
  toFun a := (presheafDerivation X).postcomp a
  invFun d := (presheafDerivationUniversal X).desc d
  left_inv a := by
    apply (presheafDerivationUniversal X).postcomp_injective
    exact (presheafDerivationUniversal X).fac _
  right_inv d := (presheafDerivationUniversal X).fac d

/-- The constructed differential sheaf represents F-derivations into every module sheaf. -/
def differentialSheafHomEquiv (X : FScheme F) (M : X.left.Modules) :
    (differentialSheaf X ⟶ M) ≃
      PresheafOfModulesOfCommRing.Derivation' M.val (constantsPresheafMap X) :=
  (_root_.PresheafOfModules.sheafificationHomEquiv (𝟙 X.left.ringCatSheaf.obj)).trans
    (presheafDifferentialHomEquiv X M.val)
end AlgebraicGeometry.Scheme.Modules.Differentials
namespace AlgebraicGeometry.Scheme.Modules.Differentials
universe u
variable {F : Type u} [Field F]
/-- The universal derivation into the actual differential sheaf. -/
def differentialSheafDerivation (X : FScheme F) :
    PresheafOfModulesOfCommRing.Derivation' (differentialSheaf X).val (constantsPresheafMap X) :=
  differentialSheafHomEquiv X (differentialSheaf X) (𝟙 _)

variable {X Y : FScheme F} (f : X ⟶ Y)
/-- Pullback of structure sections followed by the universal differential. -/
def differentialPushforwardDerivation :
    PresheafOfModulesOfCommRing.Derivation'
      ((Scheme.Modules.pushforward f.left).obj (differentialSheaf X)).val
      (constantsPresheafMap Y) where
  d {U} := (differentialSheafDerivation X).d.comp (f.left.app U.unop).hom.toAddMonoidHom
  d_mul {U} a b := by
    exact (congrArg (differentialSheafDerivation X).d ((f.left.app U.unop).hom.map_mul a b)).trans
      ((differentialSheafDerivation X).d_mul _ _)
  d_map {U V} i a := by
    have h : f.left.app V.unop (Y.left.presheaf.map i a) =
        X.left.presheaf.map ((TopologicalSpace.Opens.map f.left.base).map i.unop).op
          (f.left.app U.unop a) :=
      congrArg (fun g : Γ(Y.left, U.unop) ⟶ Γ(X.left, f.left ⁻¹ᵁ V.unop) ↦ g.hom a)
        (f.left.c.naturality i)
    exact (congrArg (differentialSheafDerivation X).d h).trans
      ((differentialSheafDerivation X).d_map _ _)
  d_app {U} a := by
    exact (congrArg (differentialSheafDerivation X).d
      (Cohomology.app_constantSection f U.unop a)).trans
        ((differentialSheafDerivation X).d_app a)

/-- The canonical adjoint differential map Ω_Y → f_*Ω_X. -/
def differentialPushforwardMap :
    differentialSheaf Y ⟶ (Scheme.Modules.pushforward f.left).obj (differentialSheaf X) :=
  (differentialSheafHomEquiv Y _).symm (differentialPushforwardDerivation f)

/-- The actual canonical map f*Ω_Y → Ω_X, as the adjoint of section pullback. -/
def differentialPullbackMap :
    (Scheme.Modules.pullback f.left).obj (differentialSheaf Y) ⟶ differentialSheaf X :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f.left).homEquiv _ _).symm
    (differentialPushforwardMap f)
end AlgebraicGeometry.Scheme.Modules.Differentials
namespace AlgebraicGeometry.Scheme.Modules.Differentials
universe u
variable {F : Type u} [Field F]
theorem differentialSheafHomEquiv_apply (X : FScheme F) (M : X.left.Modules)
    (h : differentialSheaf X ⟶ M) (U : X.left.Opensᵒᵖ) (a : X.left.presheaf.obj U) :
    (differentialSheafHomEquiv X M h).d a =
      h.val.app U ((differentialSheafDerivation X).d a) := rfl

variable {X Y : FScheme F} (f : X ⟶ Y)
@[simp]
theorem differentialPushforwardMap_d (U : Y.left.Opens) (a : Γ(Y.left, U)) :
    (differentialPushforwardMap f).val.app (op U) ((differentialSheafDerivation Y).d a) =
      (differentialSheafDerivation X).d (f.left.app U a) := by
  have h := congrArg (fun d ↦ d.d a)
    ((differentialSheafHomEquiv Y _).apply_symm_apply (differentialPushforwardDerivation f))
  rw [differentialSheafHomEquiv_apply] at h
  exact h

@[simp]
theorem differentialPullbackMap_adjoint :
    (Scheme.Modules.pullbackPushforwardAdjunction f.left).homEquiv _ _
      (differentialPullbackMap f) = differentialPushforwardMap f :=
  Equiv.apply_symm_apply _ _
end AlgebraicGeometry.Scheme.Modules.Differentials
namespace AlgebraicGeometry.Scheme.Modules.Differentials
universe u
variable {F : Type u} [Field F]
theorem differentialSheaf_hom_ext (X : FScheme F) (M : X.left.Modules)
    {f g : differentialSheaf X ⟶ M}
    (h : ∀ (U : X.left.Opensᵒᵖ) (a : X.left.presheaf.obj U),
      f.val.app U ((differentialSheafDerivation X).d a) =
        g.val.app U ((differentialSheafDerivation X).d a)) : f = g := by
  apply (differentialSheafHomEquiv X M).injective
  ext U a
  exact h U a

@[simp]
theorem differentialPushforwardMap_id (X : FScheme F) :
    differentialPushforwardMap (𝟙 X) ≫
      (Scheme.Modules.pushforwardId X.left).hom.app (differentialSheaf X) = 𝟙 _ := by
  apply differentialSheaf_hom_ext X _
  intro U a
  change (differentialPushforwardMap (𝟙 X)).val.app U ((differentialSheafDerivation X).d a) = _
  exact differentialPushforwardMap_d (𝟙 X) U.unop a

@[reassoc]
theorem differentialPushforwardMap_comp {X Y Z : FScheme F} (f : X ⟶ Y) (g : Y ⟶ Z) :
    differentialPushforwardMap (f ≫ g) =
      differentialPushforwardMap g ≫
        (Scheme.Modules.pushforward g.left).map (differentialPushforwardMap f) ≫
          (Scheme.Modules.pushforwardComp f.left g.left).hom.app (differentialSheaf X) := by
  apply differentialSheaf_hom_ext Z _
  intro U a
  change (differentialPushforwardMap (f ≫ g)).val.app U ((differentialSheafDerivation Z).d a) =
    (differentialPushforwardMap f).val.app _
      ((differentialPushforwardMap g).val.app U ((differentialSheafDerivation Z).d a))
  rw [differentialPushforwardMap_d, differentialPushforwardMap_d]
  exact (differentialPushforwardMap_d f (g.left ⁻¹ᵁ U.unop) (g.left.app U.unop a)).symm
end AlgebraicGeometry.Scheme.Modules.Differentials
