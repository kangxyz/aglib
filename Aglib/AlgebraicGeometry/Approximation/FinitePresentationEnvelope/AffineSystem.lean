/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Approximation.FinitePresentationEnvelope.System
public import Aglib.RingTheory.FiniteType.SubalgebraColimit

/-!
# Arithmetic approximation of affine schemes

Finite subsets of the original coordinate ring generate a filtered diagram of finite-type
arithmetic subalgebras. Applying the spectrum functor to its actual inclusion colimit gives
an inverse limit. Transport along the original affine scheme's `isoSpec` retains that scheme
as the literal cone point and retains the actual inclusion maps on coordinates.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite
open Algebra.FiniteTypeSubalgebraLimit

universe u

namespace AlgebraicGeometry.Scheme.FinitePresentationEnvelope

attribute [local instance] ULift.algebra'

/-- The spectra of the finitely generated arithmetic subalgebras of the original ring. -/
abbrev affineArithmeticDiagram (A : CommRingCat.{u}) : (Finset A)ᵒᵖ ⥤ Scheme.{u} :=
  (ringDiagram (ULift.{u} ℤ) A).op ⋙ Scheme.Spec

/-- The actual spectrum cone, using the original inclusion ring homomorphisms. -/
def affineArithmeticCone (A : CommRingCat.{u}) : Cone (affineArithmeticDiagram A) :=
  Scheme.Spec.mapCone (ringCocone (ULift.{u} ℤ) A).op

/-- The actual arithmetic spectrum cone is limiting. -/
def affineArithmeticIsLimit (A : CommRingCat.{u}) : IsLimit (affineArithmeticCone A) :=
  isLimitOfPreserves Scheme.Spec (ringCoconeIsColimit (ULift.{u} ℤ) A).op

/-- Every arithmetic subalgebra stage is locally of finite type over the integer base. -/
theorem affineArithmeticStage_finiteType (A : CommRingCat.{u}) (s : Finset A) :
    LocallyOfFiniteType
      (specULiftZIsTerminal.from ((affineArithmeticDiagram A).obj (op s))) := by
  let B := stage (ULift.{u} ℤ) A s
  let a : CommRingCat.of (ULift.{u} ℤ) ⟶ CommRingCat.of B :=
    CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) B)
  have ha : LocallyOfFiniteType (Spec.map a) := by
    apply HasRingHomProperty.Spec_iff.mpr
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  have he : specULiftZIsTerminal.from (Spec (CommRingCat.of B)) = Spec.map a :=
    specULiftZIsTerminal.hom_ext _ _
  change LocallyOfFiniteType (specULiftZIsTerminal.from (Spec (CommRingCat.of B)))
  rw [he]
  exact ha

/-- Transport the universal property before specializing either cone or isomorphism. -/
def isLimit_extendByIso {C J : Type*} [Category C] [Category J]
    {D : J ⥤ C} (c : Cone D) (hc : IsLimit c) {Z : C} (e : Z ≅ c.pt) :
    IsLimit (c.extend e.hom) :=
  hc.ofIsoLimit (c.extendIso e.symm)

/-- The actual arithmetic cone at the original affine scheme. -/
def affineSystemCone (X : Scheme.{u}) [IsAffine X] :
    Cone (affineArithmeticDiagram Γ(X, ⊤)) :=
  (affineArithmeticCone Γ(X, ⊤)).extend X.isoSpec.hom

/-- The original affine scheme is the limit of the arithmetic subalgebra diagram. -/
def affineSystemConeIsLimit (X : Scheme.{u}) [IsAffine X] : IsLimit (affineSystemCone X) :=
  isLimit_extendByIso (affineArithmeticCone Γ(X, ⊤))
    (affineArithmeticIsLimit Γ(X, ⊤)) X.isoSpec

/-- Every affine scheme has an actual small arithmetic approximation system. -/
def affineSystem (X : Scheme.{u}) [IsAffine X] : System X where
  Index := (Finset Γ(X, ⊤))ᵒᵖ
  category := inferInstance
  cofiltered := inferInstance
  diagram := affineArithmeticDiagram Γ(X, ⊤)
  projection := (affineSystemCone X).π
  isLimit := affineSystemConeIsLimit X
  affine _ := by
    change IsAffineHom (Scheme.Spec.map _)
    infer_instance
  finiteType i := affineArithmeticStage_finiteType Γ(X, ⊤) i.unop
  compact _ := by
    change CompactSpace (Spec _)
    infer_instance

end AlgebraicGeometry.Scheme.FinitePresentationEnvelope
