/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.LocalCompletedHom
public import Aglib.AlgebraicGeometry.Modules.InternalHom.CompletedRestriction
public import Aglib.AlgebraicGeometry.Modules.InternalHom.CompletedExt
public import Aglib.AlgebraicGeometry.Modules.IdealPowers.AffineQuotientNaturality

/-! # Restriction compatibility of completed local Hom sections -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.InternalHom

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (F G : X.Modules)
  [F.IsQuasicoherent] [G.IsQuasicoherent]
  (hF : QuasiCoherent.affineLocallyFiniteType X F)
  (hG : QuasiCoherent.affineLocallyFiniteType X G) (I : Ideal A)

local notation "α" => idealThickeningBaseScalar f

/-- Local completed Hom representatives of an original formal morphism commute
with every affine-open restriction. -/
theorem localCompletedHom_restrict (hI : I.FG)
    (η : idealPowerQuotientFunctor X α F I ⟶ idealPowerQuotientFunctor X α G I)
    (U V : X.affineOpens) (i : V.val ⟶ U.val) :
    letI := idealSectionModule X α (sheaf X F G) U.val
    letI := idealSectionModule X α (sheaf X F G) V.val
    AdicCompletion.map I ((moduleSectionsPresheaf X α (sheaf X F G)).map i.op).hom
        (localCompletedHom f F G hF hG I η U) =
      localCompletedHom f F G hF hG I η V := by
  let := idealSectionModule X α (sheaf X F G) U.val
  let := idealSectionModule X α (sheaf X F G) V.val
  let := idealSectionModule X α F U.val
  let := idealSectionModule X α F V.val
  let := idealSectionModule X α G U.val
  let := idealSectionModule X α G V.val
  let hU := localCompletedHom f F G hF hG I η U
  let hV := localCompletedHom f F G hF hG I η V
  apply affineCompletedEvaluation_ext_restriction α I F G hF hG U V i
  intro m
  have he : affineCompletedEvaluation α I V F G hF hG
      (AdicCompletion.map I ((moduleSectionsPresheaf X α (sheaf X F G)).map i.op).hom hU)
        (AdicCompletion.of I Γ(F, V) (F.val.map i.op m)) =
      AdicCompletion.map I ((moduleSectionsPresheaf X α G).map i.op).hom
        (affineCompletedEvaluation α I U F G hF hG hU (AdicCompletion.of I _ m)) := by
    have hm : AdicCompletion.map I ((moduleSectionsPresheaf X α F).map i.op).hom
        (AdicCompletion.of I Γ(F, U) m) =
        AdicCompletion.of I Γ(F, V) (F.val.map i.op m) :=
      AdicCompletion.map_of I ((moduleSectionsPresheaf X α F).map i.op).hom m
    exact (congrArg (affineCompletedEvaluation α I V F G hF hG
      (AdicCompletion.map I ((moduleSectionsPresheaf X α (sheaf X F G)).map i.op).hom hU))
        hm.symm).trans
      (affineCompletedEvaluation_restrict α I F G hF hG hI U V i hU
        (AdicCompletion.of I Γ(F, U) m))
  apply he.trans
  apply AdicCompletion.ext
  intro n
  apply (idealQuotientAffineSectionsEquiv f G (I ^ n) V).injective
  calc
    _ = (idealQuotient X α G (I ^ n)).val.map i.op
        (idealQuotientAffineSectionsEquiv f G (I ^ n) U
          (AdicCompletion.eval I Γ(G, U) n
            (affineCompletedEvaluation α I U F G hF hG hU (AdicCompletion.of I _ m)))) :=
      idealQuotientAffineSectionsEquiv_restrict f G (I ^ n) U V i _
    _ = (idealQuotient X α G (I ^ n)).val.map i.op
        ((η.app (op n)).app U.val ((idealQuotientπ X α F (I ^ n)).app U.val m)) :=
      congrArg ((idealQuotient X α G (I ^ n)).val.map i.op)
        (localCompletedHom_coordinate f F G hF hG I η U n m)
    _ = (η.app (op n)).app V.val
        ((idealQuotient X α F (I ^ n)).val.map i.op
          ((idealQuotientπ X α F (I ^ n)).app U.val m)) :=
      (PresheafOfModules.naturality_apply (η.app (op n)).val i.op _).symm
    _ = (η.app (op n)).app V.val
        ((idealQuotientπ X α F (I ^ n)).app V.val (F.val.map i.op m)) :=
      congrArg ((η.app (op n)).app V.val)
        (PresheafOfModules.naturality_apply (idealQuotientπ X α F (I ^ n)).val i.op m).symm
    _ = _ := (localCompletedHom_coordinate f F G hF hG I η V n (F.val.map i.op m)).symm

end AlgebraicGeometry.Scheme.Cohomology
