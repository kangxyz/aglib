/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Rees.Image
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pullback
public import Mathlib.RingTheory.ReesAlgebra
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# The geometric Rees image coefficient

Base change to the native Rees algebra, then base change its polynomial
inclusion. The second fibre product is the iterated presentation of
`X × Spec A[t]`. Its projection to the Rees base change is affine.
The coefficient is the actual image of the pullback unit, with no flatness
assumption on the original coefficient.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules.Rees

variable {A : Type u} [CommRing A] (I : Ideal A)
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))

/-- The actual base change to the native Rees algebra. -/
abbrev space : Scheme.{u} :=
  Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap A (reesAlgebra I))))

/-- The original projection back to the scheme carrying the coefficient. -/
abbrev projection : space I f ⟶ X := pullback.fst _ _

instance projection_isAffineHom : IsAffineHom (projection I f) := by
  let : IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap A (reesAlgebra I)))) :=
    isAffineHom_of_isAffine _
  exact MorphismProperty.pullback_fst _ _ ‹_›

/-- The structural projection after Rees base change. -/
abbrev structureMap : space I f ⟶ Spec (CommRingCat.of (reesAlgebra I)) :=
  pullback.snd _ _

/-- The polynomial extension of the Rees base change, as an iterated fibre product. -/
abbrev polynomialSpace : Scheme.{u} :=
  Limits.pullback (structureMap I f)
    (Spec.map (CommRingCat.ofHom (reesAlgebra I).val.toRingHom))

/-- The affine comparison induced by the actual Rees inclusion into polynomials. -/
abbrev polynomialProjection : polynomialSpace I f ⟶ space I f := pullback.fst _ _

instance polynomialProjection_isAffineHom : IsAffineHom (polynomialProjection I f) := by
  let : IsAffineHom (Spec.map (CommRingCat.ofHom (reesAlgebra I).val.toRingHom)) :=
    isAffineHom_of_isAffine _
  exact MorphismProperty.pullback_fst _ _ ‹_›

/-- Pullback of the original coefficient to the Rees base change. -/
def pulledCoefficient (F : X.Modules) : (space I f).Modules :=
  (pullback (projection I f)).obj F

instance pulledCoefficient_isQuasicoherent (F : X.Modules) [F.IsQuasicoherent] :
    (pulledCoefficient I f F).IsQuasicoherent := by
  dsimp [pulledCoefficient]
  infer_instance

/-- The Rees coefficient is the actual unit image, not its tensor source. -/
def coefficient (F : X.Modules) : (space I f).Modules :=
  affineUnitImage (polynomialProjection I f) (pulledCoefficient I f F)

/-- The original quotient morphism onto the geometric Rees coefficient. -/
def toCoefficient (F : X.Modules) : pulledCoefficient I f F ⟶ coefficient I f F :=
  toAffineUnitImage (polynomialProjection I f) (pulledCoefficient I f F)

/-- The geometric Rees image is coherent under the proper Noetherian hypotheses. -/
theorem affineLocallyFiniteType_coefficient [IsNoetherianRing A] [IsProper f]
    (F : X.Modules) (hF : QuasiCoherent.affineLocallyFiniteType X F) :
    QuasiCoherent.affineLocallyFiniteType (space I f) (coefficient I f F) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsLocallyNoetherian (space I f) :=
    LocallyOfFiniteType.isLocallyNoetherian (structureMap I f)
  exact affineLocallyFiniteType_affineUnitImage _ _
    (QuasiCoherent.affineLocallyFiniteType_pullback (projection I f) hF)

end AlgebraicGeometry.Scheme.Modules.Rees
