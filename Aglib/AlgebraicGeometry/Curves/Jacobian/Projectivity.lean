/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.DegreeZero
public import Aglib.AlgebraicGeometry.Picard.Scheme.QuasiProjectiveLevel

/-!
# Projectivity of the Jacobian over an algebraically closed field

For the supplied locally Noetherian representative `P,R` of the fppf Picard functor of a smooth
proper geometrically connected curve, the actual identity component `identityComponentOver P.obj`
is H-projective over the algebraically closed ground field. Existing properness gives a compact
source and the degree-zero stratum equality places its inclusion in one Picard stratum. The
general compact-factorization theorem places that same map in one H-quasi-projective Picard
level. Proper plus H-quasi-projective then gives H-projective.

The statement retains algebraic closedness and representability on locally Noetherian tests.
It uses neither a second Jacobian nor dimension, cube or multiplication-degree results.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.RelativePicard AlgebraicGeometry.Scheme.RelativePicard.Strata
open AlgebraicGeometry.Scheme.Group

namespace AlgebraicGeometry.Scheme.OverField.Curve

section Embedded

variable {k : Type u} [Field k] [IsAlgClosed k] {ι : Type u} {Y : Scheme.{u}}
  (i : Y ⟶ ProjectiveSpace k ι) [IsClosedImmersion i] {N : ℕ} (e : ι ≃ Fin (N + 1))
  [Flat (i ≫ toSpec k ι)]
  (hX : Properties (Over.mk (i ≫ toSpec k ι) : FScheme k))
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  [IsSeparated P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf (i ≫ toSpec k ι)).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

include e hX in
/-- The identity component of the supplied Picard representative is H-quasi-projective:
its compact image is the degree-zero Euler-polynomial stratum and lies in one Picard level. -/
theorem isHQuasiProjective_identityComponentOver_of_isAlgClosed_of_closedImmersion :
    letI := picardCommGrpObj (i ≫ toSpec k ι) P R
    IsHQuasiProjective (identityComponentOver P.obj).hom := by
  let := picardCommGrpObj (i ≫ toSpec k ι) P R
  have : GeometricallyIntegral (i ≫ toSpec k ι) := hX.isGeometricallyIntegral
  have : IsProper (identityComponentOver P.obj).hom :=
    isProper_identityComponentOver_of_isAlgClosed hX P R
  have : CompactSpace (identityComponentOver P.obj).left :=
    QuasiCompact.compactSpace_of_compactSpace (identityComponentOver P.obj).hom
  apply isHQuasiProjective_comp_of_isCompact_range_of_range_subset_eulerCondition i e P R
    (identityComponent P.obj).ι (isCompact_range (identityComponent P.obj).ι.continuous)
    (degreeStratumPolynomial i hX 0)
  rw [Scheme.Opens.range_ι,
    ← identityComponent_eq_opens_eulerCondition_degreeStratumPolynomial_zero_of_isAlgClosed
      i e hX P R]

end Embedded

variable {k : Type u} [Field k] {X : FScheme k} (hX : Properties X)
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  [IsSeparated P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

include hX in
/-- The actual Jacobian of a smooth proper geometrically connected curve is H-quasi-projective
over an algebraically closed field, for the supplied Picard representative. -/
theorem isHQuasiProjective_identityComponentOver_of_isAlgClosed [IsAlgClosed k] :
    letI := picardCommGrpObj X.hom P R
    IsHQuasiProjective (identityComponentOver P.obj).hom := by
  obtain ⟨N, i, hi, hiX⟩ := hX.exists_closedImmersion_projectiveSpace
  have hflat := hX.flat
  obtain ⟨Xl, ⟨⟨⟩⟩, Xh⟩ := X
  change Xl ⟶ ProjectiveSpace k (ULift.{u} (Fin (N + 1))) at i
  change i ≫ ProjectiveSpace.toSpec k (ULift.{u} (Fin (N + 1))) = Xh at hiX
  subst hiX
  have : Flat (i ≫ ProjectiveSpace.toSpec k (ULift.{u} (Fin (N + 1)))) := hflat
  exact isHQuasiProjective_identityComponentOver_of_isAlgClosed_of_closedImmersion i Equiv.ulift
    hX P R

include hX in
/-- The actual Jacobian of a smooth proper geometrically connected curve is H-projective over
an algebraically closed field. Properness and quasi-projectivity concern the same chosen `P,R`
and the same identity component. -/
theorem isHProjective_identityComponentOver_of_isAlgClosed [IsAlgClosed k] :
    letI := picardCommGrpObj X.hom P R
    IsHProjective (identityComponentOver P.obj).hom := by
  let := picardCommGrpObj X.hom P R
  have := isProper_identityComponentOver_of_isAlgClosed hX P R
  have := isHQuasiProjective_identityComponentOver_of_isAlgClosed hX P R
  exact IsHProjective.of_isHQuasiProjective_of_isProper _

end AlgebraicGeometry.Scheme.OverField.Curve
