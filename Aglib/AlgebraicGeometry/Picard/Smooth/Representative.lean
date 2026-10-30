/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Smooth.Curve

/-!
# Smoothness of the original representing Picard scheme

The curve smoothness theorem transfers along the unique isomorphism of
representatives on the stated locally Noetherian test category. The conclusion
concerns the supplied representative and its original structural morphism.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

/-- Every representative of the Picard sheaf of a projective integral curve is
smooth, on the same locally Noetherian test category as the construction. -/
theorem smooth_representative_of_curve
    {k : Type u} [Field k] {ι : Type u} {X : Scheme.{u}}
    (i : X ⟶ ProjectiveSpace k ι) [IsClosedImmersion i]
    [Flat (i ≫ toSpec k ι)] [GeometricallyIntegral (i ≫ toSpec k ι)]
    {N : ℕ} (e : ι ≃ Fin (N + 1)) [IsIntegral X]
    (hdim : topologicalKrullDim X = 1)
    (P : LocallyNoetherianOver (Spec (.of k)))
    (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
      (fppfPicardSheaf (i ≫ toSpec k ι)).obj ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P) :
    Smooth P.obj.hom := by
  let h := Strata.fineStrataRepresentableByHQuasiProjective i e
  let : Smooth (picardScheme h).obj.hom := (smooth_picardScheme_of_curve h hdim).1
  let α : P.obj ≅ (picardScheme h).obj :=
    (locallyNoetherianOverInclusion (Spec (.of k))).mapIso
    (R.uniqueUpToIso (picardSchemeRepresentableBy h))
  let : IsIso α.hom.left := (Over.forget (Spec (.of k))).map_isIso α.hom
  rw [← α.hom.w]
  infer_instance

end AlgebraicGeometry.Scheme.RelativePicard
