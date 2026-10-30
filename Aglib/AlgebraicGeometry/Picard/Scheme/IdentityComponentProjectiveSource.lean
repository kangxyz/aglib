/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Scheme.IdentityComponentQuasiProjective
public import Aglib.AlgebraicGeometry.ProjectiveSpace.QuasiProjective.EquivFin

/-!
# Quasi-projectivity of Pic0 for an H-projective source

An H-projective flat geometrically integral source supplies the finite-coordinate
closed embedding required by the general Picard-level theorem. Coordinates and
embedding are chosen only in the proof. The original structure map and supplied
locally Noetherian fppf Picard representative are retained.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.OverField

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

variable {k : Type u} [Field k] (X : FScheme k)
  [IsHProjective X.hom] [Flat X.hom] [GeometricallyIntegral X.hom]
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- The actual Picard identity component of an H-projective flat geometrically
integral source is H-quasi-projective over its original field. -/
theorem isHQuasiProjective_picardIdentityComponent_of_isHProjective :
    IsHQuasiProjective (picardIdentityComponent X.hom P R).hom := by
  obtain ⟨ι, N, e, i, hi, _, hp⟩ :=
    IsHQuasiProjective.exists_isImmersion_equivFin X.hom
  let : Finite ι := Finite.of_equiv (Fin (N + 1)) e.symm
  have : IsProper (i ≫ toSpec k ι) := by rw [hp]; infer_instance
  have : IsProper i := IsProper.of_comp i (toSpec k ι)
  have : IsClosedImmersion i :=
    (IsClosedImmersion.iff_isProper_and_mono i).mpr ⟨inferInstance, inferInstance⟩
  obtain ⟨Xl, ⟨⟨⟩⟩, p⟩ := X
  change Xl ⟶ ProjectiveSpace k ι at i
  change i ≫ toSpec k ι = p at hp
  subst hp
  exact isHQuasiProjective_picardIdentityComponent_hom i e P R

end AlgebraicGeometry.Scheme.RelativePicard
