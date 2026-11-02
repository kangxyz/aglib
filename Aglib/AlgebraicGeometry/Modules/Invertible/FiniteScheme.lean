/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Affine
public import Aglib.AlgebraicGeometry.Modules.Invertible.Power.Pullback
public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.DegreeLength
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Basic
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.ResolutionSections

/-!
# Lines on finite field schemes and their original section dimensions

Semilocal Picard triviality supplies an existence statement, not a chosen
canonical orientation. The numerical equality retains the actual structural
scalars and actual pushforward, including nilpotent finite schemes over any field.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.OverField

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

/-- A semilocal affine line is trivial. The existence is used only within
numerical section comparisons, not as a canonical choice of orientation. -/
theorem semilocalLine_nonempty_iso_unit
    (B : CommRingCat.{u}) [Finite (MaximalSpectrum B)]
    (L : Invertible.LineBundle (Spec B)) :
    Nonempty (L.val ≅ SheafOfModules.unit (Spec B).ringCatSheaf) := by
  let : Subsingleton (Invertible.PicardGroup (Spec B)) :=
    (Invertible.picardGroupEquivCommRingPic B).injective.subsingleton
  obtain ⟨e⟩ := (Invertible.class_eq_iff (Spec B) L
    (Invertible.trivialLineBundle (Spec B))).mp
      (Subsingleton.elim (Invertible.classOf (Spec B) L)
        (Invertible.classOf (Spec B) (Invertible.trivialLineBundle (Spec B))))
  exact ⟨e ≪≫ Invertible.PowerPullback.freeUnitIso (Spec B)⟩

/-- Equality of section dimensions of a line and the structure module on a
semilocal affine scheme, for the original scalar action. -/
theorem semilocalLine_sections_finrank
    (k : Type u) [Field k] (B : CommRingCat.{u}) [Finite (MaximalSpectrum B)]
    (α : k →+* Γ(Spec B, ⊤)) (L : Invertible.LineBundle (Spec B)) :
    Module.finrank k ((moduleGlobalSectionsFunctorOfHom (Spec B) α).obj L.val) =
      Module.finrank k ((moduleGlobalSectionsFunctorOfHom (Spec B) α).obj
        (SheafOfModules.unit (Spec B).ringCatSheaf)) := by
  obtain ⟨e⟩ := semilocalLine_nonempty_iso_unit B L
  exact (((moduleGlobalSectionsFunctorOfHom (Spec B) α).mapIso e).toLinearEquiv).finrank_eq

/-- A line on an affine semilocal scheme is trivial, transported through the
original affine-spectrum isomorphism. -/
theorem affineSemilocalLine_nonempty_iso_unit
    (D : Scheme.{u}) [IsAffine D] [Finite (MaximalSpectrum Γ(D, ⊤))]
    (L : Invertible.LineBundle D) :
    Nonempty (L.val ≅ SheafOfModules.unit D.ringCatSheaf) := by
  have hinj : Function.Injective (Invertible.pullbackClass D.isoSpec.inv) := by
    intro a b h
    have h' := congrArg (Invertible.pullbackClass D.isoSpec.hom) h
    simpa only [← Invertible.pullbackClass_comp, Iso.hom_inv_id,
      Invertible.pullbackClass_id] using h'
  let : Subsingleton (Invertible.PicardGroup (Spec Γ(D, ⊤))) :=
    (Invertible.picardGroupEquivCommRingPic Γ(D, ⊤)).injective.subsingleton
  let : Subsingleton (Invertible.PicardGroup D) := hinj.subsingleton
  obtain ⟨e⟩ := (Invertible.class_eq_iff D L (Invertible.trivialLineBundle D)).mp
    (Subsingleton.elim (Invertible.classOf D L)
      (Invertible.classOf D (Invertible.trivialLineBundle D)))
  exact ⟨e ≪≫ Invertible.PowerPullback.freeUnitIso D⟩

/-- A line on a finite field scheme is trivial, including its nonreduced structure. -/
theorem finiteSchemeLine_nonempty_iso_unit
    {k : Type u} [Field k] (D : Scheme.{u})
    (q : D ⟶ Spec (.of k)) [IsFinite q] (L : Invertible.LineBundle D) :
    Nonempty (L.val ≅ SheafOfModules.unit D.ringCatSheaf) := by
  let : IsAffine D := isAffine_of_isAffineHom q
  let : Algebra k Γ(D, ⊤) := Scheme.Hom.coordinateAlgebra k (Over.mk q)
  let : Module.Finite k Γ(D, ⊤) :=
    Scheme.Hom.FiniteFlat.finite_coordinate_algebra k D q
  let : IsArtinianRing Γ(D, ⊤) := IsArtinianRing.of_finite k Γ(D, ⊤)
  exact affineSemilocalLine_nonempty_iso_unit D L

-- Any actual pushforward retains this (noncanonical) iso, which is enough for
-- equality of original H0 dimensions of i_*L and i_*O_D. No finite pushforward
-- cohomology comparison is needed for that particular numerical equality.
/-- Pushing forward a line from an actual finite field scheme preserves its
section dimension relative to the structure module. The choice of a
trivialization is used only for this numerical statement. -/
theorem finiteSchemeLine_pushforward_h0_finrank
    {k : Type u} [Field k] (X : FScheme k) {D : Scheme.{u}}
    (i : D ⟶ X.left) [IsFinite (i ≫ X.hom)] (L : Invertible.LineBundle D) :
    Module.finrank k (moduleCohomology k X ((pushforward i).obj L.val) 0) =
      Module.finrank k (moduleCohomology k X ((pushforward i).obj
        (SheafOfModules.unit D.ringCatSheaf)) 0) := by
  obtain ⟨e⟩ := finiteSchemeLine_nonempty_iso_unit D (i ≫ X.hom) L
  exact (moduleCohomologyIso X ((pushforward i).mapIso e) 0).finrank_eq

end AlgebraicGeometry.Scheme.Cohomology
