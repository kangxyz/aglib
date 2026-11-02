/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.LocalBaseIdeal
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Original residue scalars over the closed point of a local base

The original base germ is an isomorphism at the closed point of a local base.
Its native residue-field equivalence identifies the original scheme residue
map with the residue map of the original structural stalk scalars. Finiteness
is equivalent across that same square; it is not assumed.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {A : Type u} [CommRing A] [IsLocalRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) (x : X) (hx : f x = IsLocalRing.closedPoint A)

/-- The original base germ, as a ring equivalence over the closed point. -/
def closedBaseStalkEquiv : A ≃+* (Spec (.of A)).presheaf.stalk (f x) := by
  have hb (y : Spec (.of A)) (hy : y = IsLocalRing.closedPoint A) :
      IsIso ((Scheme.ΓSpecIso (.of A)).inv ≫
        (Spec (.of A)).presheaf.germ ⊤ y trivial) := by
    subst y
    rw [← ΓSpecIso_hom_stalkClosedPointIso_inv]
    infer_instance
  let := hb (f x) hx
  exact (asIso ((Scheme.ΓSpecIso (.of A)).inv ≫
    (Spec (.of A)).presheaf.germ ⊤ (f x) trivial)).commRingCatIsoToRingEquiv

/-- This equivalence retains the original Spec constants and original germ. -/
theorem closedBaseStalkEquiv_toRingHom :
    (closedBaseStalkEquiv f x hx).toRingHom =
      ((Spec (.of A)).presheaf.germ ⊤ (f x) trivial).hom.comp
        (Scheme.ΓSpecIso (.of A)).inv.hom := rfl

/-- Its composite with the actual morphism stalk map is the original scalar map. -/
theorem closedBaseStalkEquiv_stalkMap :
    (f.stalkMap x).hom.comp (closedBaseStalkEquiv f x hx).toRingHom =
      f.stalkScalar x := by
  rw [closedBaseStalkEquiv_toRingHom]
  exact (f.stalkScalar_eq_local x).symm

/-- The native residue equivalence induced by the same original base germ. -/
def closedBaseResidueEquiv :
    IsLocalRing.ResidueField A ≃+* (Spec (.of A)).residueField (f x) :=
  IsLocalRing.ResidueField.mapEquiv (closedBaseStalkEquiv f x hx)

/-- The whole residue square retains the original scheme and scalar maps. -/
theorem closedBaseResidueEquiv_stalkScalar :
    let := f.stalkScalar_isLocalHom_of_closedPoint x hx
    (f.residueFieldMap x).hom.comp (closedBaseResidueEquiv f x hx).toRingHom =
      IsLocalRing.ResidueField.map (f.stalkScalar x) := by
  let := f.stalkScalar_isLocalHom_of_closedPoint x hx
  apply RingHom.ext
  intro z
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective z
  change IsLocalRing.residue (X.presheaf.stalk x)
      ((f.stalkMap x).hom (closedBaseStalkEquiv f x hx r)) =
    IsLocalRing.residue (X.presheaf.stalk x) (f.stalkScalar x r)
  exact congrArg (IsLocalRing.residue (X.presheaf.stalk x))
    (RingHom.congr_fun (closedBaseStalkEquiv_stalkMap f x hx) r)

/-- Finiteness is transported across precisely the same original residue square. -/
theorem stalkScalar_residueMap_finite_iff :
    let := f.stalkScalar_isLocalHom_of_closedPoint x hx
    (IsLocalRing.ResidueField.map (f.stalkScalar x)).Finite ↔
      (f.residueFieldMap x).hom.Finite := by
  let := f.stalkScalar_isLocalHom_of_closedPoint x hx
  change (IsLocalRing.ResidueField.map (f.stalkScalar x)).Finite ↔
    (f.residueFieldMap x).hom.Finite
  rw [← closedBaseResidueEquiv_stalkScalar f x hx]
  exact ⟨RingHom.Finite.of_comp_finite,
    fun h ↦ h.comp (closedBaseResidueEquiv f x hx).finite⟩

end AlgebraicGeometry.Scheme.Hom
