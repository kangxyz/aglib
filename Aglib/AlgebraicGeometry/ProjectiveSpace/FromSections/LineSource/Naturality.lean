/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.FromSections.LineSource
public import Aglib.AlgebraicGeometry.ProjectiveSpace.FromSections.Naturality
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-!
# Trivialized line-source projective coordinates

A specified trivialization of the original line source identifies the
line-source projective morphism with the ordinary section-family morphism.
The actual dual-evaluation and tensor-unit maps supply the coefficient
isomorphism, and every coordinate retains the given source trivialization.
This avoids imposing any compatibility of duals with scheme pullback.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.ProjectiveSpace.FromSections.LineSource

variable {X : Scheme.{u}} (D : X.Modules) (hD : IsLocallyRankOne X D)
variable (eD : D ≅ SheafOfModules.unit X.ringCatSheaf)

/-- The dual trivialization induced by the specified original source frame. -/
def trivializedDualIso : dualSheaf X D ≅ SheafOfModules.unit X.ringCatSheaf :=
  (MonoidalCategory.rightUnitor (C := X.Modules) (dualSheaf X D)).symm ≪≫
    (tensorLeft (C := X.Modules) (dualSheaf X D)).mapIso eD.symm ≪≫ dualEvaluationIso X ⟨D, hD⟩

/-- Tensoring by the actual dual is identified with the identity using only
the specified frame and the actual evaluation and unit isomorphisms. -/
def trivializedCoefficientNatIso : tensorLeft (C := X.Modules) (dualSheaf X D) ≅ 𝟭 X.Modules :=
  (tensoringLeft X.Modules).mapIso (trivializedDualIso D hD eD) ≪≫
    leftUnitorNatIso X.Modules

/-- At the unit, the comparison retains the original inverse frame and
original dual evaluation, not an unspecified scalar multiple. -/
theorem trivializedCoefficientNatIso_unit :
    (trivializedCoefficientNatIso D hD eD).hom.app
        (SheafOfModules.unit X.ringCatSheaf) =
      (tensorLeft (C := X.Modules) (dualSheaf X D)).map eD.inv ≫
        (dualEvaluationIso X ⟨D, hD⟩).hom := by
  change MonoidalCategory.whiskerRight (C := X.Modules)
      (trivializedDualIso D hD eD).hom (𝟙_ X.Modules) ≫
    (MonoidalCategory.leftUnitor (C := X.Modules) (𝟙_ X.Modules)).hom = _
  rw [unitors_equal, rightUnitor_naturality]
  simp only [trivializedDualIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.hom_inv_id_assoc]

/-- At the original source, the comparison is exactly evaluation followed by
the inverse original frame. -/
theorem trivializedCoefficientNatIso_source :
    (trivializedCoefficientNatIso D hD eD).hom.app D =
      (dualEvaluationIso X ⟨D, hD⟩).hom ≫ eD.inv := by
  apply (cancel_epi ((tensorLeft (C := X.Modules) (dualSheaf X D)).map eD.inv)).mp
  rw [(trivializedCoefficientNatIso D hD eD).hom.naturality eD.inv,
    trivializedCoefficientNatIso_unit]
  rfl

/-- The actual coefficient module comparison for a specified source frame. -/
def trivializedCoefficientIso (J : X.Modules) : coefficientModule D J ≅ J :=
  (trivializedCoefficientNatIso D hD eD).app J

/-- Every original coordinate becomes exactly its section in the specified
source frame. -/
@[reassoc]
theorem sectionOfHom_trivialized (J : X.Modules) (d : D ⟶ J) :
    sectionOfHom D J hD d ≫ (trivializedCoefficientIso D hD eD J).hom =
      eD.inv ≫ d := by
  change (dualEvaluationIso X ⟨D, hD⟩).inv ≫
    (tensorLeft (C := X.Modules) (dualSheaf X D)).map d ≫
      (trivializedCoefficientNatIso D hD eD).hom.app J = _
  rw [(trivializedCoefficientNatIso D hD eD).hom.naturality d,
    trivializedCoefficientNatIso_source]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Functor.id_map]

variable (J : X.Modules) {I : Type u} (d : I → (D ⟶ J))

/-- Changing the original source to its displayed frame preserves generation. -/
instance trivializedFamily_epi [Epi (Sigma.desc d)] :
    Epi (Sigma.desc (fun i ↦ eD.inv ≫ d i)) := by
  have h : Sigma.desc (fun i ↦ eD.inv ≫ d i) =
      CategoryTheory.Limits.Sigma.map (fun _ : I ↦ eD.inv) ≫ Sigma.desc d := by
    apply Sigma.hom_ext
    intro i
    simp only [Sigma.ι_comp_desc, Sigma.ι_map_assoc]
  rw [h]
  infer_instance

/-- Actual equality of projective scheme morphisms for the original family
in a specified source frame. No field or reducedness hypothesis is used. -/
theorem mapOfFamily_eq_of_sourceIso {R : Type u} [CommRing R] [Finite I]
    [Epi (Sigma.desc d)] (p : X ⟶ Spec (.of R)) (hJ : IsLocallyRankOne X J) :
    letI : Epi (Sigma.desc (fun i ↦ eD.inv ≫ d i)) :=
      trivializedFamily_epi D eD J d
    mapOfFamily D J hD p hJ d =
      mapOfFiniteFamily p J hJ (fun i ↦ eD.inv ≫ d i) := by
  let : Epi (Sigma.desc (fun i ↦ eD.inv ≫ d i)) :=
    trivializedFamily_epi D eD J d
  unfold mapOfFamily
  exact mapOfFiniteFamily_iso p (coefficientModule D J) J
    (coefficientModule_locallyRankOne D J hD hJ) hJ
    (fun i ↦ sectionOfHom D J hD (d i)) (fun i ↦ eD.inv ≫ d i)
    (trivializedCoefficientIso D hD eD J)
    (fun i ↦ sectionOfHom_trivialized D hD eD J (d i))

end AlgebraicGeometry.ProjectiveSpace.FromSections.LineSource
