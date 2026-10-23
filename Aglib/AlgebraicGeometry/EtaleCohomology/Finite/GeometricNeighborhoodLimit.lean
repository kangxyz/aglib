/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.StrictHenselization.SeparablyClosedResidue
public import Mathlib.AlgebraicGeometry.Limits

/-!
# The actual spectrum limit of geometric etale neighborhoods

Taking spectra of the native filtered ring colimit gives an actual limiting
cone. The chosen field-valued point restricts to the specified point at every
stage, with literal spectrum maps. This does not yet identify the index with
the full small-etale geometric neighborhood category or prove cofinality there.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood

universe u

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω]

/-- The actual cofiltered scheme diagram obtained by taking spectra. -/
def diagram : (GeometricEtaleNeighborhood R Ω)ᵒᵖ ⥤ Scheme.{u} :=
  (GeometricEtaleNeighborhood.ringDiagram R Ω).op ⋙ Scheme.Spec

/-- The cone whose point is the spectrum of the constructed neighborhood ring. -/
def specCone : Cone (diagram R Ω) :=
  Scheme.Spec.mapCone (GeometricEtaleColimit.ringCocone R Ω).op

/-- The spectrum cone is limiting by the native `Spec` adjunction. -/
def specConeIsLimit : IsLimit (specCone R Ω) :=
  isLimitOfPreserves Scheme.Spec (GeometricEtaleColimit.ringCoconeIsColimit R Ω).op

/-- Each cone projection is literally the spectrum of its stage ring map. -/
@[simp]
lemma specCone_π (X : GeometricEtaleNeighborhood R Ω) :
    (specCone R Ω).π.app (op X) =
      Spec.map (CommRingCat.ofHom (GeometricEtaleColimit.stageRingHom R Ω X)) := rfl

/-- The actual chosen geometric field point of the limit scheme. -/
def point : Spec (.of Ω) ⟶ (specCone R Ω).pt :=
  Spec.map (CommRingCat.ofHom (GeometricEtaleColimit.residue R Ω).toRingHom)

/-- Restricting the chosen point to a stage gives its original specified point. -/
@[reassoc]
lemma point_π (X : GeometricEtaleNeighborhood R Ω) :
    point R Ω ≫ (specCone R Ω).π.app (op X) =
      Spec.map (CommRingCat.ofHom X.point.toRingHom) := by
  rw [specCone_π]
  change Spec.map (CommRingCat.ofHom (GeometricEtaleColimit.residue R Ω).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (GeometricEtaleColimit.stageRingHom R Ω X)) = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (GeometricEtaleColimit.residueRingHom_comp_stageRingHom R Ω X)

/-- The point-to-stage equation in the canonical spectrum-map normal form. -/
@[simp, reassoc]
lemma point_specMap_stageRingHom (X : GeometricEtaleNeighborhood R Ω) :
    point R Ω ≫ Spec.map (CommRingCat.ofHom (GeometricEtaleColimit.stageRingHom R Ω X)) =
      Spec.map (CommRingCat.ofHom X.point.toRingHom) := by
  have h := point_π R Ω X
  change (point R Ω ≫
      Spec.map (CommRingCat.ofHom (GeometricEtaleColimit.stageRingHom R Ω X)) :
        Spec (.of Ω) ⟶ Spec (.of X.algebra)) =
    Spec.map (CommRingCat.ofHom X.point.toRingHom) at h
  exact h

/-- The cone projections retain the original structural maps over the base. -/
@[reassoc]
lemma π_structure (X : GeometricEtaleNeighborhood R Ω) :
    (specCone R Ω).π.app (op X) ≫ Spec.algebraMap R X.algebra =
      Spec.algebraMap R (GeometricEtaleColimit R Ω) := by
  rw [specCone_π]
  change Spec.map (CommRingCat.ofHom (GeometricEtaleColimit.stageRingHom R Ω X)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R X.algebra)) = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (GeometricEtaleColimit.stageRingHom_comp_algebraMap R Ω X)

/-- The stage spectrum map has the original structural map over the base. -/
@[simp]
lemma specMap_stageRingHom_structure (X : GeometricEtaleNeighborhood R Ω) :
    Spec.map (CommRingCat.ofHom (GeometricEtaleColimit.stageRingHom R Ω X)) ≫
        Spec.algebraMap R X.algebra =
      Spec.algebraMap R (GeometricEtaleColimit R Ω) := by
  have h := π_structure R Ω X
  change (Spec.map (CommRingCat.ofHom (GeometricEtaleColimit.stageRingHom R Ω X)) ≫
      Spec.algebraMap R X.algebra :
        Spec (.of (GeometricEtaleColimit R Ω)) ⟶ Spec (.of R)) =
    Spec.algebraMap R (GeometricEtaleColimit R Ω) at h
  exact h

/-- The chosen field point lies over the specified field-valued point of the base. -/
@[simp, reassoc]
lemma point_structure :
    point R Ω ≫ Spec.algebraMap R (GeometricEtaleColimit R Ω) =
      Spec.algebraMap R Ω := by
  change Spec.map (CommRingCat.ofHom (GeometricEtaleColimit.residue R Ω).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (GeometricEtaleColimit.of R Ω)) = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (GeometricEtaleColimit.residue_comp_of R Ω)


end AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood
