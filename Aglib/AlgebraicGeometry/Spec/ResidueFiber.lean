/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# The literal residue fibre of a scheme over a local ring

The objects and maps are the original residue-spectrum map and categorical
pullback. The same section specializes by the pullback universal property.
Properness and flatness are inherited by base change.

Extraction: frozen R5 `LocalModels/ActualModel.lean:132–162` and the canonical
map in `ResidueField/LocalRingMap.lean:25–31`, revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`. The definitions consume only a
commutative local ring, the actual structural map, and the given section.
-/

@[expose] public section
noncomputable section

open CategoryTheory Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.LocalRing

/-- The actual closed-point map induced by the local ring's residue quotient. -/
abbrev residueSpecMap (R : Type u) [CommRing R] [IsLocalRing R] :
    Spec (.of (IsLocalRing.ResidueField R)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))

/-- The canonical residue-spectrum map of a local ring is a closed immersion. -/
instance residueSpecMap_isClosedImmersion (R : Type u) [CommRing R] [IsLocalRing R] :
    IsClosedImmersion (residueSpecMap R) :=
  IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective

namespace ResidueFiber
variable {R : Type u} [CommRing R] [IsLocalRing R] {Y : Scheme.{u}}
variable (π : Y ⟶ Spec (.of R))

/-- The actual residue-field pullback. -/
abbrev obj : Scheme.{u} := pullback π (residueSpecMap R)

/-- The structural arrow to the spectrum of the original residue field. -/
abbrev structureMap : obj π ⟶ Spec (.of (IsLocalRing.ResidueField R)) :=
  pullback.snd π (residueSpecMap R)

/-- The actual residue-fibre inclusion in the original scheme. -/
abbrev projection : obj π ⟶ Y := pullback.fst π (residueSpecMap R)

/-- The projection from the actual residue fibre is a closed immersion. -/
instance projection_isClosedImmersion : IsClosedImmersion (projection π) := by
  infer_instance

/-- Base change of the same given section. -/
def «section» (σ : Spec (.of R) ⟶ Y) (hσ : σ ≫ π = 𝟙 _) :
    Spec (.of (IsLocalRing.ResidueField R)) ⟶ obj π :=
  pullback.lift (residueSpecMap R ≫ σ) (𝟙 _)
    (by simp only [Category.assoc, hσ, Category.comp_id, Category.id_comp])

@[simp, reassoc] theorem section_structureMap (σ : Spec (.of R) ⟶ Y)
    (hσ : σ ≫ π = 𝟙 _) : «section» π σ hσ ≫ structureMap π = 𝟙 _ :=
  pullback.lift_snd _ _ _

@[simp, reassoc] theorem section_projection (σ : Spec (.of R) ⟶ Y)
    (hσ : σ ≫ π = 𝟙 _) : «section» π σ hσ ≫ projection π = residueSpecMap R ≫ σ :=
  pullback.lift_fst _ _ _

/-- The actual residue fibre is proper over the residue field when the original structure map is
proper. -/
instance structureMap_isProper [IsProper π] : IsProper (structureMap π) := by
  infer_instance

/-- The actual residue-fibre structure map is flat when the original structure map is flat. -/
instance structureMap_flat [Flat π] : Flat (structureMap π) := by
  infer_instance

end ResidueFiber
end AlgebraicGeometry.Scheme.LocalRing
