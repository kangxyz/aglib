/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.ProjectiveLine.Charts
public import Aglib.AlgebraicGeometry.Limits.FiniteProducts
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Reindex
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Point
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Cartesian
public import Aglib.AlgebraicGeometry.ProjectiveSpace.PulledCoordinates

/-!
# The original product source and its zero-factor multiplication map

The source is the existing finite native product in `Over (Spec R)` of
the existing universe-polymorphic projective lines. The empty product is
the original base. The target uses the lifted `n+1` coordinate index.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct

universe u

variable (R : Type u) [CommRing R]

/-- Each factor is the original native projective line over its original base. -/
abbrev factor (n : ℕ) (_i : Fin n) : Over (Spec (CommRingCat.of R)) :=
  Over.mk (Scheme.ProjectiveLine.structureMap R)

/-- The existing finite native over-product, without replacing any factor. -/
abbrev product (n : ℕ) : Over (Spec (CommRingCat.of R)) :=
  Scheme.finiteProductOver (factor R n)

/-- The original scheme underlying the existing native product. -/
abbrev source (n : ℕ) : Scheme.{u} := (product R n).left

/-- The unchanged structural morphism of the native over-product. -/
abbrev structureMap (n : ℕ) : source R n ⟶ Spec (CommRingCat.of R) := (product R n).hom

/-- The original projection to an original native projective-line factor. -/
abbrev projection (n : ℕ) (i : Fin n) : source R n ⟶ Scheme.ProjectiveLine.projectiveP1 R :=
  (Scheme.finiteProductOverπ (factor R n) i).left

@[reassoc (attr := simp)]
theorem projection_over (n : ℕ) (i : Fin n) :
    projection R n i ≫ Scheme.ProjectiveLine.structureMap R = structureMap R n :=
  Scheme.finiteProductOverπ_hom (factor R n) i

/-- Coordinates are evaluated through the existing literal/lifted comparison;
the product source and its original factor projection remain unchanged. -/
abbrev liftedProjection (n : ℕ) (i : Fin n) :
    source R n ⟶ ProjectiveSpace R (ULift.{u} (Fin 2)) :=
  projection R n i ≫ (ProjectiveSpace.finUliftIso R 2).hom

-- The fundamental projection and line-chart rules supply simp normalization.
@[reassoc]
theorem liftedProjection_over (n : ℕ) (i : Fin n) :
    liftedProjection R n i ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)) =
      structureMap R n := by
  rw [Category.assoc, ProjectiveSpace.finUliftIso_hom_toSpec]
  exact projection_over R n i

/-- The original product structure map is proper over every base ring. -/
instance structureMap_isProper (n : ℕ) : IsProper (structureMap R n) := by
  let : ∀ i : Fin n, IsProper (factor R n i).hom := fun _ => by
    change IsProper (Scheme.ProjectiveLine.structureMap R)
    infer_instance
  exact Scheme.isProper_finiteProductOver (factor R n)

@[simp]
theorem source_zero : source R 0 = Spec (CommRingCat.of R) := rfl

@[simp]
theorem structureMap_zero : structureMap R 0 = 𝟙 (Spec (CommRingCat.of R)) := rfl

/-- The target has exactly the original `n+1` coefficient positions, lifted
only to the coefficient ring's universe. -/
abbrev target (n : ℕ) : Scheme.{u} := ProjectiveSpace R (ULift.{u} (Fin (n + 1)))

/-- The zero-factor product maps isomorphically to the original projective zero-space. -/
def zeroIso : source R 0 ≅ target R 0 :=
  (asIso (ProjectiveSpace.toSpec R (ULift.{u} (Fin 1)))).symm

/-- The actual empty-product binary-form map. Its only coordinate is one. -/
abbrev zeroMap : source R 0 ⟶ target R 0 := (zeroIso R).hom

@[reassoc (attr := simp)]
theorem zeroMap_over :
    zeroMap R ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 1)) = structureMap R 0 :=
  (asIso (ProjectiveSpace.toSpec R (ULift.{u} (Fin 1)))).inv_hom_id

instance zeroMap_isFinite : IsFinite (zeroMap R) := by
  change IsFinite (zeroIso R).hom
  infer_instance

instance zeroMap_surjective : Surjective (zeroMap R) := by
  change Surjective (zeroIso R).hom
  infer_instance

/-- The zero-factor map commutes with every original coefficient base change. -/
theorem zeroMap_baseChange {S : Type u} [CommRing S] (σ : R →+* S) :
    zeroMap S ≫ ProjectiveSpace.map σ (ULift.{u} (Fin 1)) =
      Spec.map (CommRingCat.ofHom σ) ≫ zeroMap R := by
  apply (cancel_mono (ProjectiveSpace.toSpec R (ULift.{u} (Fin 1)))).mp
  simp [ProjectiveSpace.map_toSpec]

end AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct
