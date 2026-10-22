/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Limits.FiniteProducts
public import Aglib.AlgebraicGeometry.SchemeTheoreticImage.Dominance
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# The original source in a finite-product schematic image

One immersive component makes the literal map to the finite ambient product
an immersion. If that map is quasi-compact, its native image factor is an
open immersion and schematically dominant. Noetherianity of the source
supplies quasi-compactness automatically. Proper ambient factors over a
Noetherian base make the actual schematic image Noetherian as well.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory Limits
universe u

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} {U : Over S} {n : ℕ} (C : Fin n → Over S)
    (j : ∀ i, U ⟶ C i)

/-- The map to the finite product is an immersion if one original component
is an immersion. The specified index accounts for nonemptiness. -/
theorem finiteProductOverLift_isImmersion (i : Fin n) [IsImmersion (j i).left] :
    IsImmersion (finiteProductOverLift C j).left := by
  have h : (finiteProductOverLift C j).left ≫ (finiteProductOverπ C i).left =
      (j i).left := congrArg (fun a => a.left) (finiteProductOverLift_π C j i)
  let : IsImmersion ((finiteProductOverLift C j).left ≫
      (finiteProductOverπ C i).left) := by rw [h]; infer_instance
  exact IsImmersion.of_comp _ (finiteProductOverπ C i).left

/-- The original source is an open schematically dense subscheme of its
actual finite-product image, under the explicit quasi-compactness premise. -/
theorem finiteProductOverLift_toImage_properties (i : Fin n)
    [IsImmersion (j i).left] [QuasiCompact (finiteProductOverLift C j).left] :
    IsOpenImmersion (finiteProductOverLift C j).left.toImage ∧
      IsSchemeTheoreticallyDominant (finiteProductOverLift C j).left.toImage := by
  let : IsImmersion (finiteProductOverLift C j).left :=
    finiteProductOverLift_isImmersion C j i
  exact ⟨inferInstance, isSchemeTheoreticallyDominant_toImage _⟩

/-- For a Noetherian source, the actual finite-product map is quasi-compact,
and the original source embeds openly and schematically densely in its image. -/
theorem finiteProductOverLift_source_properties_of_noetherian (i : Fin n)
    [IsNoetherian U.left] [IsImmersion (j i).left] :
    QuasiCompact (finiteProductOverLift C j).left ∧
      IsOpenImmersion (finiteProductOverLift C j).left.toImage ∧
      IsSchemeTheoreticallyDominant (finiteProductOverLift C j).left.toImage :=
  ⟨inferInstance, finiteProductOverLift_toImage_properties C j i⟩

/-- The schematic image in a finite product of proper models over a
Noetherian base is itself Noetherian. The source need not be Noetherian. -/
theorem finiteProductOverLift_image_isNoetherian
    [IsNoetherian S] [∀ i, IsProper (C i).hom] :
    IsNoetherian (finiteProductOverLift C j).left.image := by
  let : IsProper (finiteProductOver C).hom := isProper_finiteProductOver C
  let p := (finiteProductOverLift C j).left.imageι ≫ (finiteProductOver C).hom
  let : IsLocallyNoetherian (finiteProductOverLift C j).left.image :=
    LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace (finiteProductOverLift C j).left.image :=
    QuasiCompact.compactSpace_of_compactSpace p
  exact ⟨⟩

end AlgebraicGeometry.Scheme
