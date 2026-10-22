/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.SchemeTheoreticImage.ProperComparison
public import Aglib.AlgebraicGeometry.Limits.FiniteProducts

/-!
# Comparing schematic images in finite proper ambient products

Componentwise ambient maps preserving the original source induce an actual
proper surjective map between the schematic images in the finite products.
The original source factor and every projection triangle are retained.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory Limits
universe u

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} {U : Over S} {n : ℕ} {C' C : Fin n → Over S}
variable (β : ∀ i, C' i ⟶ C i) (j' : ∀ i, U ⟶ C' i) (j : ∀ i, U ⟶ C i)
    (w : ∀ i, j' i ≫ β i = j i)

include w in
/-- Compatibility of the literal finite-product maps with the original source. -/
lemma finiteProductOverLift_map_comp :
    finiteProductOverLift C' j' ≫ finiteProductOverMap β = finiteProductOverLift C j := by
  apply finiteProductOver_hom_ext C
  intro i
  simp only [Category.assoc, finiteProductOverMap_π,
    finiteProductOverLift_π_assoc, finiteProductOverLift_π, w]

variable [QuasiCompact (finiteProductOverLift C' j').left]
    [QuasiCompact (finiteProductOverLift C j).left]

/-- Actual schematic-image comparison for the finite-product ambient maps. -/
def finiteProductImageComparison :
    (finiteProductOverLift C' j').left.image ⟶ (finiteProductOverLift C j).left.image :=
  imageComparison (finiteProductOverLift C' j').left (finiteProductOverLift C j).left
    (finiteProductOverMap β).left
    (congrArg (fun a => a.left) (finiteProductOverLift_map_comp β j' j w))

@[reassoc (attr := simp)]
lemma finiteProductImageComparison_imageι :
    finiteProductImageComparison β j' j w ≫ (finiteProductOverLift C j).left.imageι =
      (finiteProductOverLift C' j').left.imageι ≫ (finiteProductOverMap β).left :=
  imageComparison_imageι _ _ _ _

@[reassoc (attr := simp)]
lemma toImage_finiteProductImageComparison :
    (finiteProductOverLift C' j').left.toImage ≫ finiteProductImageComparison β j' j w =
      (finiteProductOverLift C j).left.toImage :=
  toImage_imageComparison _ _ _ _

/-- Each projection of the image comparison is the original component map. -/
@[reassoc]
lemma finiteProductImageComparison_π (i : Fin n) :
    finiteProductImageComparison β j' j w ≫ (finiteProductOverLift C j).left.imageι ≫
        (finiteProductOverπ C i).left =
      (finiteProductOverLift C' j').left.imageι ≫ (finiteProductOverπ C' i).left ≫
        (β i).left := by
  rw [← Category.assoc, finiteProductImageComparison_imageι, Category.assoc]
  congr 1
  exact congrArg (fun a => a.left) (finiteProductOverMap_π β i)

/-- Proper finite ambient models give a proper comparison; the individual
ambient maps need not themselves be supplied as proper. -/
theorem finiteProductImageComparison_isProper
    [∀ i, IsProper (C' i).hom] [∀ i, IsProper (C i).hom] :
    IsProper (finiteProductImageComparison β j' j w) := by
  let : IsProper (finiteProductOver C').hom := isProper_finiteProductOver C'
  let : IsProper (finiteProductOver C).hom := isProper_finiteProductOver C
  exact imageComparison_isProper _ _ _ _ (finiteProductOver C').hom
    (finiteProductOver C).hom (finiteProductOverMap β).w

/-- The actual map of finite-product schematic images is also surjective. -/
theorem finiteProductImageComparison_surjective
    [∀ i, IsProper (C' i).hom] [∀ i, IsProper (C i).hom] :
    Surjective (finiteProductImageComparison β j' j w) := by
  have hp : IsProper (finiteProductImageComparison β j' j w) :=
    finiteProductImageComparison_isProper β j' j w
  unfold finiteProductImageComparison at hp ⊢
  let := hp
  exact imageComparison_surjective _ _ _ _

end AlgebraicGeometry.Scheme
