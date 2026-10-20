/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.Finite.GeometricDegreeOperations
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Literal multiplication conjugacy under an actual group isomorphism

Source: `R5Lab.AlgebraicGeometry.EllipticCurve.Tate.DualIsogeny`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`, original lines 632–657.
Only the stated generic slice is admitted; its actual objects, maps and hypotheses are retained.
-/

@[expose] public section

noncomputable section
open CategoryTheory AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.OverField
namespace AlgebraicGeometry.Scheme.Group.Multiplication
universe u
attribute [local instance] Over.cartesianMonoidalCategory
variable {F : Type u} [Field F]

/-- Literal multiplication is conjugate under any actual group-scheme
isomorphism, as an equality of morphisms over the original field. -/
theorem multiplication_eq_conjugate {G H : Grp (FScheme F)} (e : G ≅ H) (n : ℕ) :
    (𝟙 G.X) ^ n = e.hom.hom.hom ≫ ((𝟙 H.X) ^ n) ≫ e.inv.hom.hom := by
  have hi : e.hom.hom.hom ≫ e.inv.hom.hom = 𝟙 G.X :=
    ((Grp.forget (FScheme F)).mapIso e).hom_inv_id
  rw [← Category.assoc, MonObj.comp_pow, Category.comp_id, MonObj.pow_comp, hi]

/-- Transfer the independently proved target multiplication properties across
an actual target group-scheme identification. No reverse-map property is input. -/
theorem multiplication_geometry_of_iso {G H : Grp (FScheme F)} (e : G ≅ H)
    (n : ℕ) (hn : 0 < n)
    (hf : IsFinite ((𝟙 H.X) ^ n).left) (he : Etale ((𝟙 H.X) ^ n).left)
    (hd : HasGeometricDegree ((𝟙 H.X) ^ n) (n * n)) :
    IsFinite ((𝟙 G.X) ^ n).left ∧ Etale ((𝟙 G.X) ^ n).left ∧
    HasGeometricDegree ((𝟙 G.X) ^ n) (n * n) := by
  let := hf
  let := he
  let E := ((Grp.forget (FScheme F)) ⋙ Over.forget (Base F)).mapIso e
  let : IsIso e.hom.hom.hom.left := by
    change IsIso E.hom
    infer_instance
  let : IsIso e.inv.hom.hom.left := by
    change IsIso E.inv
    infer_instance
  rw [multiplication_eq_conjugate e n]
  refine ⟨?_, ?_, ?_⟩
  · change IsFinite (e.hom.hom.hom.left ≫ ((𝟙 H.X) ^ n).left ≫ e.inv.hom.hom.left)
    infer_instance
  · change Etale (e.hom.hom.hom.left ≫ ((𝟙 H.X) ^ n).left ≫ e.inv.hom.hom.left)
    infer_instance
  · exact geometricDegree_conjugate ((Grp.forget (FScheme F)).mapIso e) _
      (Nat.mul_pos hn hn) hd


end AlgebraicGeometry.Scheme.Group.Multiplication
