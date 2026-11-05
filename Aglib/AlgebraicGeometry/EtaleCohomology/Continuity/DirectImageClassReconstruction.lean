/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DirectImageCohomologyDescent
public import Aglib.CategoryTheory.Sites.SheafCohomology.FamilyNaturalIsoRepresentative

/-! # Complete class reconstruction before geometric coefficients are substituted

Combine original scheme-limit class extraction, original counit transfers,
and the supplied actual whole coefficient transformations in one construction.
The coefficient functors remain variables, so no concrete smooth mate or
pullback coefficient is unfolded to assemble the return equation.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe u e d v
attribute [local instance] hasSheafifyLarge

/-- Actual coefficient transformations to the original direct-image system
produce actual stage representatives and their literal return equation. -/
theorem exists_stage_class_of_whole_coefficient_maps
    {I : Type u} [Category.{u} I] [IsFiltered I]
    (X : I ⥤ Scheme.{u}ᵒᵖ) (c : Cocone X) (hc : IsColimit c)
    [∀ i, IsAffine (X.obj i).unop]
    [∀ {i j} (a : i ⟶ j), IsAffineHom (X.map a).unop]
    [∀ i, HasExt.{e} (AbelianSheaf.{u, u + 1} (X.obj i).unop)]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} c.pt.unop)]
    [HasColimitsOfShape I AddCommGrpCat.{e}] [UnivLE.{u, e}]
    {D : Type d} [Category.{v} D]
    (L : D ⥤ AbelianSheaf.{u, u + 1} c.pt.unop)
    (Li : ∀ i, D ⥤ AbelianSheaf.{u, u + 1} (X.obj i).unop)
    (α : ∀ i, Li i ⟶ L ⋙ directImage (c.ι.app i).unop)
    (hα : ∀ i, IsIso (α i)) (M : D) (q : ℕ)
    (a : Sheaf.H.{e} (L.obj M) q) :
    ∃ (i : I) (aᵢ : Sheaf.H.{e} ((Li i).obj M) q),
      cohomologyTransfer (X := (X.obj i).unop) (Y := c.pt.unop) (c.ι.app i).unop
        ((inverseImageAdjunction (c.ι.app i).unop).counit.app (L.obj M)) q
        (Sheaf.H.map ((α i).app M) q aᵢ) = a := by
  let : ∀ i, IsIso (α i) := hα
  let r : ∀ i : I,
      Sheaf.H.{e} ((directImage (c.ι.app i).unop).obj (L.obj M)) q →
        Sheaf.H.{e} (L.obj M) q :=
    fun i z => (cohomologyTransfer.{u, e}
      (X := (X.obj i).unop) (Y := c.pt.unop) (c.ι.app i).unop
      ((inverseImageAdjunction (c.ι.app i).unop).counit.app (L.obj M)) q).hom z
  exact Sheaf.H.exists_family_naturalIso_representative_return
    (A := Sheaf.H.{e} (L.obj M) q)
    (fun i => (X.obj i).unop.smallEtaleTopology)
    (fun i => asIso (α i)) M q r a
    (exists_directImage_stage_class X c hc (L.obj M) q a)

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
