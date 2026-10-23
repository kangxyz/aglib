/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.InjectiveAcyclic
public import Aglib.CategoryTheory.Sites.SheafCohomology.Slice.Comparison

/-! # Underlying module-injective acyclicity on the original slices -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace CategoryTheory.Sheaf.ModuleCoefficients

universe e e' v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v})]
  [∀ W : C, HasFiniteProducts (Over W)]
  [HasExt.{e} (Sheaf J AddCommGrpCat.{max u v})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{max u v})]

/-- Native slice comparison transports this original Ext vanishing to native slice cohomology.
No preservation of module injectives by restriction is presumed. -/
theorem toSheaf_injective_over_cohomology_subsingleton
    (R : Sheaf J RingCat.{v}) (I : SheafOfModules.{max u v} R) [Injective I]
    (W : C) [HasSheafify (J.over W) AddCommGrpCat.{max u v}]
    [(J.over W).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [(J.over W).HasSheafCompose (forget AddCommGrpCat.{max u v})]
    [HasExt.{e'} (Sheaf (J.over W) AddCommGrpCat.{max u v})] (n : ℕ) :
    Subsingleton (Sheaf.H.{e'} (((SheafOfModules.toSheaf R).obj I).over W) (n + 1)) := by
  let E := SliceCohomology.sliceComparison.{e, e', u} J W
    ((SheafOfModules.toSheaf R).obj I) (n + 1)
  have h : Subsingleton (Ext.{e} (Hypercohomology.freeAbelianSheaf.{u} J W)
      ((SheafOfModules.toSheaf R).obj I) (n + 1)) :=
    toSheaf_injective_ext_subsingleton R I W n
  exact ⟨fun a b => E.symm.injective (h.elim _ _)⟩


/-- For large scalar rings, native slice comparison transports original Ext vanishing
to native slice cohomology.
No preservation of module injectives by restriction is presumed. -/
theorem toSheaf_injective_over_cohomology_subsingleton_largeScalars
    (R : Sheaf J RingCat.{max u v}) (I : SheafOfModules.{max u v} R) [Injective I]
    (W : C) [HasSheafify (J.over W) AddCommGrpCat.{max u v}]
    [(J.over W).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [(J.over W).HasSheafCompose (forget AddCommGrpCat.{max u v})]
    [HasExt.{e'} (Sheaf (J.over W) AddCommGrpCat.{max u v})] (n : ℕ) :
    Subsingleton (Sheaf.H.{e'} (((SheafOfModules.toSheaf R).obj I).over W) (n + 1)) := by
  let E := SliceCohomology.sliceComparison.{e, e', u} J W
    ((SheafOfModules.toSheaf R).obj I) (n + 1)
  have h : Subsingleton (Ext.{e} (Hypercohomology.freeAbelianSheaf.{u} J W)
      ((SheafOfModules.toSheaf R).obj I) (n + 1)) :=
    toSheaf_injective_ext_subsingleton_largeScalars R I W n
  exact ⟨fun a b => E.symm.injective (h.elim _ _)⟩


end CategoryTheory.Sheaf.ModuleCoefficients
