/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DirectImageClassReconstruction
public import Aglib.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.OrdinaryBoundedNatIso

/-! # Actual bounded-functor stage representatives

An original class with coefficients pulled back from T is first represented
using the actual direct-image stage system. The proved ordinary smooth mate
then produces a stage class whose coefficients are pulled back from the
original direct image on T_i. The return equation retains the same canonical
mate, cone projection, cohomological pullback and counit. No positive-degree
smooth exchange or stage-class-vanishing premise is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe u e
attribute [local instance] hasSheafifyLarge

/-- The complete stage producer on the actual bounded functor carriers. -/
theorem exists_smooth_bounded_stage_class
    {I : Type u} [Category.{u} I] [IsFiltered I]
    (X : I ⥤ Scheme.{u}ᵒᵖ) (c : Cocone X) (hc : IsColimit c)
    [∀ i, IsAffine (X.obj i).unop]
    [∀ {i j} (a : i ⟶ j), IsAffineHom (X.map a).unop]
    [∀ i, HasExt.{e} (AbelianSheaf.{u, u + 1} (X.obj i).unop)]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} c.pt.unop)]
    [HasColimitsOfShape I AddCommGrpCat.{e}] [UnivLE.{u, e}]
    {T : Scheme.{u}} (b : c.pt.unop ⟶ T)
    (Ti : I → Scheme.{u}) (p : ∀ i, T ⟶ Ti i)
    (bi : ∀ i, (X.obj i).unop ⟶ Ti i)
    (h : ∀ i, IsPullback b (c.ι.app i).unop (p i) (bi i))
    [∀ i, Smooth (bi i)]
    (n : ℕ) (hn : 0 < n) (F : (boundedCoefficientProperty T n).FullSubcategory)
    (q : ℕ) (a : Sheaf.H.{e} (((boundedCoefficientProperty T n).ι ⋙ inverseImage b).obj F) q) :
    ∃ (i : I)
      (aᵢ : Sheaf.H.{e} ((boundedBaseChangeSource (p i) (bi i) n).obj F) q),
      cohomologyTransfer (X := (X.obj i).unop) (Y := c.pt.unop) (c.ι.app i).unop
        ((inverseImageAdjunction (c.ι.app i).unop).counit.app
          (((boundedCoefficientProperty T n).ι ⋙ inverseImage b).obj F)) q
        (Sheaf.H.map
          ((boundedBaseChangeMap (p i) (c.ι.app i).unop (bi i) b (h i).w.symm n).app F)
          q aᵢ) = a := by
  exact exists_stage_class_of_whole_coefficient_maps X c hc
    ((boundedCoefficientProperty T n).ι ⋙ inverseImage b)
    (fun i => boundedBaseChangeSource (p i) (bi i) n)
    (fun i => boundedBaseChangeMap (p i) (c.ι.app i).unop (bi i) b (h i).w.symm n)
    (fun i => boundedBaseChangeMap_isIso (p i) (c.ι.app i).unop (bi i) b (h i) n hn)
    F q a

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
