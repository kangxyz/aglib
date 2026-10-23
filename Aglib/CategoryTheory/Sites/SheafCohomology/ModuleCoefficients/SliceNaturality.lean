/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.Slice

/-!
# Module restriction and the original abelian slice restriction

For coefficients restricted from the base, the endpoint transport is
Mathlib's original `overFunctorMap`. The resulting square uses the original
A1 slice restriction, rather than defining either map by the comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe u v r w e₀ e₁ e₂ e₃ e₄

namespace CategoryTheory.Sheaf.ModuleCoefficients

private theorem extFullRestriction_square
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasExt.{e₁} A] [HasExt.{e₂} B] [HasExt.{e₃} C] [HasExt.{e₄} D]
    (P : A ⥤ C) (R : A ⥤ B) (S : C ⥤ D) (Q : B ⥤ D)
    [P.Additive] [R.Additive] [S.Additive] [Q.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (τ : R ⋙ Q ⟶ P ⋙ S) {X F : A} {Y N : C} {Z : B} {W : D}
    (a : Z ⟶ R.obj X) (b : W ⟶ S.obj Y) (c : Y ⟶ P.obj X)
    (d : W ⟶ Q.obj Z) (h : d ≫ Q.map a ≫ τ.app X = b ≫ S.map c)
    (g : P.obj F ⟶ N) (k : Q.obj (R.obj F) ⟶ S.obj N)
    (hk : τ.app F ≫ S.map g = k) (n : ℕ) (x : Ext.{e₁} X F n) :
    S.extPrecompMap b N n (SliceCohomology.extRestrictionMap P c g n x) =
      SliceCohomology.extRestrictionMap Q d k n (R.extPrecompMap a F n x) := by
  change S.extPrecompMap b N n
      ((P.extPrecompMap c F n x).comp (Ext.mk₀ g) (Nat.add_zero n)) = _
  rw [Functor.extPrecompMap_comp, Ext.mapExactFunctor_mk₀,
    ← extPrecompMap_square P R S Q τ a b c d h]
  change (((Ext.mk₀ d).comp
      ((R.extPrecompMap a F n x).mapExactFunctor Q) (Nat.zero_add n)).comp
      (Ext.mk₀ (τ.app F)) (Nat.add_zero n)).comp (Ext.mk₀ (S.map g)) (Nat.add_zero n) = _
  rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, hk]
  rfl

private theorem toSheaf_overFunctorMap
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{r}) {U V : C} (f : U ⟶ V)
    (M : SheafOfModules.{max v r w} R) :
    (SheafOfModules.toSheaf (R.over U)).map
      ((SheafOfModules.overFunctorMap R f).hom.app M) =
      (SliceCohomology.overMapRestrictionIso.{max r w, v, u} J f).hom.app
        ((SheafOfModules.toSheaf R).obj M) := by
  ext W z
  rfl

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasBinaryProducts C] [HasPullbacks C]
  (R : Sheaf J RingCat.{r}) {U V : C} (f : U ⟶ V)
  [HasSheafify J AddCommGrpCat.{max v r w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max v r w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max v r w})]
  [HasSheafify (J.over U) AddCommGrpCat.{max v r w}]
  [HasSheafify (J.over V) AddCommGrpCat.{max v r w}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max v r w}]
  [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{max v r w}]
  [(J.over U).HasSheafCompose (forget AddCommGrpCat.{max v r w})]
  [(J.over V).HasSheafCompose (forget AddCommGrpCat.{max v r w})]
  [HasExt.{e₀} (Sheaf J AddCommGrpCat.{max v r w})]
  [HasExt.{e₁} (SheafOfModules.{max v r w} (R.over V))]
  [HasExt.{e₂} (SheafOfModules.{max v r w} (R.over U))]
  [HasExt.{e₃} (Sheaf (J.over V) AddCommGrpCat.{max v r w})]
  [HasExt.{e₄} (Sheaf (J.over U) AddCommGrpCat.{max v r w})]

/-- Native module restriction on coefficients originating on the base site. -/
def sliceModuleRestriction (M : SheafOfModules.{max v r w} R) (n : ℕ) :
    Ext.{e₁} (SheafOfModules.liftedUnit.{max u v, v, max v w, r} (R.over V))
      (M.over V) n →+
    Ext.{e₂} (SheafOfModules.liftedUnit.{max u v, v, max v w, r} (R.over U))
      (M.over U) n :=
  SliceCohomology.extRestrictionMap (SheafOfModules.overMap R f)
    (SheafOfModules.overMapLiftedUnitIso.{u, v, r, max v w} R f).inv
    ((SheafOfModules.overFunctorMap R f).hom.app M) n

omit [HasSheafify J AddCommGrpCat.{max v r w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max v r w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max v r w})]
  [(J.over U).HasSheafCompose (forget AddCommGrpCat.{max v r w})]
  [(J.over V).HasSheafCompose (forget AddCommGrpCat.{max v r w})]
  [HasExt.{e₀} (Sheaf J AddCommGrpCat.{max v r w})]
  [HasExt.{e₃} (Sheaf (J.over V) AddCommGrpCat.{max v r w})]
  [HasExt.{e₄} (Sheaf (J.over U) AddCommGrpCat.{max v r w})] in
omit [HasBinaryProducts C] in
/-- The original module restriction, with its actual coefficient transport. -/
theorem sliceModuleRestriction_apply (M : SheafOfModules.{max v r w} R) (n : ℕ)
    (x : Ext.{e₁} (SheafOfModules.liftedUnit.{max u v, v, max v w, r} (R.over V))
      (M.over V) n) :
    sliceModuleRestriction R f M n x =
      (overMapCohomologyRestriction.{u, v, r, max v w, e₁, e₂} R f (M.over V) n x).comp
        (Ext.mk₀ ((SheafOfModules.overFunctorMap R f).hom.app M)) (Nat.add_zero n) := rfl

omit [HasSheafify J AddCommGrpCat.{max v r w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max v r w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max v r w})]
  [HasExt.{e₀} (Sheaf J AddCommGrpCat.{max v r w})] in
omit [HasBinaryProducts C] in
/-- The module-to-abelian comparison commutes with the original A1 slice restriction. -/
theorem cohomologyMap_sliceRestriction (M : SheafOfModules.{max v r w} R) (n : ℕ)
    (x : Ext.{e₁} (SheafOfModules.liftedUnit.{max u v, v, max v w, r} (R.over V))
      (M.over V) n) :
    cohomologyMap.{max u v, v, r, max v w, e₂, e₄} Over.mkIdTerminal (R.over U) (M.over U) n
      (sliceModuleRestriction R f M n x) =
    SliceCohomology.sliceRestriction.{e₃, e₄, max r w, v, u} J f
      ((SheafOfModules.toSheaf R).obj M) n
      (cohomologyMap.{max u v, v, r, max v w, e₁, e₃} Over.mkIdTerminal (R.over V)
        (M.over V) n x) := by
  exact extFullRestriction_square (SheafOfModules.overMap R f)
    (SheafOfModules.toSheaf (R.over V)) (SheafOfModules.toSheaf (R.over U))
    (SliceCohomology.overMapRestriction J f)
    (SheafOfModules.overMapCompToSheaf R f).inv
    (F := M.over V) (N := M.over U)
    (liftedUnitIntegerMap.{max u v, v, r, max v w} Over.mkIdTerminal (R.over V))
    (liftedUnitIntegerMap.{max u v, v, r, max v w} Over.mkIdTerminal (R.over U))
    (SheafOfModules.overMapLiftedUnitIso.{u, v, r, max v w} R f).inv
    (SliceCohomology.constantOverMap J f (AddCommGrpCat.of (ULift.{max v r w} ℤ)))
    (by
      change SliceCohomology.constantOverMap J f
        (AddCommGrpCat.of (ULift.{max v r w} ℤ)) ≫
        (SliceCohomology.overMapRestriction J f).map
          (liftedUnitIntegerMap.{max u v, v, r, max v w} Over.mkIdTerminal (R.over V)) ≫
        𝟙 ((SliceCohomology.overMapRestriction J f).obj
          ((SheafOfModules.toSheaf (R.over V)).obj
            (SheafOfModules.liftedUnit.{max u v, v, max v w, r} (R.over V)))) = _
      rw [Category.comp_id]
      exact liftedUnitIntegerMap_overMap.{u, v, r, max v w} R f)
    ((SheafOfModules.overFunctorMap R f).hom.app M)
    ((SliceCohomology.overMapRestrictionIso.{max r w, v, u} J f).hom.app
      ((SheafOfModules.toSheaf R).obj M))
    (by
      change 𝟙 ((SheafOfModules.toSheaf (R.over U)).obj
        ((SheafOfModules.overMap R f).obj (M.over V))) ≫
        (SheafOfModules.toSheaf (R.over U)).map
          ((SheafOfModules.overFunctorMap R f).hom.app M) = _
      rw [Category.id_comp]
      exact toSheaf_overFunctorMap R f M) n x

end CategoryTheory.Sheaf.ModuleCoefficients
