/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.Restriction
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.Comparison
public import Aglib.CategoryTheory.Sites.SheafCohomology.Slice.Naturality

/-!
# Native module cohomology on slices

The maps are induced by the original exact ringed-site restriction, not by
conjugating the module-to-abelian equivalence. Their compatibility is proved
from the section-one source square and functoriality of native Ext.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe u v r w m e₁ e₂ e₃ e₄

namespace CategoryTheory.Sheaf.ModuleCoefficients

section ExactSquare

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasExt.{e₁} A] [HasExt.{e₂} B] [HasExt.{e₃} C] [HasExt.{e₄} D]
  (P : A ⥤ C) (R : A ⥤ B) (S : C ⥤ D) (Q : B ⥤ D)
  [P.Additive] [R.Additive] [S.Additive] [Q.Additive]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]
  [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]

/-- Exact-functor source squares commute on the actual Ext classes.
The complete equation is abstracted before specializing to ringed sites. -/
theorem extPrecompMap_square (τ : R ⋙ Q ⟶ P ⋙ S)
    {X F : A} {Y : C} {Z : B} {W : D}
    (a : Z ⟶ R.obj X) (b : W ⟶ S.obj Y) (c : Y ⟶ P.obj X)
    (d : W ⟶ Q.obj Z) (h : d ≫ Q.map a ≫ τ.app X = b ≫ S.map c)
    (n : ℕ) (x : Ext.{e₁} X F n) :
    (SliceCohomology.extRestrictionMap Q d (τ.app F) n)
      (R.extPrecompMap a F n x) =
    S.extPrecompMap b (P.obj F) n (P.extPrecompMap c F n x) := by
  change ((Ext.mk₀ d).comp
      (((Ext.mk₀ a).comp (x.mapExactFunctor R) (Nat.zero_add n)).mapExactFunctor Q)
      (Nat.zero_add n)).comp (Ext.mk₀ (τ.app F)) (Nat.add_zero n) =
    (Ext.mk₀ b).comp
      (((Ext.mk₀ c).comp (x.mapExactFunctor P) (Nat.zero_add n)).mapExactFunctor S)
      (Nat.zero_add n)
  simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  rw [← Ext.comp_mapExactFunctor, ← Ext.comp_mapExactFunctor]
  simp only [Ext.comp_assoc_of_third_deg_zero]
  rw [Ext.mapExactFunctor_comp_mk₀_natTransApp x τ]
  simp only [Ext.mk₀_comp_mk₀_assoc]
  rw [h]

end ExactSquare

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{r}) {U V : C} (f : U ⟶ V)
  [HasSheafify (J.over U) AddCommGrpCat.{max r w}]
  [HasSheafify (J.over V) AddCommGrpCat.{max r w}]

omit [HasSheafify (J.over U) AddCommGrpCat.{max r w}]
  [HasSheafify (J.over V) AddCommGrpCat.{max r w}] in
/-- Evaluation of native constant-source restriction is restriction of sections. -/
theorem integerHomTerminalEquiv_overMap
    [HasSheafify (J.over U) AddCommGrpCat.{m}]
    [HasSheafify (J.over V) AddCommGrpCat.{m}]
    (F : Sheaf (J.over V) AddCommGrpCat.{m})
    (a : (constantSheaf (J.over V) AddCommGrpCat.{m}).obj
      (AddCommGrpCat.of (ULift.{m} ℤ)) ⟶ F) :
    integerHomTerminalEquiv Over.mkIdTerminal _
      (SliceCohomology.constantOverMap J f (AddCommGrpCat.of (ULift.{m} ℤ)) ≫
        (SliceCohomology.overMapRestriction J f).map a) =
      F.obj.map (Over.mkIdTerminal.from ((Over.map f).obj (Over.mk (𝟙 U)))).op
        (integerHomTerminalEquiv Over.mkIdTerminal F a) := by
  dsimp only [integerHomTerminalEquiv, AddEquiv.trans_apply, Adjunction.homAddEquiv_apply]
  rw [SliceCohomology.constantOverMap_sections]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The native integer-source restriction and lifted-unit transport preserve section one. -/
theorem liftedUnitIntegerMap_overMap :
    SliceCohomology.constantOverMap J f (AddCommGrpCat.of (ULift.{max r w} ℤ)) ≫
      (SliceCohomology.overMapRestriction J f).map
        (liftedUnitIntegerMap.{max u v, v, r, w} Over.mkIdTerminal (R.over V)) =
    liftedUnitIntegerMap.{max u v, v, r, w} Over.mkIdTerminal (R.over U) ≫
      (SheafOfModules.toSheaf (R.over U)).map
        (SheafOfModules.overMapLiftedUnitIso.{u, v, r, w} R f).inv := by
  apply (integerHomTerminalEquiv Over.mkIdTerminal _).injective
  rw [integerHomTerminalEquiv_overMap f, liftedUnitIntegerMap_sections.{max u v, v, r, w},
    integerHomTerminalEquiv_comp, liftedUnitIntegerMap_sections.{max u v, v, r, w}]
  change ULift.up ((R.over V).obj.map
      (Over.mkIdTerminal.from ((Over.map f).obj (Over.mk (𝟙 U)))).op 1) = ULift.up 1
  rw [map_one]

variable [HasBinaryProducts C] [HasPullbacks C]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max r w}]
  [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{max r w}]
  [(J.over U).HasSheafCompose (forget AddCommGrpCat.{max r w})]
  [(J.over V).HasSheafCompose (forget AddCommGrpCat.{max r w})]
  [HasExt.{e₁} (SheafOfModules.{max r w} (R.over V))]
  [HasExt.{e₂} (SheafOfModules.{max r w} (R.over U))]
  [HasExt.{e₃} (Sheaf (J.over V) AddCommGrpCat.{max r w})]
  [HasExt.{e₄} (Sheaf (J.over U) AddCommGrpCat.{max r w})]

/-- Restriction on module cohomology is induced by the original exact `overMap`. -/
def overMapCohomologyRestriction (M : SheafOfModules.{max r w} (R.over V)) (n : ℕ) :
    Ext.{e₁} (SheafOfModules.liftedUnit.{max u v, v, w, r} (R.over V)) M n →+
      Ext.{e₂} (SheafOfModules.liftedUnit.{max u v, v, w, r} (R.over U))
        ((SheafOfModules.overMap R f).obj M) n :=
  (SheafOfModules.overMap R f).extPrecompMap
    (SheafOfModules.overMapLiftedUnitIso.{u, v, r, w} R f).inv M n

/-- The underlying abelian restriction is the original exact slice functor. -/
def overMapAbCohomologyRestriction
    [HasSheafify (J.over U) AddCommGrpCat.{m}]
    [HasSheafify (J.over V) AddCommGrpCat.{m}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{m}]
    [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{m}]
    [(J.over U).HasSheafCompose (forget AddCommGrpCat.{m})]
    [(J.over V).HasSheafCompose (forget AddCommGrpCat.{m})]
    [HasExt.{e₃} (Sheaf (J.over V) AddCommGrpCat.{m})]
    [HasExt.{e₄} (Sheaf (J.over U) AddCommGrpCat.{m})]
    (F : Sheaf (J.over V) AddCommGrpCat.{m}) (n : ℕ) :
    Sheaf.H.{e₃} F n →+
      Sheaf.H.{e₄} ((SliceCohomology.overMapRestriction J f).obj F) n :=
  (SliceCohomology.overMapRestriction J f).extPrecompMap
    (SliceCohomology.constantOverMap J f (AddCommGrpCat.of (ULift.{m} ℤ))) F n

omit [HasBinaryProducts C] in
set_option backward.isDefEq.respectTransparency false in
/-- Restriction commutes with the canonical module-to-abelian comparison in every degree. -/
theorem cohomologyMap_overMap (M : SheafOfModules.{max r w} (R.over V)) (n : ℕ)
    (x : Ext.{e₁} (SheafOfModules.liftedUnit.{max u v, v, w, r} (R.over V)) M n) :
    cohomologyMap.{max u v, v, r, w, e₂, e₄} Over.mkIdTerminal (R.over U)
      ((SheafOfModules.overMap R f).obj M) n
      (overMapCohomologyRestriction.{u, v, r, w, e₁, e₂} R f M n x) =
    overMapAbCohomologyRestriction f ((SheafOfModules.toSheaf (R.over V)).obj M) n
      (cohomologyMap.{max u v, v, r, w, e₁, e₃} Over.mkIdTerminal (R.over V) M n x) := by
  have h := extPrecompMap_square (SheafOfModules.overMap R f)
    (SheafOfModules.toSheaf (R.over V)) (SheafOfModules.toSheaf (R.over U))
    (SliceCohomology.overMapRestriction J f)
    (SheafOfModules.overMapCompToSheaf R f).inv
    (liftedUnitIntegerMap.{max u v, v, r, w} Over.mkIdTerminal (R.over V))
    (liftedUnitIntegerMap.{max u v, v, r, w} Over.mkIdTerminal (R.over U))
    (SheafOfModules.overMapLiftedUnitIso.{u, v, r, w} R f).inv
    (SliceCohomology.constantOverMap J f (AddCommGrpCat.of (ULift.{max r w} ℤ)))
    (by
      change SliceCohomology.constantOverMap J f (AddCommGrpCat.of (ULift.{max r w} ℤ)) ≫
        (SliceCohomology.overMapRestriction J f).map
          (liftedUnitIntegerMap.{max u v, v, r, w} Over.mkIdTerminal (R.over V)) ≫
        𝟙 ((SliceCohomology.overMapRestriction J f).obj
          ((SheafOfModules.toSheaf (R.over V)).obj
            (SheafOfModules.liftedUnit.{max u v, v, w, r} (R.over V)))) = _
      rw [Category.comp_id]
      exact liftedUnitIntegerMap_overMap.{u, v, r, w} R f) n x
  have h' := h.symm
  change cohomologyMap.{max u v, v, r, w, e₂, e₄} Over.mkIdTerminal (R.over U)
      ((SheafOfModules.overMap R f).obj M) n
      (overMapCohomologyRestriction.{u, v, r, w, e₁, e₂} R f M n x) =
    ((Ext.mk₀ (SliceCohomology.constantOverMap J f
      (AddCommGrpCat.of (ULift.{max r w} ℤ)))).comp
      ((cohomologyMap.{max u v, v, r, w, e₁, e₃} Over.mkIdTerminal
        (R.over V) M n x).mapExactFunctor (SliceCohomology.overMapRestriction J f))
      (zero_add n)).comp
      (Ext.mk₀ (𝟙 ((SliceCohomology.overMapRestriction J f).obj
        ((SheafOfModules.toSheaf (R.over V)).obj M)))) (add_zero n) at h'
  rw [Ext.comp_mk₀_id] at h'
  exact h'


end CategoryTheory.Sheaf.ModuleCoefficients

namespace CategoryTheory.Sheaf.ModuleCoefficients

universe eM eA

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (U : C)
  [HasSheafify (J.over U) AddCommGrpCat.{max u v}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [(J.over U).HasSheafCompose (forget AddCommGrpCat.{max u v})]
  [∀ W : Over U, HasFiniteProducts (Over W)]
  [HasExt.{eA} (Sheaf (J.over U) AddCommGrpCat.{max u v})]
  [EnoughInjectives (Sheaf (J.over U) AddCommGrpCat.{max u v})]

/-- On each actual ringed slice, genuine injective acyclicity gives the
canonical comparison for unchanged small scalars and original restriction. -/
def sliceModuleExtCohomologyAddEquiv (R : Sheaf J RingCat.{v})
    [HasExt.{eM} (SheafOfModules.{max u v} (R.over U))]
    (M : SheafOfModules.{max u v} R) (n : ℕ) :
    Ext.{eM} (SheafOfModules.liftedUnit.{max u v, v, max u v, v} (R.over U))
      (M.over U) n ≃+ Sheaf.H.{eA} (((SheafOfModules.toSheaf R).obj M).over U) n :=
  moduleExtCohomologyAddEquiv Over.mkIdTerminal (R.over U) (M.over U) n

/-- The corresponding original slice comparison for aligned large scalars. -/
def sliceModuleExtCohomologyAddEquivLargeScalars (R : Sheaf J RingCat.{max u v})
    [HasExt.{eM} (SheafOfModules.{max u v} (R.over U))]
    (M : SheafOfModules.{max u v} R) (n : ℕ) :
    Ext.{eM} (SheafOfModules.liftedUnit.{max u v, v, max u v, max u v} (R.over U))
      (M.over U) n ≃+ Sheaf.H.{eA} (((SheafOfModules.toSheaf R).obj M).over U) n :=
  moduleExtCohomologyAddEquivLargeScalars Over.mkIdTerminal (R.over U) (M.over U) n

end CategoryTheory.Sheaf.ModuleCoefficients
