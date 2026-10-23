/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.DerivedRestriction
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.DerivedGamma
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.Slice

/-!
# Native derived terminal sections under ringed slice restriction

Restriction is constructed from the genuine injective-resolution comparison
on represented Hom complexes and the canonical derived evaluation isomorphisms.
Its normalization to the original exact-functor Ext map is a theorem, not its
definition. The source and target remain native right-derived module evaluation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe u v r w e₁ e₂

namespace CategoryTheory.Sheaf.ModuleCoefficients

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasBinaryProducts C] [HasPullbacks C]
  (R : Sheaf J RingCat.{r}) {U V : C} (f : U ⟶ V)
  [HasSheafify (J.over U) AddCommGrpCat.{max u v r w}]
  [HasSheafify (J.over V) AddCommGrpCat.{max u v r w}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v r w}]
  [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v r w}]
  [EnoughInjectives (SheafOfModules.{max u v r w} (R.over U))]
  [EnoughInjectives (SheafOfModules.{max u v r w} (R.over V))]

omit [HasBinaryProducts C] [HasPullbacks C]
  [HasSheafify (J.over U) AddCommGrpCat.{max u v r w}]
  [HasSheafify (J.over V) AddCommGrpCat.{max u v r w}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v r w}]
  [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v r w}]
  [EnoughInjectives (SheafOfModules.{max u v r w} (R.over U))]
  [EnoughInjectives (SheafOfModules.{max u v r w} (R.over V))] in
set_option backward.isDefEq.respectTransparency false in
/-- The represented source map is the original restriction of module sections.
Thus the resolution construction restricts sections before applying its target lift. -/
theorem liftedUnitSections_overMap (M : SheafOfModules.{max u v r w} (R.over V))
    (a : SheafOfModules.liftedUnit.{max u v, v, max u v w, r} (R.over V) ⟶ M) :
    liftedUnitHomTerminalEquiv Over.mkIdTerminal (R.over U)
      ((SheafOfModules.overMap R f).obj M)
      ((SheafOfModules.overMapLiftedUnitIso.{u, v, r, max u v w} R f).inv ≫
        (SheafOfModules.overMap R f).map a) =
    M.val.map (Over.mkIdTerminal.from ((Over.map f).obj (Over.mk (𝟙 U)))).op
      (liftedUnitHomTerminalEquiv Over.mkIdTerminal (R.over V) M a) := by
  change a.val.app (op ((Over.map f).obj (Over.mk (𝟙 U)))) (ULift.up 1) =
    M.val.map (Over.mkIdTerminal.from ((Over.map f).obj (Over.mk (𝟙 U)))).op
      (a.val.app (op (Over.mk (𝟙 V))) (ULift.up 1))
  rw [← PresheafOfModules.naturality_apply]
  congr 1
  change ULift.up (1 : (R.over V).obj.obj _) =
    ULift.up ((R.over V).obj.map
      (Over.mkIdTerminal.from ((Over.map f).obj (Over.mk (𝟙 U)))).op 1)
  rw [map_one]

/-- The actual resolution-comparison restriction on native derived terminal sections. -/
def derivedOverMapRestriction (M : SheafOfModules.{max u v r w} (R.over V)) (n : ℕ) :
    ((SheafOfModules.evaluation (R.over V) (op (Over.mk (𝟙 V)))).rightDerived n).obj M →+
      ((SheafOfModules.evaluation (R.over U) (op (Over.mk (𝟙 U)))).rightDerived n).obj
        ((SheafOfModules.overMap R f).obj M) :=
  ((derivedTerminalSectionsIso.{max u v, v, r, w} Over.mkIdTerminal (R.over V) n).hom.app M ≫
    representedRightDerivedRestriction (SheafOfModules.overMap R f)
      (SheafOfModules.overMapLiftedUnitIso.{u, v, r, max u v w} R f).inv n ≫
    (derivedTerminalSectionsIso.{max u v, v, r, w} Over.mkIdTerminal (R.over U) n).inv.app
      ((SheafOfModules.overMap R f).obj M)).hom

variable [HasExt.{e₁} (SheafOfModules.{max u v r w} (R.over V))]
  [HasExt.{e₂} (SheafOfModules.{max u v r w} (R.over U))]

omit [HasBinaryProducts C] in
/-- The genuine resolution restriction agrees with the original Ext restriction
under the canonical normalization of native derived terminal sections. -/
theorem derivedOverMapRestriction_ext (M : SheafOfModules.{max u v r w} (R.over V))
    (n : ℕ)
    (x : ((SheafOfModules.evaluation (R.over V) (op (Over.mk (𝟙 V)))).rightDerived n).obj M) :
    derivedTerminalSectionsExtAddEquiv.{max u v, v, r, w, e₂} Over.mkIdTerminal (R.over U)
      ((SheafOfModules.overMap R f).obj M) n (derivedOverMapRestriction.{u, v, r, w} R f M n x) =
      overMapCohomologyRestriction.{u, v, r, max u v w, e₁, e₂} R f M n
        (derivedTerminalSectionsExtAddEquiv.{max u v, v, r, w, e₁} Over.mkIdTerminal
          (R.over V) M n x) := by
  apply (extRightDerivedRepresentedAddEquiv _ _ n).injective
  have h := representedRightDerivedRestriction_ext (SheafOfModules.overMap R f)
    (SheafOfModules.overMapLiftedUnitIso.{u, v, r, max u v w} R f).inv n
    (derivedTerminalSectionsExtAddEquiv.{max u v, v, r, w, e₁} Over.mkIdTerminal (R.over V) M n x)
  simp only [derivedTerminalSectionsExtAddEquiv, representedDerivedModuleAddEquiv,
    overMapCohomologyRestriction,
    AddEquiv.trans_apply,
    AddEquiv.apply_symm_apply] at h ⊢
  rw [← h]
  exact ConcreteCategory.congr_hom
    ((derivedTerminalSectionsIso.{max u v, v, r, w} Over.mkIdTerminal (R.over U)
      n).inv_hom_id_app _)
      (representedRightDerivedRestriction (SheafOfModules.overMap R f)
        (SheafOfModules.overMapLiftedUnitIso.{u, v, r, max u v w} R f).inv n
        ((derivedTerminalSectionsIso.{max u v, v, r, w} Over.mkIdTerminal (R.over V)
          n).hom.app M x))

universe e₃ e₄

variable [(J.over U).HasSheafCompose (forget AddCommGrpCat.{max u v r w})]
  [(J.over V).HasSheafCompose (forget AddCommGrpCat.{max u v r w})]
  [HasExt.{e₃} (Sheaf (J.over V) AddCommGrpCat.{max u v r w})]
  [HasExt.{e₄} (Sheaf (J.over U) AddCommGrpCat.{max u v r w})]

omit [HasBinaryProducts C] in
/-- The canonical native-derived-sections to abelian-cohomology map commutes
with genuine resolution restriction and original abelian slice restriction. -/
theorem derivedOverMapRestriction_cohomologyMap
    (M : SheafOfModules.{max u v r w} (R.over V)) (n : ℕ)
    (x : ((SheafOfModules.evaluation (R.over V) (op (Over.mk (𝟙 V)))).rightDerived n).obj M) :
    cohomologyMap.{max u v, v, r, max u v w, e₂, e₄} Over.mkIdTerminal (R.over U)
      ((SheafOfModules.overMap R f).obj M) n
      (derivedTerminalSectionsExtAddEquiv.{max u v, v, r, w, e₂} Over.mkIdTerminal (R.over U)
        ((SheafOfModules.overMap R f).obj M) n (derivedOverMapRestriction.{u, v, r, w} R f M n x)) =
    overMapAbCohomologyRestriction f ((SheafOfModules.toSheaf (R.over V)).obj M) n
      (cohomologyMap.{max u v, v, r, max u v w, e₁, e₃} Over.mkIdTerminal (R.over V) M n
        (derivedTerminalSectionsExtAddEquiv.{max u v, v, r, w, e₁} Over.mkIdTerminal
          (R.over V) M n x)) := by
  rw [derivedOverMapRestriction_ext, cohomologyMap_overMap]

end CategoryTheory.Sheaf.ModuleCoefficients
