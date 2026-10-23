/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.DerivedSlice
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.DerivedScalarSections

/-!
# Native coefficient-valued derived sections on slices

The target coefficient action is the original scalar action followed by the
ring restriction map. Exact scalar restriction and the genuine resolution
comparison induce an additive map on native coefficient-valued derived
sections. No alternative cohomology groups or arbitrary coefficient action
are introduced.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe u v r w s e₁ e₂ e₃ e₄

namespace CategoryTheory.Sheaf.ModuleCoefficients

/-- Transport a genuine additive restriction through exact scalar-comparison isomorphisms. -/
def scalarRestrictionFactory
    {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
    {B₁ B₂ Λ : Type*} [Ring B₁] [Ring B₂] [Ring Λ]
    (F₁ : C₁ ⥤ ModuleCat.{w} B₁) (G₁ : C₁ ⥤ ModuleCat.{w} Λ)
    (F₂ : C₂ ⥤ ModuleCat.{w} B₂) (G₂ : C₂ ⥤ ModuleCat.{w} Λ)
    (α₁ : Λ →+* B₁) (α₂ : Λ →+* B₂)
    (β₁ : G₁ ≅ F₁ ⋙ ModuleCat.restrictScalars α₁)
    (β₂ : G₂ ≅ F₂ ⋙ ModuleCat.restrictScalars α₂)
    (M : C₁) (N : C₂) (r : F₁.obj M →+ F₂.obj N) : G₁.obj M →+ G₂.obj N :=
  let a := (((forget₂ (ModuleCat Λ) AddCommGrpCat).mapIso
    (β₁.app M)).addCommGroupIsoToAddEquiv)
  let b := (((forget₂ (ModuleCat Λ) AddCommGrpCat).mapIso
    (β₂.app N)).addCommGroupIsoToAddEquiv)
  b.symm.toAddMonoidHom.comp (r.comp a.toAddMonoidHom)

private theorem scalarRestrictionFactory_square
    {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
    {B₁ B₂ Λ : Type*} [Ring B₁] [Ring B₂] [Ring Λ]
    (F₁ : C₁ ⥤ ModuleCat.{w} B₁) (G₁ : C₁ ⥤ ModuleCat.{w} Λ)
    (F₂ : C₂ ⥤ ModuleCat.{w} B₂) (G₂ : C₂ ⥤ ModuleCat.{w} Λ)
    (α₁ : Λ →+* B₁) (α₂ : Λ →+* B₂)
    (β₁ : G₁ ≅ F₁ ⋙ ModuleCat.restrictScalars α₁)
    (β₂ : G₂ ≅ F₂ ⋙ ModuleCat.restrictScalars α₂)
    (M : C₁) (N : C₂) (r : F₁.obj M →+ F₂.obj N)
    {Z₁ Z₂ : Type*} [AddCommGroup Z₁] [AddCommGroup Z₂]
    (e₁ : F₁.obj M ≃+ Z₁) (e₂ : F₂.obj N ≃+ Z₂) (q : Z₁ →+ Z₂)
    (h : ∀ x, e₂ (r x) = q (e₁ x)) (x : G₁.obj M) :
    scalarDerivedModuleAddEquiv F₂ G₂ α₂ β₂ N e₂
        (scalarRestrictionFactory F₁ G₁ F₂ G₂ α₁ α₂ β₁ β₂ M N r x) =
      q (scalarDerivedModuleAddEquiv F₁ G₁ α₁ β₁ M e₁ x) := by
  let a := (((forget₂ (ModuleCat Λ) AddCommGrpCat).mapIso
    (β₁.app M)).addCommGroupIsoToAddEquiv)
  let b := (((forget₂ (ModuleCat Λ) AddCommGrpCat).mapIso
    (β₂.app N)).addCommGroupIsoToAddEquiv)
  change e₂ (b (b.symm (r (a x)))) = q (e₁ (a x))
  exact (congrArg e₂ (b.apply_symm_apply (r (a x)))).trans (h (a x))

private theorem scalarRestrictionFactory_square_of_eq
    {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
    {B₁ B₂ Λ : Type*} [Ring B₁] [Ring B₂] [Ring Λ]
    (F₁ : C₁ ⥤ ModuleCat.{w} B₁) (G₁ : C₁ ⥤ ModuleCat.{w} Λ)
    (F₂ : C₂ ⥤ ModuleCat.{w} B₂) (G₂ : C₂ ⥤ ModuleCat.{w} Λ)
    (α₁ : Λ →+* B₁) (α₂ : Λ →+* B₂)
    (β₁ : G₁ ≅ F₁ ⋙ ModuleCat.restrictScalars α₁)
    (β₂ : G₂ ≅ F₂ ⋙ ModuleCat.restrictScalars α₂)
    (M : C₁) (N : C₂) (r : F₁.obj M →+ F₂.obj N)
    {Z₁ Z₂ : Type*} [AddCommGroup Z₁] [AddCommGroup Z₂]
    (e₁ : F₁.obj M ≃+ Z₁) (e₂ : F₂.obj N ≃+ Z₂) (q : Z₁ →+ Z₂)
    (h : ∀ x, e₂ (r x) = q (e₁ x)) (x : G₁.obj M)
    (E : G₂.obj N ≃+ Z₂)
    (hE : E = scalarDerivedModuleAddEquiv F₂ G₂ α₂ β₂ N e₂)
    (y : G₂.obj N)
    (hy : y = scalarRestrictionFactory F₁ G₁ F₂ G₂ α₁ α₂ β₁ β₂ M N r x)
    (z : Z₂)
    (hz : z = q (scalarDerivedModuleAddEquiv F₁ G₁ α₁ β₁ M e₁ x)) :
    E y = z := by
  rw [hE, hy, hz]
  exact scalarRestrictionFactory_square F₁ G₁ F₂ G₂ α₁ α₂ β₁ β₂ M N r e₁ e₂ q h x

section Actions

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {T : C} (hT : IsTerminal T) (R : Sheaf J RingCat.{r})
  (Λ : Type s) [Ring Λ] (α : Λ →+* R.obj.obj (op T))

/-- Restrict a global coefficient action by the original sheaf restriction. -/
def sliceScalarAction (U : C) : Λ →+* (R.over U).obj.obj (op (Over.mk (𝟙 U))) :=
  (R.obj.map (hT.from U).op).hom.comp α

/-- The original scalar actions on slices satisfy literal restriction coherence. -/
theorem sliceScalarAction_comp {U V : C} (f : U ⟶ V) :
    (R.obj.map f.op).hom.comp (sliceScalarAction hT R Λ α V) =
      sliceScalarAction hT R Λ α U := by
  have h : f ≫ hT.from V = hT.from U := hT.hom_ext _ _
  ext a
  change R.obj.map f.op (R.obj.map (hT.from V).op (α a)) =
    R.obj.map (hT.from U).op (α a)
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, h]

end Actions

/-- Original restriction of the coefficient action, with its native slice terminal type. -/
def overMapScalarAction {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{r}) {U V : C} (f : U ⟶ V) (Λ : Type s) [Ring Λ]
    (α : Λ →+* (R.over V).obj.obj (op (Over.mk (𝟙 V)))) :
    Λ →+* (R.over U).obj.obj (op (Over.mk (𝟙 U))) :=
  (R.obj.map f.op).hom.comp α

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasBinaryProducts C] [HasPullbacks C]
  (R : Sheaf J RingCat.{r}) {U V : C} (f : U ⟶ V)
  [HasSheafify (J.over U) AddCommGrpCat.{max u v r w}]
  [HasSheafify (J.over V) AddCommGrpCat.{max u v r w}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v r w}]
  [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v r w}]
  [EnoughInjectives (SheafOfModules.{max u v r w} (R.over U))]
  [EnoughInjectives (SheafOfModules.{max u v r w} (R.over V))]
  (Λ : Type s) [Ring Λ] (α : Λ →+* (R.over V).obj.obj (op (Over.mk (𝟙 V))))

/-- Coefficient-valued native restriction uses the same actual resolution map,
with the target action obtained by original ring restriction. -/
def derivedScalarOverMapRestriction (M : SheafOfModules.{max u v r w} (R.over V)) (n : ℕ) :
    ((scalarTerminalSections.{max u v, v, r, w, s} (T := Over.mk (𝟙 V)) (R.over V) Λ
      α).rightDerived n).obj M →+
      ((scalarTerminalSections.{max u v, v, r, w, s} (T := Over.mk (𝟙 U)) (R.over U) Λ
        (overMapScalarAction R f Λ α)).rightDerived n).obj
        ((SheafOfModules.overMap R f).obj M) :=
  scalarRestrictionFactory
    ((SheafOfModules.evaluation.{max u v r w} (R.over V)
      (op (Over.mk (𝟙 V)))).rightDerived n)
    ((scalarTerminalSections.{max u v, v, r, w, s} (T := Over.mk (𝟙 V))
      (R.over V) Λ α).rightDerived n)
    ((SheafOfModules.evaluation.{max u v r w} (R.over U)
      (op (Over.mk (𝟙 U)))).rightDerived n)
    ((scalarTerminalSections.{max u v, v, r, w, s} (T := Over.mk (𝟙 U))
      (R.over U) Λ (overMapScalarAction R f Λ α)).rightDerived n)
    α (overMapScalarAction R f Λ α)
    (derivedScalarTerminalSectionsIso.{max u v, v, r, w, s}
      (T := Over.mk (𝟙 V)) (R.over V) Λ α n)
    (derivedScalarTerminalSectionsIso.{max u v, v, r, w, s}
      (T := Over.mk (𝟙 U)) (R.over U) Λ (overMapScalarAction R f Λ α) n)
    M ((SheafOfModules.overMap R f).obj M)
    (derivedOverMapRestriction.{u, v, r, w} R f M n)

variable [HasExt.{e₁} (SheafOfModules.{max u v r w} (R.over V))]
  [HasExt.{e₂} (SheafOfModules.{max u v r w} (R.over U))]

omit [HasBinaryProducts C] in
/-- Canonical coefficient-valued derived normalization respects actual Ext restriction. -/
theorem derivedScalarOverMapRestriction_ext
    (M : SheafOfModules.{max u v r w} (R.over V)) (n : ℕ)
    (x : ((scalarTerminalSections.{max u v, v, r, w, s} (T := Over.mk (𝟙 V)) (R.over V)
      Λ α).rightDerived n).obj M) :
    derivedScalarTerminalSectionsExtAddEquiv.{max u v, v, r, w, e₂, s}
      Over.mkIdTerminal (R.over U) Λ
      (overMapScalarAction R f Λ α) ((SheafOfModules.overMap R f).obj M) n
        (derivedScalarOverMapRestriction.{u, v, r, w, s} R f Λ α M n x) =
    overMapCohomologyRestriction.{u, v, r, max u v w, e₁, e₂} R f M n
      (derivedScalarTerminalSectionsExtAddEquiv.{max u v, v, r, w, e₁, s}
        Over.mkIdTerminal (R.over V) Λ α M n x) := by
  exact scalarRestrictionFactory_square_of_eq
    ((SheafOfModules.evaluation.{max u v r w} (R.over V)
      (op (Over.mk (𝟙 V)))).rightDerived n)
    ((scalarTerminalSections.{max u v, v, r, w, s} (T := Over.mk (𝟙 V))
      (R.over V) Λ α).rightDerived n)
    ((SheafOfModules.evaluation.{max u v r w} (R.over U)
      (op (Over.mk (𝟙 U)))).rightDerived n)
    ((scalarTerminalSections.{max u v, v, r, w, s} (T := Over.mk (𝟙 U))
      (R.over U) Λ (overMapScalarAction R f Λ α)).rightDerived n)
    α (overMapScalarAction R f Λ α)
    (derivedScalarTerminalSectionsIso.{max u v, v, r, w, s}
      (T := Over.mk (𝟙 V)) (R.over V) Λ α n)
    (derivedScalarTerminalSectionsIso.{max u v, v, r, w, s}
      (T := Over.mk (𝟙 U)) (R.over U) Λ (overMapScalarAction R f Λ α) n)
    M ((SheafOfModules.overMap R f).obj M)
    (derivedOverMapRestriction.{u, v, r, w} R f M n)
    (derivedTerminalSectionsExtAddEquiv.{max u v, v, r, w, e₁}
      Over.mkIdTerminal (R.over V) M n)
    (derivedTerminalSectionsExtAddEquiv.{max u v, v, r, w, e₂}
      Over.mkIdTerminal (R.over U) ((SheafOfModules.overMap R f).obj M) n)
    (overMapCohomologyRestriction.{u, v, r, max u v w, e₁, e₂} R f M n)
    (derivedOverMapRestriction_ext.{u, v, r, w, e₁, e₂} R f M n) x
    (derivedScalarTerminalSectionsExtAddEquiv.{max u v, v, r, w, e₂, s}
      Over.mkIdTerminal (R.over U) Λ (overMapScalarAction R f Λ α)
      ((SheafOfModules.overMap R f).obj M) n) rfl
    (derivedScalarOverMapRestriction.{u, v, r, w, s} R f Λ α M n x) rfl
    (overMapCohomologyRestriction.{u, v, r, max u v w, e₁, e₂} R f M n
      (derivedScalarTerminalSectionsExtAddEquiv.{max u v, v, r, w, e₁, s}
        Over.mkIdTerminal (R.over V) Λ α M n x)) rfl

variable [(J.over U).HasSheafCompose (forget AddCommGrpCat.{max u v r w})]
  [(J.over V).HasSheafCompose (forget AddCommGrpCat.{max u v r w})]
  [HasExt.{e₃} (Sheaf (J.over V) AddCommGrpCat.{max u v r w})]
  [HasExt.{e₄} (Sheaf (J.over U) AddCommGrpCat.{max u v r w})]

omit [HasBinaryProducts C] in
/-- The canonical native coefficient-valued comparison commutes with original
abelian restriction, using the canonically restricted coefficient action. -/
theorem derivedScalarOverMapRestriction_cohomologyMap
    (M : SheafOfModules.{max u v r w} (R.over V)) (n : ℕ)
    (x : ((scalarTerminalSections.{max u v, v, r, w, s} (T := Over.mk (𝟙 V)) (R.over V)
      Λ α).rightDerived n).obj M) :
    cohomologyMap.{max u v, v, r, max u v w, e₂, e₄} Over.mkIdTerminal (R.over U)
      ((SheafOfModules.overMap R f).obj M) n
      (derivedScalarTerminalSectionsExtAddEquiv.{max u v, v, r, w, e₂, s}
        Over.mkIdTerminal (R.over U) Λ
        (overMapScalarAction R f Λ α) ((SheafOfModules.overMap R f).obj M) n
          (derivedScalarOverMapRestriction.{u, v, r, w, s} R f Λ α M n x)) =
    overMapAbCohomologyRestriction f ((SheafOfModules.toSheaf (R.over V)).obj M) n
      (cohomologyMap.{max u v, v, r, max u v w, e₁, e₃} Over.mkIdTerminal (R.over V) M n
        (derivedScalarTerminalSectionsExtAddEquiv.{max u v, v, r, w, e₁, s}
          Over.mkIdTerminal (R.over V) Λ α M n x)) := by
  rw [derivedScalarOverMapRestriction_ext, cohomologyMap_overMap]

end CategoryTheory.Sheaf.ModuleCoefficients
