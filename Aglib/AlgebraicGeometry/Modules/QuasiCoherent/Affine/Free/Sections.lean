/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Free

/-!
# Original sections under the affine tilde/basis isomorphism

The native tilde/Finsupp coproduct comparison preserves the original
summand inclusions. Consequently the existing `tildeBasisIso`, with its
original unchanged map, sends every original localized basis vector to
the native free section, and its inverse recovers that same vector.
The coefficient ring and index type retain their original native universe;
no finite, field, Noetherian, or nontrivial premise is added.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
universe u
variable {R : CommRingCat.{u}} {I : Type u}

/-- The native tilde/Finsupp comparison preserves the original summand inclusions. -/
theorem tildeFinsupp_hom_ιFree (i : I) :
    tilde.map (ModuleCat.ofHom (Finsupp.lsingle i : R →ₗ[R] (I →₀ R))) ≫
      (tildeFinsupp I).hom = SheafOfModules.ιFree i := by
  let H : IsColimit ((tilde.functor R).mapCocone (ModuleCat.finsuppCocone R R I)) :=
    isColimitOfPreserves (tilde.functor R) (ModuleCat.finsuppCoconeIsColimit R R I)
  let e : (Discrete.functor fun (_ : I) => ModuleCat.of R R) ⋙ tilde.functor R ≅
      Discrete.functor fun _ => SheafOfModules.unit (Spec R).ringCatSheaf :=
    Discrete.natIso fun _ => tildeSelf
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom
    ((IsColimit.precomposeHomEquiv e.symm _).symm H) (coproductIsCoproduct _) (Discrete.mk i)
  change (𝟙 (tilde (ModuleCat.of R R))) ≫
    tilde.map (ModuleCat.ofHom (Finsupp.lsingle i : R →ₗ[R] (I →₀ R))) ≫
      (tildeFinsupp I).hom = SheafOfModules.ιFree i at h
  simpa only [Category.id_comp] using h

/-- The original section of one in the tilde of the coefficient ring is the original unit. -/
theorem tilde_toOpen_self_one (U : (Spec R).Opens) :
    tilde.toOpen (ModuleCat.of R R) U (1 : R) = (1 : Γ(Spec R, U)) := by
  change StructureSheaf.const (1 : R) (1 : R) U (by simp) = 1
  exact StructureSheaf.const_one U


/-- The original basis-point inclusion maps to the corresponding native free summand. -/
theorem tildeBasisIso_hom_basisPoint (M : ModuleCat.{u} R) (b : Module.Basis I R M) (i : I) :
    tilde.map (ModuleCat.ofHom (LinearMap.toSpanSingleton R M (b i))) ≫
      (tildeBasisIso M b).hom = SheafOfModules.ιFree i := by
  change tilde.map (ModuleCat.ofHom (LinearMap.toSpanSingleton R M (b i))) ≫
    tilde.map (ModuleCat.ofHom b.repr.toLinearMap) ≫ (tildeFinsupp I).hom = _
  rw [← tilde.map_comp_assoc]
  have h : ModuleCat.ofHom (LinearMap.toSpanSingleton R M (b i)) ≫
      ModuleCat.ofHom b.repr.toLinearMap =
        ModuleCat.ofHom (Finsupp.lsingle i : R →ₗ[R] (I →₀ R)) := by
    ext r
    simp
  rw [h]
  exact tildeFinsupp_hom_ιFree i

/-- The original tilde/basis comparison sends a localized basis vector to the free section. -/
theorem tildeBasisIso_hom_toOpen (M : ModuleCat.{u} R) (b : Module.Basis I R M)
    (i : I) (U : (Spec R).Opens) :
    (tildeBasisIso M b).hom.val.app (op U) (tilde.toOpen M U (b i)) =
      (SheafOfModules.freeSection (R := (Spec R).ringCatSheaf) i).val (op U) := by
  let p : ModuleCat.of R R ⟶ M := ModuleCat.ofHom (LinearMap.toSpanSingleton R M (b i))
  have hp : (tilde.map p).val.app (op U) (1 : Γ(Spec R, U)) =
      tilde.toOpen M U (b i) := by
    have h := ConcreteCategory.congr_hom (tilde.toOpen_map_app p U) (1 : R)
    change (tilde.map p).val.app (op U) (tilde.toOpen (ModuleCat.of R R) U 1) =
      tilde.toOpen M U (p 1) at h
    have hone : tilde.toOpen (ModuleCat.of R R) U (1 : R) = (1 : Γ(Spec R, U)) :=
      tilde_toOpen_self_one U
    rw [hone] at h
    simpa [p] using h
  have h := congrArg (fun k => k.val.app (op U) (1 : Γ(Spec R, U)))
    (tildeBasisIso_hom_basisPoint M b i)
  change (tildeBasisIso M b).hom.val.app (op U)
    ((tilde.map p).val.app (op U) (1 : Γ(Spec R, U))) =
      (SheafOfModules.freeSection (R := (Spec R).ringCatSheaf) i).val (op U) at h
  exact (congrArg ((tildeBasisIso M b).hom.val.app (op U)) hp).symm.trans h

/-- The inverse original tilde/basis comparison recovers that same localized basis vector. -/
theorem tildeBasisIso_inv_freeSection (M : ModuleCat.{u} R) (b : Module.Basis I R M)
    (i : I) (U : (Spec R).Opens) :
    (tildeBasisIso M b).inv.val.app (op U)
      ((SheafOfModules.freeSection (R := (Spec R).ringCatSheaf) i).val (op U)) =
        tilde.toOpen M U (b i) :=
  (congrArg ((tildeBasisIso M b).inv.val.app (op U))
    (tildeBasisIso_hom_toOpen M b i U).symm).trans
    (congrArg (fun k => k.val.app (op U) (tilde.toOpen M U (b i)))
      (tildeBasisIso M b).hom_inv_id)

end AlgebraicGeometry.Scheme.Modules
