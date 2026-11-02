/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.SectionStalk
public import Aglib.AlgebraicGeometry.Modules.Pullback.StalkUnit

/-!
# The original pullback unit under point equality transport

This is the original germ law, extracted once from proper formal functions.
It uses arbitrary schemes, morphisms and module sheaves, with no geometric
or quasicoherence hypotheses.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite IsLocalRing

universe u v w

namespace AlgebraicGeometry.Scheme.Modules

private theorem scalarExtensionIso_mpr_unit
    {R S : Type u} [CommRing R] [CommRing S]
    {C : Type v} [Category.{w} C]
    (F : C ⥤ ModuleCat.{u} S) (G : C ⥤ ModuleCat.{u} R)
    (σ τ : R →+* S) (hστ : σ = τ) (E : F ≅ G ⋙ ModuleCat.extendScalars σ)
    (hTypes : (F ≅ G ⋙ ModuleCat.extendScalars τ) =
      (F ≅ G ⋙ ModuleCat.extendScalars σ))
    (M : C) (m : F.obj M) (n : G.obj M)
    (hE : E.hom.app M m = (ModuleCat.extendRestrictScalarsAdj σ).unit.app (G.obj M) n) :
    (Eq.mpr hTypes E).hom.app M m =
      (ModuleCat.extendRestrictScalarsAdj τ).unit.app (G.obj M) n := by
  subst τ
  have hh : hTypes = rfl := Subsingleton.elim _ _
  rw [hh]
  exact hE

/-- The original pullback-stalk unit formula survives actual point equality transport. -/
theorem pullbackModuleStalkAtEqIso_unit_germ
    {X Y : Scheme.{u}} (p : X ⟶ Y) (x : X) (y : Y) (hpx : p x = y)
    (M : Y.Modules) (U : Y.Opens) (hy : y ∈ U) (m : Γ(M, U)) :
    (pullbackModuleStalkAtEqIso p x y hpx).hom.app M
      (((Scheme.Modules.pullback p).obj M).presheaf.germ (p ⁻¹ᵁ U) x
        (by change p x ∈ U; simpa only [hpx] using hy)
        (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M).app U m)) =
      (ModuleCat.extendRestrictScalarsAdj
        (((Y.presheaf.stalkCongr (.of_eq hpx)).inv ≫ p.stalkMap x).hom)).unit.app
          ((moduleStalk Y y).obj M) (M.presheaf.germ U y hy m) := by
  subst y
  let F := Scheme.Modules.pullback p ⋙ moduleStalk X x
  let G := moduleStalk Y (p x)
  let σ := (p.stalkMap x).hom
  let τ := ((Y.presheaf.stalkCongr (.of_eq (rfl : p x = p x))).inv ≫ p.stalkMap x).hom
  have hστ : σ = τ := by
    dsimp only [σ, τ]
    congr 1
    simp only [TopCat.Presheaf.stalkCongr, TopCat.Presheaf.stalkSpecializes_refl,
      Category.id_comp]
  let hTypes := congrArg (fun ρ => F ≅ G ⋙ ModuleCat.extendScalars ρ) hστ.symm
  have hE : (pullbackModuleStalkIso p x).hom.app M
      (((Scheme.Modules.pullback p).obj M).presheaf.germ (p ⁻¹ᵁ U) x hy
        (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M).app U m)) =
      (ModuleCat.extendRestrictScalarsAdj σ).unit.app (G.obj M)
        (M.presheaf.germ U (p x) hy m) := by
    simpa only [ModuleCat.extendRestrictScalarsAdj_unit_app_apply] using
      pullbackModuleStalkIso_unit_germ p x M U hy m
  dsimp only [pullbackModuleStalkAtEqIso]
  exact scalarExtensionIso_mpr_unit F G σ τ hστ (pullbackModuleStalkIso p x)
    hTypes M _ _ hE

end AlgebraicGeometry.Scheme.Modules
