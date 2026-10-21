/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Proper.FibreFormalFunctions
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.DegreeZero
public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion.CartesianSections
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Stalk
public import Mathlib.Algebra.Category.Ring.FilteredColimits

/-!
# Proper fibre idempotents in the image of the original ordinary stalk

The native local-spectrum comparison retains the original pullback unit and
neighborhood germs. The actual ordinary Cartesian mate identifies the original
pushforward ring stalk with local-spectrum global functions. The canonical
local-fibre comparison then turns the affine formal-functions image theorem
into the image theorem for the original ordinary stalk-to-fibre arrow.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Scheme.Cohomology.ProperFibreFormalFunctions

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y)

/-- The canonical additive forgetful functor factors through ordinary rings. -/
abbrev ringAdditiveFunctor : CommRingCat.{u} ⥤ AddCommGrpCat.{u} :=
  forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u}

/-- Forgetting ring operations preserves the actual filtered neighborhood colimit. -/
def pushforwardStructureStalkAddIso :
    ringAdditiveFunctor.obj ((f.base _* X.presheaf).stalk y) ≅
      (forget₂ (ModuleCat (Y.presheaf.stalk y)) AddCommGrpCat.{u}).obj
        ((moduleStalk Y y).obj ((Scheme.Modules.pushforward f).obj
          (SheafOfModules.unit X.ringCatSheaf))) := by
  let : PreservesFilteredColimits ringAdditiveFunctor :=
    comp_preservesFilteredColimits (forget₂ CommRingCat RingCat)
      (forget₂ RingCat AddCommGrpCat.{u})
  exact preservesColimitIso ringAdditiveFunctor
    ((OpenNhds.inclusion y).op ⋙ (f.base _* X.presheaf))

/-- The comparison carries each original ring germ to the same additive module germ. -/
theorem pushforwardStructureStalkAddIso_germ
    (U : Y.Opens) (hy : y ∈ U) (s : Γ(X, f ⁻¹ᵁ U)) :
    (pushforwardStructureStalkAddIso f y).hom ((f.base _* X.presheaf).germ U y hy s) =
      (((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)).presheaf.germ
        U y hy s) := by
  let : PreservesFilteredColimits ringAdditiveFunctor :=
    comp_preservesFilteredColimits (forget₂ CommRingCat RingCat)
      (forget₂ RingCat AddCommGrpCat.{u})
  exact ConcreteCategory.congr_hom
    (ι_preservesColimitIso_hom ringAdditiveFunctor
      ((OpenNhds.inclusion y).op ⋙ (f.base _* X.presheaf)) (op ⟨U, hy⟩)) s

/-- The actual ordinary stalk identifies with local-spectrum degree-zero cohomology,
using the original right-derived-zero map and native localization equivalence. -/
def ordinaryStalkLocalH0Equiv [QuasiCompact f] [QuasiSeparated f] :
    let a := Limits.pullback.fst f (Y.fromSpecStalk y)
    let N := (Scheme.Modules.pullback a).obj (SheafOfModules.unit X.ringCatSheaf)
    (f.base _* X.presheaf).stalk y ≃+
      Sheaf.H.{u + 1} (moduleAddSheaf _ N) 0 := by
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let : O.IsQuasicoherent := quasicoherent_of_affineCharts O
    (fun R j _ => (affineLocallyFiniteType_unit X R j).1)
  let a := Limits.pullback.fst f (Y.fromSpecStalk y)
  let b := Limits.pullback.snd f (Y.fromSpecStalk y)
  let N := (Scheme.Modules.pullback a).obj O
  let α := b.appTop.hom.comp (Scheme.ΓSpecIso (Y.presheaf.stalk y)).inv.hom
  letI := moduleCohomologyModuleOfHom _ α N 0
  let e₀ := (pushforwardStructureStalkAddIso f y).addCommGroupIsoToAddEquiv
  let e₁ := ((moduleStalk Y y).mapIso
    (asIso ((Scheme.Modules.pushforward f).toRightDerivedZero.app O))).toLinearEquiv.toAddEquiv
  let e₂ := (moduleHigherDirectImageStalkLinearEquiv f O y 0).toAddEquiv
  exact e₀.trans (e₁.trans e₂)

end AlgebraicGeometry.Scheme.Cohomology.ProperFibreFormalFunctions

namespace AlgebraicGeometry.Scheme.Cohomology.ProperFibreFormalFunctions

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite IsLocalRing
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
universe u

universe v w

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

private theorem scalarExtensionIso_mp_unit
    {R S : Type u} [CommRing R] [CommRing S]
    {C : Type v} [Category.{w} C]
    (F : C ⥤ ModuleCat.{u} S) (G : C ⥤ ModuleCat.{u} R)
    (σ τ : R →+* S) (hστ : σ = τ) (E : F ≅ G ⋙ ModuleCat.extendScalars σ)
    (hTypes : (F ≅ G ⋙ ModuleCat.extendScalars σ) =
      (F ≅ G ⋙ ModuleCat.extendScalars τ))
    (M : C) (m : F.obj M) (n : G.obj M)
    (hE : E.hom.app M m = (ModuleCat.extendRestrictScalarsAdj σ).unit.app (G.obj M) n) :
    (Eq.mp hTypes E).hom.app M m =
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

/-- At the original local-spectrum closed point, the same unit gives the normalized scalar unit. -/
theorem fromSpecStalkPullbackStalkIso_unit_germ
    (Y : Scheme.{u}) (y : Y) (M : Y.Modules)
    (U : Y.Opens) (hy : y ∈ U) (m : Γ(M, U)) :
    (fromSpecStalkPullbackStalkIso Y y).hom.app M
      (((Scheme.Modules.pullback (Y.fromSpecStalk y)).obj M).presheaf.germ
        ((Y.fromSpecStalk y) ⁻¹ᵁ U) (closedPoint (Y.presheaf.stalk y))
        (by
          change Y.fromSpecStalk y (closedPoint (Y.presheaf.stalk y)) ∈ U
          simpa only [Scheme.fromSpecStalk_closedPoint] using hy)
        (((Scheme.Modules.pullbackPushforwardAdjunction
          (Y.fromSpecStalk y)).unit.app M).app U m)) =
      (ModuleCat.extendRestrictScalarsAdj
        (stalkClosedPointIso (Y.presheaf.stalk y)).inv.hom).unit.app
          ((moduleStalk Y y).obj M) (M.presheaf.germ U y hy m) := by
  let j := Y.fromSpecStalk y
  let x := closedPoint (Y.presheaf.stalk y)
  let hx := Scheme.fromSpecStalk_closedPoint (x := y)
  let F := Scheme.Modules.pullback j ⋙ moduleStalk (Spec (Y.presheaf.stalk y)) x
  let G := moduleStalk Y y
  let σ := ((Y.presheaf.stalkCongr (.of_eq hx)).inv ≫ j.stalkMap x).hom
  let τ := (stalkClosedPointIso (Y.presheaf.stalk y)).inv.hom
  have hστ : σ = τ := congrArg CommRingCat.Hom.hom
    (fromSpecStalk_normalized_stalkMap Y y)
  let hTypes := congrArg (fun ρ => F ≅ G ⋙ ModuleCat.extendScalars ρ) hστ
  have hE := pullbackModuleStalkAtEqIso_unit_germ j x y hx M U hy m
  dsimp only [fromSpecStalkPullbackStalkIso]
  exact scalarExtensionIso_mp_unit F G σ τ hστ
    (pullbackModuleStalkAtEqIso j x y hx) hTypes M _ _ hE

/-- The original local-section isomorphism cancels to the original scalar-extension unit. -/
theorem stalkFromSpecStalkSectionsIso_cancel
    (Y : Scheme.{u}) (y : Y) (M : Y.Modules) :
    (stalkFromSpecStalkSectionsIso Y y M).hom ≫
      (localSpectrumSectionsStalkIso (Y.presheaf.stalk y)
        ((Scheme.Modules.pullback (Y.fromSpecStalk y)).obj M)).hom ≫
      (ModuleCat.restrictScalars (stalkClosedPointIso (Y.presheaf.stalk y)).inv.hom).map
        ((fromSpecStalkPullbackStalkIso Y y).hom.app M) =
      (ModuleCat.extendRestrictScalarsAdj
        (stalkClosedPointIso (Y.presheaf.stalk y)).inv.hom).unit.app
          ((moduleStalk Y y).obj M) := by
  rw [stalkFromSpecStalkSectionsIso_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp,
    Iso.app_inv, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- The native stalk/local-sections comparison sends each actual germ to its actual
pulled-back neighborhood section restricted to the whole local spectrum. -/
theorem stalkFromSpecStalkSectionsIso_germ
    (Y : Scheme.{u}) (y : Y) (M : Y.Modules)
    (U : Y.Opens) (hy : y ∈ U) (m : Γ(M, U)) :
    (stalkFromSpecStalkSectionsIso Y y M).hom (M.presheaf.germ U y hy m) =
      ((Scheme.Modules.pullback (Y.fromSpecStalk y)).obj M).presheaf.map
        (homOfLE (ProperFibreIdempotents.stalkRestriction_le y U hy)).op
        (((Scheme.Modules.pullbackPushforwardAdjunction
          (Y.fromSpecStalk y)).unit.app M).app U m) := by
  let P := (Scheme.Modules.pullback (Y.fromSpecStalk y)).obj M
  let c :=
    (localSpectrumSectionsStalkIso (Y.presheaf.stalk y) P).hom ≫
      (ModuleCat.restrictScalars (stalkClosedPointIso (Y.presheaf.stalk y)).inv.hom).map
        ((fromSpecStalkPullbackStalkIso Y y).hom.app M)
  apply (ConcreteCategory.bijective_of_isIso c).1
  have hleft := ConcreteCategory.congr_hom (stalkFromSpecStalkSectionsIso_cancel Y y M)
    (M.presheaf.germ U y hy m)
  change c ((stalkFromSpecStalkSectionsIso Y y M).hom (M.presheaf.germ U y hy m)) = _ at hleft
  rw [hleft]
  symm
  change (fromSpecStalkPullbackStalkIso Y y).hom.app M
    (P.presheaf.germ ⊤ (closedPoint (Y.presheaf.stalk y)) trivial
      (P.presheaf.map (homOfLE (ProperFibreIdempotents.stalkRestriction_le y U hy)).op
        (((Scheme.Modules.pullbackPushforwardAdjunction
          (Y.fromSpecStalk y)).unit.app M).app U m))) = _
  rw [P.presheaf.germ_res_apply]
  exact fromSpecStalkPullbackStalkIso_unit_germ Y y M U hy m

/-- The actual ordinary mate is invertible under flat base change of a qcqs morphism. -/
theorem cartesianBaseChangeMap_isIso_of_flat
    {W X V Y : Scheme.{u}} (a : W ⟶ X) (b : W ⟶ V) (f : X ⟶ Y) (j : V ⟶ Y)
    (h : IsPullback a b f j) [Flat j] [QuasiCompact f] [QuasiSeparated f]
    (M : X.Modules) [M.IsQuasicoherent] :
    IsIso ((cartesianBaseChangeMap a b f j h).app M) := by
  let : IsIso ((higherDirectImageFlatBaseChangeMap a b f j h 0).app M) :=
    higherDirectImageFlatBaseChangeMap_isIso_app a b f j h M 0
  have : IsIso ((cartesianBaseChangeMap a b f j h).app M ≫
      (Scheme.Modules.pushforward b).toRightDerivedZero.app
        ((Scheme.Modules.pullback a).obj M)) := by
    rw [← higherDirectImageFlatBaseChangeMap_zero_unit a b f j h M]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((Scheme.Modules.pushforward b).toRightDerivedZero.app
      ((Scheme.Modules.pullback a).obj M))

private theorem cartesianBaseChangeMap_restrict_unit
    {W X V Y : Scheme.{u}} (a : W ⟶ X) (b : W ⟶ V) (f : X ⟶ Y) (j : V ⟶ Y)
    (h : IsPullback a b f j) (M : X.Modules) (U : Y.Opens) (T : V.Opens)
    (hT : T ≤ j ⁻¹ᵁ U) (hW : b ⁻¹ᵁ T ≤ a ⁻¹ᵁ (f ⁻¹ᵁ U))
    (m : Γ(M, f ⁻¹ᵁ U)) :
    ((cartesianBaseChangeMap a b f j h).app M).app T
      (((Scheme.Modules.pullback j).obj ((Scheme.Modules.pushforward f).obj M)).presheaf.map
        (homOfLE hT).op (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
          ((Scheme.Modules.pushforward f).obj M)).app U m)) =
      ((Scheme.Modules.pullback a).obj M).presheaf.map (homOfLE hW).op
        (((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M).app (f ⁻¹ᵁ U) m) := by
  let N := (Scheme.Modules.pullback a).obj M
  have hn := PresheafOfModules.naturality_apply
    ((cartesianBaseChangeMap a b f j h).app M).val (homOfLE hT).op
      (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
        ((Scheme.Modules.pushforward f).obj M)).app U m)
  have hu := congrArg (fun k => k.app U m) (cartesianBaseChangeMap_unit a b f j h M)
  change ((cartesianPushforwardSquare a b f j h).hom.app N).app U
      (((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M).app (f ⁻¹ᵁ U) m) =
    ((cartesianBaseChangeMap a b f j h).app M).app (j ⁻¹ᵁ U)
      (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
        ((Scheme.Modules.pushforward f).obj M)).app U m) at hu
  let r := N.presheaf.map ((Opens.map b.base).map (homOfLE hT)).op
  have he := congrArg
    (fun k => k (((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M).app
      (f ⁻¹ᵁ U) m)) (cartesianPushforwardSquare_hom_app a b f j h N U)
  refine hn.trans ((congrArg r hu.symm).trans ((congrArg r he).trans ?_))
  have hm : N.presheaf.map (eqToHom (show b ⁻¹ᵁ (j ⁻¹ᵁ U) = a ⁻¹ᵁ (f ⁻¹ᵁ U) from
      congrArg (fun k => k ⁻¹ᵁ U) h.w.symm)).op ≫ r =
      N.presheaf.map (homOfLE hW).op := by
    dsimp only [r]
    rw [← CategoryTheory.Functor.map_comp]
    exact congrArg N.presheaf.map (Subsingleton.elim _ _)
  exact ConcreteCategory.congr_hom hm
    (((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M).app (f ⁻¹ᵁ U) m)

private theorem pullbackUnitIso_restrict_unit
    {X Y : Scheme.{u}} (p : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
    (h : V ≤ p ⁻¹ᵁ U) (m : Γ(Y, U)) :
    (pullbackUnitIso p).hom.app V
      (((Scheme.Modules.pullback p).obj (SheafOfModules.unit Y.ringCatSheaf)).presheaf.map
        (homOfLE h).op (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app
          (SheafOfModules.unit Y.ringCatSheaf)).app U m)) = p.appLE U V h m := by
  let O := SheafOfModules.unit Y.ringCatSheaf
  have hn := PresheafOfModules.naturality_apply (pullbackUnitIso p).hom.val
    (homOfLE h).op (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app O).app U m)
  have hu := pullbackUnitIso_homEquiv p
  rw [Adjunction.homEquiv_unit] at hu
  have hv := congrArg (fun k => k.app U m) hu
  change (pullbackUnitIso p).hom.app (p ⁻¹ᵁ U)
      (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app O).app U m) = p.app U m at hv
  exact hn.trans (congrArg (X.presheaf.map (homOfLE h).op) hv)

/-- The actual local-spectrum source lies over every neighborhood of the original point. -/
theorem localSourceRestriction_le {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y)
    (U : Y.Opens) (hy : y ∈ U) :
    ⊤ ≤ (Limits.pullback.fst f (Y.fromSpecStalk y)) ⁻¹ᵁ (f ⁻¹ᵁ U) := by
  intro z _
  change f (Limits.pullback.fst f (Y.fromSpecStalk y) z) ∈ U
  have hz := congrArg (fun k : Limits.pullback f (Y.fromSpecStalk y) ⟶ Y => k z)
    (Limits.pullback.condition (f := f) (g := Y.fromSpecStalk y))
  change f (Limits.pullback.fst f (Y.fromSpecStalk y) z) =
    Y.fromSpecStalk y (Limits.pullback.snd f (Y.fromSpecStalk y) z) at hz
  rw [hz]
  exact ProperFibreIdempotents.stalkRestriction_le y U hy trivial

/-- The original ordinary ring stalk identifies additively with the global functions on
its actual local-spectrum base change, through the original ordinary base-change mate. -/
def ordinaryStalkLocalSectionsEquiv
    {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) [QuasiCompact f] [QuasiSeparated f] :
    (f.base _* X.presheaf).stalk y ≃+ Γ(Limits.pullback f (Y.fromSpecStalk y), ⊤) := by
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let : O.IsQuasicoherent := quasicoherent_of_affineCharts O
    (fun R j _ => (affineLocallyFiniteType_unit X R j).1)
  let a := Limits.pullback.fst f (Y.fromSpecStalk y)
  let b := Limits.pullback.snd f (Y.fromSpecStalk y)
  let N := (Scheme.Modules.pullback a).obj O
  let : Flat (Y.fromSpecStalk y) := Scheme.fromSpecStalk_flat Y y
  let c := (cartesianBaseChangeMap a b f (Y.fromSpecStalk y)
    (IsPullback.of_hasPullback f (Y.fromSpecStalk y))).app O
  let : IsIso c := cartesianBaseChangeMap_isIso_of_flat a b f (Y.fromSpecStalk y)
    (IsPullback.of_hasPullback f (Y.fromSpecStalk y)) O
  let e₀ := (pushforwardStructureStalkAddIso f y).addCommGroupIsoToAddEquiv
  let e₁ := (stalkFromSpecStalkSectionsIso Y y
    ((Scheme.Modules.pushforward f).obj O)).toLinearEquiv.toAddEquiv
  let e₂ := (moduleSpecΓFunctor.mapIso (asIso c)).toLinearEquiv.toAddEquiv
  let e₃ := ((moduleSpecPushforwardGlobalSectionsIso b).app N).toLinearEquiv.toAddEquiv
  let e₄ := AddEquiv.ofBijective ((pullbackUnitIso a).hom.app ⊤).hom
    (ConcreteCategory.bijective_of_isIso ((pullbackUnitIso a).hom.app ⊤))
  exact e₀.trans (e₁.trans (e₂.trans (e₃.trans e₄)))

/-- The local-section equivalence retains the actual ordinary base-change map on sections. -/
theorem ordinaryStalkLocalSectionsEquiv_apply
    {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) [QuasiCompact f] [QuasiSeparated f]
    (s : (f.base _* X.presheaf).stalk y) :
    ordinaryStalkLocalSectionsEquiv f y s =
      (pullbackUnitIso (Limits.pullback.fst f (Y.fromSpecStalk y))).hom.app ⊤
        (((cartesianBaseChangeMap (Limits.pullback.fst f (Y.fromSpecStalk y))
          (Limits.pullback.snd f (Y.fromSpecStalk y)) f (Y.fromSpecStalk y)
          (IsPullback.of_hasPullback f (Y.fromSpecStalk y))).app
            (SheafOfModules.unit X.ringCatSheaf)).app ⊤
          ((stalkFromSpecStalkSectionsIso Y y ((Scheme.Modules.pushforward f).obj
            (SheafOfModules.unit X.ringCatSheaf))).hom
              ((pushforwardStructureStalkAddIso f y).hom s))) := by
  rfl

/-- The equivalence sends each original neighborhood germ to the literal restriction
along the original first projection from the local-spectrum pullback. -/
theorem ordinaryStalkLocalSectionsEquiv_germ
    {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) [QuasiCompact f] [QuasiSeparated f]
    (U : Y.Opens) (hy : y ∈ U) (s : Γ(X, f ⁻¹ᵁ U)) :
    ordinaryStalkLocalSectionsEquiv f y ((f.base _* X.presheaf).germ U y hy s) =
      (Limits.pullback.fst f (Y.fromSpecStalk y)).appLE (f ⁻¹ᵁ U) ⊤
        (localSourceRestriction_le f y U hy) s := by
  rw [ordinaryStalkLocalSectionsEquiv_apply, pushforwardStructureStalkAddIso_germ,
    stalkFromSpecStalkSectionsIso_germ]
  rw [cartesianBaseChangeMap_restrict_unit
    (Limits.pullback.fst f (Y.fromSpecStalk y))
    (Limits.pullback.snd f (Y.fromSpecStalk y)) f (Y.fromSpecStalk y)
    (IsPullback.of_hasPullback f (Y.fromSpecStalk y))
    (SheafOfModules.unit X.ringCatSheaf) U ⊤
    (ProperFibreIdempotents.stalkRestriction_le y U hy)
    (localSourceRestriction_le f y U hy)]
  exact pullbackUnitIso_restrict_unit (Limits.pullback.fst f (Y.fromSpecStalk y))
    (f ⁻¹ᵁ U) ⊤ (localSourceRestriction_le f y U hy) s

/-- The maximal-ideal thickening of the actual local-spectrum base change is the
original scheme-theoretic fibre, through the native pullback-pasting isomorphism. -/
def localFibreIso {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) :
    idealThickeningSpace (Limits.pullback.snd f (Y.fromSpecStalk y))
      (maximalIdeal (Y.presheaf.stalk y)) ≅ f.fiber y :=
  pullbackLeftPullbackSndIso f (Y.fromSpecStalk y) (Spec.map (Y.residue y))

/-- The local-fibre comparison retains the original two first projections. -/
theorem localFibreIso_hom_fiberι {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) :
    (localFibreIso f y).hom ≫ f.fiberι y =
      idealThickeningι (Limits.pullback.snd f (Y.fromSpecStalk y))
        (maximalIdeal (Y.presheaf.stalk y)) ≫
          Limits.pullback.fst f (Y.fromSpecStalk y) :=
  pullbackLeftPullbackSndIso_hom_fst f (Y.fromSpecStalk y) (Spec.map (Y.residue y))

private theorem appLE_top {A B : Scheme.{u}} (g : A ⟶ B) (h : ⊤ ≤ g ⁻¹ᵁ ⊤) :
    g.appLE ⊤ ⊤ h = g.appTop := by
  simpa only [Scheme.Hom.preimage_top] using (g.appLE_eq_app (U := ⊤))

private theorem appLE_comp_appTop
    {A B C : Scheme.{u}} (g : A ⟶ B) (h : B ⟶ C) (U : C.Opens)
    (hU : ⊤ ≤ h ⁻¹ᵁ U) (hV : ⊤ ≤ (g ≫ h) ⁻¹ᵁ U) :
    h.appLE U ⊤ hU ≫ g.appTop = (g ≫ h).appLE U ⊤ hV := by
  have he := Scheme.Hom.appLE_comp_appLE g h U ⊤ ⊤ hU
    (show ⊤ ≤ g ⁻¹ᵁ ⊤ from by simp)
  rw [appLE_top] at he
  exact he

private theorem appLE_congr_hom {A B : Scheme.{u}} (g h : A ⟶ B) (heq : g = h)
    (U : B.Opens) (V : A.Opens) (eg : V ≤ g ⁻¹ᵁ U) (eh : V ≤ h ⁻¹ᵁ U) :
    g.appLE U V eg = h.appLE U V eh := by
  subst h
  rfl

/-- The original ordinary stalk-to-fibre arrow is exactly restriction from the actual
local-spectrum source, followed through the native local-fibre isomorphism. -/
theorem localRestriction_stalkToFibreSections
    {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) [QuasiCompact f] [QuasiSeparated f]
    (s : (f.base _* X.presheaf).stalk y) :
    (localFibreIso f y).hom.appTop (ProperFibreIdempotents.stalkToFibreSections f y s) =
      (idealThickeningι (Limits.pullback.snd f (Y.fromSpecStalk y))
        (maximalIdeal (Y.presheaf.stalk y))).appTop
          (ordinaryStalkLocalSectionsEquiv f y s) := by
  obtain ⟨U, hy, s, rfl⟩ := (f.base _* X.presheaf).exists_germ_eq s
  have hβ := ConcreteCategory.congr_hom
    (ProperFibreIdempotents.germ_stalkToFibreSections f y U hy) s
  change ProperFibreIdempotents.stalkToFibreSections f y
      ((f.base _* X.presheaf).germ U y hy s) =
    (f.fiberι y).appLE (f ⁻¹ᵁ U) ⊤
      (ProperFibreIdempotents.fibreRestriction_le f y U hy) s at hβ
  rw [hβ, ordinaryStalkLocalSectionsEquiv_germ]
  let a := Limits.pullback.fst f (Y.fromSpecStalk y)
  let i := idealThickeningι (Limits.pullback.snd f (Y.fromSpecStalk y))
    (maximalIdeal (Y.presheaf.stalk y))
  let E := localFibreIso f y
  have hleft : ⊤ ≤ (E.hom ≫ f.fiberι y) ⁻¹ᵁ (f ⁻¹ᵁ U) := by
    intro z _
    exact ProperFibreIdempotents.fibreRestriction_le f y U hy trivial
  have hright : ⊤ ≤ (i ≫ a) ⁻¹ᵁ (f ⁻¹ᵁ U) := by
    intro z _
    exact localSourceRestriction_le f y U hy trivial
  have hc : (f.fiberι y).appLE (f ⁻¹ᵁ U) ⊤
      (ProperFibreIdempotents.fibreRestriction_le f y U hy) ≫ E.hom.appTop =
      a.appLE (f ⁻¹ᵁ U) ⊤ (localSourceRestriction_le f y U hy) ≫ i.appTop := by
    rw [appLE_comp_appTop E.hom (f.fiberι y) (f ⁻¹ᵁ U)
      (ProperFibreIdempotents.fibreRestriction_le f y U hy) hleft,
      appLE_comp_appTop i a (f ⁻¹ᵁ U) (localSourceRestriction_le f y U hy) hright]
    exact appLE_congr_hom _ _ (localFibreIso_hom_fiberι f y) _ _ hleft hright
  exact ConcreteCategory.congr_hom hc s

/-- Every actual fibre idempotent of a proper morphism over a locally Noetherian
scheme is in the image of the original ordinary pushforward-stalk map. The
preimage is an arbitrary original stalk element. -/
theorem exists_stalk_restrict_eq_of_isIdempotentElem
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsProper f] (y : Y)
    (e : Γ(f.fiber y, ⊤)) (he : IsIdempotentElem e) :
    ∃ s : (f.base _* X.presheaf).stalk y,
      ProperFibreIdempotents.stalkToFibreSections f y s = e := by
  let : IsNoetherianRing (Y.presheaf.stalk y) := inferInstance
  let b := Limits.pullback.snd f (Y.fromSpecStalk y)
  let I := maximalIdeal (Y.presheaf.stalk y)
  let E := localFibreIso f y
  let e' : Γ(idealThickeningSpace b I, ⊤) := E.hom.appTop e
  have he' : IsIdempotentElem e' := he.map E.hom.appTop.hom
  obtain ⟨a, ha⟩ := exists_section_restrict_eq_of_isIdempotentElem
    (A := Y.presheaf.stalk y) b I e' he'
  refine ⟨(ordinaryStalkLocalSectionsEquiv f y).symm a, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso E.hom.appTop).1
  rw [localRestriction_stalkToFibreSections, AddEquiv.apply_symm_apply]
  exact ha

end AlgebraicGeometry.Scheme.Cohomology.ProperFibreFormalFunctions
