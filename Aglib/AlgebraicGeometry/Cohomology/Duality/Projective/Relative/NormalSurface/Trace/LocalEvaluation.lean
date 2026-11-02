/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.Trace.Localization
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.Trace.DegreeZero
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.Trace.BaseChange
public import Aglib.AlgebraicGeometry.Modules.Pullback.LocalSpectrum.Naturality

/-!
# The actual local-spectrum sections comparison is the ordinary base-change mate

The original degree-zero stalk comparison is identified with the original
ordinary flat base-change map, before any trace or inverse trace is applied.
This connects the actual local-sections coordinate to the ordinary counit
formula in `Trace.BaseChange` without using faithfulness of global sections.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u

private theorem canonicalTrace_inverse_square
    {C : Type*} [Category* C] {A B D E : C}
    (e : A ≅ B) (d : D ≅ E) (p : A ⟶ D) (q : B ⟶ E)
    (h : e.hom ≫ q = p ≫ d.hom) : e.inv ≫ p = q ≫ d.inv := by
  apply (cancel_mono d.hom).mp
  rw [Category.assoc, ← h, Iso.inv_hom_id_assoc,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The original mu comparison is exactly stalk-to-local-sections followed by
the ORIGINAL ordinary base-change mate and the original pushforward-sections
map. All local rings and scalar maps remain the actual geometric ones. -/
theorem ordinaryPushforwardStalkSectionsLinearEquiv_ordinary
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (M : X.Modules) [M.IsQuasicoherent] (y : Y)
    (s : (moduleStalk Y y).obj ((pushforward f).obj M)) :
    let a := Limits.pullback.fst f (Y.fromSpecStalk y)
    let b := Limits.pullback.snd f (Y.fromSpecStalk y)
    let N := (Scheme.Modules.pullback a).obj M
    ordinaryPushforwardStalkSectionsLinearEquiv f M y s =
      (moduleSpecPushforwardGlobalSectionsIso b).hom.app N
        (moduleSpecΓFunctor.map
          ((cartesianBaseChangeMap a b f (Y.fromSpecStalk y)
            (IsPullback.of_hasPullback f (Y.fromSpecStalk y))).app M)
          ((stalkFromSpecStalkSectionsIso Y y ((pushforward f).obj M)).hom s)) := by
  let j := Y.fromSpecStalk y
  let a := Limits.pullback.fst f j
  let b := Limits.pullback.snd f j
  let N := (Scheme.Modules.pullback a).obj M
  let h := IsPullback.of_hasPullback f j
  let : Flat j := Scheme.fromSpecStalk_flat Y y
  let : QuasiCompact b := inferInstanceAs (QuasiCompact (Limits.pullback.snd f j))
  let : QuasiSeparated b := inferInstanceAs (QuasiSeparated (Limits.pullback.snd f j))
  let β := (cartesianBaseChangeMap a b f j h).app M
  let β₀ := (higherDirectImageFlatBaseChangeMap a b f j h 0).app M
  let ΓS := moduleSpecΓFunctor (R := Y.presheaf.stalk y)
  let e := (Scheme.Modules.pullback j).mapIso ((pushforward f).rightDerivedZeroIsoSelf.app M)
  let d := (pushforward b).rightDerivedZeroIsoSelf.app N
  have hz : e.inv ≫ β₀ = β ≫ d.inv :=
    canonicalTrace_inverse_square e d β₀ β (canonicalTraceHigherBaseChange_zero a b f j h M)
  let x := (stalkFromSpecStalkSectionsIso Y y ((pushforward f).obj M)).hom s
  have hn :
      (stalkFromSpecStalkSectionsIso Y y (((pushforward f).rightDerived 0).obj M)).hom
        ((moduleStalk Y y).map ((pushforward f).rightDerivedZeroIsoSelf.inv.app M) s) =
      ΓS.map e.inv x := by
    exact ConcreteCategory.congr_hom
      (stalkFromSpecStalkSectionsIso_naturality Y y
        ((pushforward f).rightDerivedZeroIsoSelf.inv.app M)) s
  have hm : ΓS.map β₀ (ΓS.map e.inv x) =
      ΓS.map ((pushforward b).toRightDerivedZero.app N) (ΓS.map β x) := by
    have he := congrArg ΓS.map hz
    rw [ΓS.map_comp, ΓS.map_comp] at he
    exact ConcreteCategory.congr_hom he x
  rw [ordinaryPushforwardStalkSectionsLinearEquiv_apply,
    moduleHigherDirectImageStalkLinearEquiv_apply]
  rw [hn, hm]
  exact moduleHigherDirectImageAffineSectionsLinearEquiv_toRightDerivedZero b N
    (injectiveResolution N) (ΓS.map β x)

/-- The inverse localized trace is exactly the sections of the original
base-change mate after the pulled-back inverse trace. This is the precise input
to the original counit in `ordinaryTracePullback_baseChange`; invertibility is
required of the actual trace, not inferred from properness. -/
theorem ordinaryPushforwardIsoOnLocalSections_symm_evaluation
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (M : X.Modules) [M.IsQuasicoherent] (L : Y.Modules)
    (τ : (pushforward f).obj M ⟶ L) [IsIso τ] (y : Y)
    (s : (moduleStalk Y y).obj L) :
    let j := Y.fromSpecStalk y
    let a := Limits.pullback.fst f j
    let b := Limits.pullback.snd f j
    let N := (Scheme.Modules.pullback a).obj M
    (ordinaryPushforwardIsoOnLocalSections f M L τ y).symm s =
      (moduleSpecPushforwardGlobalSectionsIso b).hom.app N
        (moduleSpecΓFunctor.map
          ((Scheme.Modules.pullback j).map (inv τ) ≫
            (cartesianBaseChangeMap a b f j (IsPullback.of_hasPullback f j)).app M)
          ((stalkFromSpecStalkSectionsIso Y y L).hom s)) := by
  simp +instances only [ordinaryPushforwardIsoOnLocalSections, LinearEquiv.trans_symm,
    LinearEquiv.symm_symm, LinearEquiv.trans_apply, CategoryTheory.Iso.toLinearEquiv_symm,
    CategoryTheory.Iso.toLinearEquiv_apply, Iso.symm_hom, Functor.mapIso_inv, asIso_inv]
  rw [ordinaryPushforwardStalkSectionsLinearEquiv_ordinary]
  have hn := ConcreteCategory.congr_hom
    (stalkFromSpecStalkSectionsIso_naturality Y y (inv τ)) s
  simp only [ModuleCat.comp_apply] at hn
  rw [hn, Functor.map_comp, ModuleCat.comp_apply]
  rfl

end AlgebraicGeometry.Scheme.Cohomology
