/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.IdealPowers.AffinePushforward
public import Aglib.AlgebraicGeometry.Modules.Pushforward.ClosedImmersion
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.Completion

/-! # Native formal systems under closed pushforward -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] {X Y : Scheme.{u}}
  (i : X ⟶ Y) [IsClosedImmersion i] (f : Y ⟶ Spec (CommRingCat.of A))
  (I : Ideal A)

local notation "KX" => idealThickeningIdealSheaf (i ≫ f) I
local notation "KY" => idealThickeningIdealSheaf f I

/-- Original closed pushforward commutes with native ideal-sheaf quotients. -/
def closedPushforwardNativeQuotientIso (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    (pushforward i).obj ((idealSheafQuotientFunctor X (KX ^ n)).obj F) ≅
      (idealSheafQuotientFunctor Y (KY ^ n)).obj ((pushforward i).obj F) := by
  let : ((pushforward i).obj F).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_isAffineHom i F
  exact (pushforward i).mapIso (idealPowerQuotientIdealSheafIso (i ≫ f) I F n).symm ≪≫
    affinePushforwardIdealQuotientIso i f F (I ^ n) ≪≫
    idealPowerQuotientIdealSheafIso f I ((pushforward i).obj F) n

@[reassoc (attr := simp)]
theorem closedPushforwardNativeQuotientIso_unit (F : X.Modules) [F.IsQuasicoherent]
    (n : ℕ) :
    (pushforward i).map ((idealSheafQuotientUnit X (KX ^ n)).app F) ≫
      (closedPushforwardNativeQuotientIso i f I F n).hom =
    (idealSheafQuotientUnit Y (KY ^ n)).app ((pushforward i).obj F) := by
  let : ((pushforward i).obj F).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_isAffineHom i F
  have hπ : (pushforward i).map
      (idealQuotientπ X (idealThickeningBaseScalar (i ≫ f)) F (I ^ n)) ≫
        (affinePushforwardIdealQuotientIso i f F (I ^ n)).hom =
      idealQuotientπ Y (idealThickeningBaseScalar f) ((pushforward i).obj F) (I ^ n) := by
    simpa only [idealThickeningBaseScalar, Scheme.Hom.comp_app,
      TopologicalSpace.Opens.map_top] using affinePushforwardIdealQuotientIso_π i f F (I ^ n)
  dsimp only [closedPushforwardNativeQuotientIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom]
  rw [← Functor.map_comp_assoc, ← idealQuotientπ_idealSheafIso_hom (i ≫ f) I F n,
    Category.assoc, Iso.hom_inv_id, Category.comp_id,
    ← Category.assoc, hπ]
  exact idealQuotientπ_idealSheafIso_hom f I ((pushforward i).obj F) n

/-- Annihilation by the base ideal power survives actual closed pushforward. -/
theorem closedPushforward_killed_basePower (F : X.Modules) [F.IsQuasicoherent]
    (n : ℕ) (hF : killedByIdealSheaf (KX ^ n) F) :
    killedByIdealSheaf (KY ^ n) ((pushforward i).obj F) := by
  have hunit : IsIso ((idealSheafQuotientUnit X (KX ^ n)).app F) :=
    (pullbackPushforwardUnit_isIso_iff_killedByIdealSheaf (KX ^ n).subschemeι F).mpr
      (by simpa only [IdealSheafData.ker_subschemeι] using hF)
  have : IsIso ((idealSheafQuotientUnit Y (KY ^ n)).app ((pushforward i).obj F)) := by
    rw [← closedPushforwardNativeQuotientIso_unit i f I F n]
    infer_instance
  have hk := (pullbackPushforwardUnit_isIso_iff_killedByIdealSheaf
    (KY ^ n).subschemeι ((pushforward i).obj F)).mp this
  simpa only [IdealSheafData.ker_subschemeι] using hk

variable [IsLocallyNoetherian X] [IsLocallyNoetherian Y]

local instance formalCoefficient_isQuasicoherent (F : AdicSystem X KX) (n : ℕᵒᵖ) :
    (F.obj.obj n).IsQuasicoherent :=
  QuasiCoherent.quasicoherent_of_affineCharts _
    (fun R j _ => ((F.property.coherent n.unop) R j).1)

omit [IsLocallyNoetherian Y] in
/-- Pushforward of an arbitrary native formal coherent system remains native adic. -/
theorem closedPushforward_isAdicSystem (F : AdicSystem X KX) :
    IsAdicSystem Y KY (F.obj ⋙ pushforward i) where
  coherent n := QuasiCoherent.FiniteMorphism.affineLocallyFiniteType_pushforward i
    (F.property.coherent n)
  annihilated n := closedPushforward_killed_basePower i f I _ n (F.property.annihilated n)
  reduction n := ⟨(closedPushforwardNativeQuotientIso i f I _ n).symm ≪≫
    (pushforward i).mapIso (F.reductionIso n), by
      dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
      change (idealSheafQuotientUnit Y (KY ^ n)).app
        ((pushforward i).obj (F.obj.obj (op (n + 1)))) ≫
          (closedPushforwardNativeQuotientIso i f I (F.obj.obj (op (n + 1))) n).inv ≫
            (pushforward i).map (F.reductionIso n).hom =
        (pushforward i).map (F.transition n)
      rw [← closedPushforwardNativeQuotientIso_unit i f I _ n,
        Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp,
        F.unit_reductionIso_hom]⟩

/-- The actual pushforward diagram with its proved formal conditions. -/
def closedPushforwardAdicSystem (F : AdicSystem X KX) : AdicSystem Y KY :=
  ⟨F.obj ⋙ pushforward i, closedPushforward_isAdicSystem i f I F⟩

end AlgebraicGeometry.Scheme.Cohomology
