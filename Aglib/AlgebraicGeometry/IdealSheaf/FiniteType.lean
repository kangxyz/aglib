/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.Modules
public import Aglib.AlgebraicGeometry.Modules.ZeroLocus
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.QuasiCoherent
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.AffinePushforward
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.AffineSections

/-!
# Finite-type native ideal sheaves

The kernel module of the canonical closed immersion of an ideal-sheaf datum is
quasicoherent. Its finite-type condition is equivalent to finite generation of the
original ideals on affine opens. Images of finite-type quasicoherent modules in the
structure module satisfy this same native finite-generation condition.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Hom

/-- Kernels of structural maps of affine morphisms are actual quasicoherent modules. -/
theorem idealModule_isQuasicoherent {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] :
    (idealModule f).IsQuasicoherent := by
  let := isQuasicoherent_unit X
  let := isQuasicoherent_unit Y
  let := isQuasicoherent_pushforward_of_isAffineHom f
    (SheafOfModules.unit X.ringCatSheaf)
  exact QuasiCoherent.quasicoherent_kernel (structureModuleMap f)

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The native ideals are finitely generated on every affine open. -/
def AffineLocallyFG : Prop := ∀ U : X.affineOpens, (I.ideal U).FG

/-- The actual ideal module of an ideal-sheaf datum is quasicoherent. -/
theorem idealModule_isQuasicoherent :
    (Scheme.Hom.idealModule I.subschemeι).IsQuasicoherent :=
  Scheme.Hom.idealModule_isQuasicoherent I.subschemeι

/-- Finite generation of native affine ideals is exactly finite generation of
sections of the actual kernel module. -/
theorem ideal_fg_iff_finite_sections (U : X.affineOpens) :
    (I.ideal U).FG ↔
      Module.Finite Γ(X, U) Γ(Scheme.Hom.idealModule I.subschemeι, U) := by
  rw [← I.ker_subschemeι_app U]
  constructor
  · intro h
    have : Module.Finite Γ(X, U) (RingHom.ker (I.subschemeι.app U).hom) :=
      Module.Finite.iff_fg.mpr h
    exact Module.Finite.equiv (Scheme.Hom.idealSectionsEquiv I.subschemeι U.val).symm
  · intro h
    have : Module.Finite Γ(X, U) ((Scheme.Hom.idealModule I.subschemeι).val.obj (op U.val)) := h
    exact Module.Finite.iff_fg.mp
      (Module.Finite.equiv (Scheme.Hom.idealSectionsEquiv I.subschemeι U.val))

/-- Chartwise finite generation and finite-type quasicoherence agree for the
original ideal-sheaf datum and its actual ideal module. -/
theorem affineLocallyFG_iff_affineLocallyFiniteType :
    I.AffineLocallyFG ↔ QuasiCoherent.affineLocallyFiniteType X
      (Scheme.Hom.idealModule I.subschemeι) := by
  let := I.idealModule_isQuasicoherent
  rw [QuasiCoherent.affineLocallyFiniteType_iff_finite_affineSections]
  exact forall_congr' fun U => I.ideal_fg_iff_finite_sections U

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.Modules.Hom

/-- The actual image ideal of a finite-type quasicoherent module is finitely
generated on every affine open. -/
theorem imageIdealData_affineLocallyFG {X : Scheme.{u}} {M : X.Modules}
    [M.IsQuasicoherent] (φ : M ⟶ SheafOfModules.unit X.ringCatSheaf)
    (hM : QuasiCoherent.affineLocallyFiniteType X M) :
    (imageIdealData φ).AffineLocallyFG := by
  intro U
  rw [imageIdealData_eq φ (imageIdealLocalizes_of_isQuasicoherent φ) U]
  have : Module.Finite (X.ringCatSheaf.obj.obj (op U.val)) (M.val.obj (op U.val)) :=
    QuasiCoherent.finite_sections_of_affineLocallyFiniteType M hM U
  exact Submodule.fg_range (φ.val.app (op U.val)).hom

end AlgebraicGeometry.Scheme.Modules.Hom
