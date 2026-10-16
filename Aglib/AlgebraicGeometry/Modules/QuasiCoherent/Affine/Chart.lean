/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Free

/-!
# Affine chart sections and free presentations

The actual scalar-compatible Gamma chart comparison transfers a module basis
to the same restricted sheaf. The scalar maps and GammaSpec identifications
are the original canonical ones.

Source: `R5Lab/AlgebraicGeometry/Curves/Degree/AffineModuleBaseChange.lean`, frozen R5 integration
`79307ff88f07d34fd5c3edb859f799c55e38f290`, SHA-256
`0739a4c1e7297a8f1dec99f8f53914339710e9240fa56c70a90ae2127581ed06`. Selected original ranges: [[153,
205]].
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry Opposite Module
namespace AlgebraicGeometry.Scheme.Modules
universe u
variable {R : CommRingCat.{u}}

/-- Transfer the given basis of affine global sections to the same quasi-coherent module sheaf. -/
def affineBasisIso {I : Type u} (M : (Spec R).Modules) [M.IsQuasicoherent]
    (b : Basis I R ((moduleSpecΓFunctor (R := R)).obj M)) :
    SheafOfModules.free (R := (Spec R).ringCatSheaf) I ≅ M := by
  letI : IsIso M.fromTildeΓ := (isQuasicoherent_iff_isIso_fromTildeΓ M).mp inferInstance
  exact (tildeBasisIso _ b).symm ≪≫ asIso M.fromTildeΓ

theorem affineChart_scalar_map {X : Scheme.{u}} (U : X.affineOpens)
    (V : (Spec Γ(X, U)).Opens) :
    (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec Γ(X, U)).presheaf.map V.leTop.op ≫
      (U.property.fromSpec.appIso V).inv =
      X.presheaf.map (homOfLE (show U.property.fromSpec ''ᵁ V ≤ U.val from by
        exact (Scheme.Hom.image_le_opensRange _ _).trans_eq
          U.property.opensRange_fromSpec)).op := by
  apply (cancel_mono (U.property.fromSpec.appIso V).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [Scheme.Hom.appIso_hom, ← Category.assoc, Scheme.Hom.naturality,
    U.property.fromSpec_app_self]
  simp only [Category.assoc, ← Functor.map_comp]
  rfl

theorem affineChart_restrict_smul {X : Scheme.{u}} (U : X.affineOpens)
    (M : X.Modules) (V : (Spec Γ(X, U)).Opens)
    (r : Γ(X, U)) (m : Γ(M.restrict U.property.fromSpec, V)) :
    (M.restrictAppIso U.property.fromSpec V).hom (r • m) =
      X.presheaf.map (homOfLE (show U.property.fromSpec ''ᵁ V ≤ U.val from by
        exact (Scheme.Hom.image_le_opensRange _ _).trans_eq
          U.property.opensRange_fromSpec)).op r •
        (M.restrictAppIso U.property.fromSpec V).hom m := by
  rw [Scheme.Modules.smul_Spec_def, Scheme.Modules.smul_restrictAppIso_hom_apply]
  have h := congrArg (fun k : Γ(X, U) ⟶ Γ(X, U.property.fromSpec ''ᵁ V) ↦ k r)
    (affineChart_scalar_map U V)
  simpa only [ConcreteCategory.comp_apply] using congrArg
    (fun a ↦ a • (M.restrictAppIso U.property.fromSpec V).hom m) h

/-- The scalar-compatible global-sections comparison for the actual affine spectrum chart. -/
def affineChartΓIso {X : Scheme.{u}} (U : X.affineOpens) (M : X.Modules) :
    (moduleSpecΓFunctor (R := Γ(X, U))).obj (M.restrict U.property.fromSpec) ≅
      ModuleCat.of Γ(X, U) Γ(M, U) := by
  let e : Γ(M.restrict U.property.fromSpec, ⊤) ≅ Γ(M, U) :=
    M.restrictAppIso U.property.fromSpec ⊤ ≪≫
      M.presheaf.mapIso (eqToIso (by
        simp [Scheme.Hom.image_top_eq_opensRange, U.property.opensRange_fromSpec])).op
  refine ModuleCat.isoMk e ?_
  intro r
  ext m
  change Γ(M.restrict U.property.fromSpec, ⊤) at m
  change r • e.hom m = e.hom (r • m)
  dsimp only [e, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom]
  simp only [ConcreteCategory.comp_apply]
  rw [affineChart_restrict_smul U M, M.map_smul]
  simp only [← Functor.map_comp_apply]
  simp only [← op_comp, eqToHom_comp_homOfLE]
  change _ = (X.presheaf.map (𝟙 (op U.val))) r • _
  rw [X.presheaf.map_id]
  rfl

end AlgebraicGeometry.Scheme.Modules
