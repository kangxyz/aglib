/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Aglib.AlgebraicGeometry.Modules.Flat.Relative.Locality
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Localization.AffineOpenSections

/-!
# Actual affine sections of a relatively flat coefficient

The native general scalar-tower localization criterion detects flatness of an
affine section module over the original base ring. Its localization maps are
the original `tilde.toStalk`; quasicoherence supplies the original
`fromTildeΓ` isomorphism. The arbitrary affine-open result uses the actual
restriction unit and the literal section-ring map of the structure morphism.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- Quasicoherent actual affine sections are flat over the original base ring
when their coefficient is relatively flat for the given affine ring map. -/
theorem flat_moduleSpecΓFunctor_of_relativeFlat {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (M : (Spec B).Modules) [M.IsQuasicoherent]
    (hM : relativeFlat (Spec.map φ) M) :
    Module.Flat A ((ModuleCat.restrictScalars φ.hom).obj (moduleSpecΓFunctor.obj M)) := by
  let := φ.hom.toAlgebra
  let E := moduleSpecΓFunctor.obj M
  let F (P : Ideal B) [P.IsMaximal] : ModuleCat A :=
    (ModuleCat.restrictScalars φ.hom).obj
      (ModuleCat.of B ((tilde E).presheaf.stalk (⟨P, inferInstance⟩ : Spec B)))
  let : IsScalarTower A B ((ModuleCat.restrictScalars φ.hom).obj E) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let hF : ∀ (P : Ideal B) [P.IsMaximal], IsScalarTower A B (F P) :=
    fun _ _ => IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hloc (x : Spec B) :
      IsLocalizedModule x.asIdeal.primeCompl (tilde.toStalk E x).hom := inferInstance
  refine @Module.flat_of_isLocalized_maximal A B _ _ _
    ((ModuleCat.restrictScalars φ.hom).obj E) _ _ _ _ (fun P _ => F P)
    (fun P _ => inferInstanceAs (AddCommMonoid (F P)))
    (fun P _ => inferInstanceAs (Module A (F P)))
    (fun P _ => inferInstanceAs (Module B (F P))) hF
    (fun P _ => (tilde.toStalk E (⟨P, inferInstance⟩ : Spec B)).hom)
    (fun P _ => hloc (⟨P, inferInstance⟩ : Spec B)) ?_
  intro P hP
  let x : Spec B := ⟨P, inferInstance⟩
  let e := (ModuleCat.restrictScalars φ.hom).mapIso
    ((ModuleCat.restrictScalars (StructureSheaf.toStalk B x).hom).mapIso
      ((moduleStalk (Spec B) x).mapIso (asIso M.fromTildeΓ)))
  exact (Module.Flat.equiv_iff e.toLinearEquiv).mpr
    (flat_stalk_of_relativeFlat_specMap φ hM x)

/-- The actual ring map on an affine open gives the original affine chart
followed by the original structure morphism. -/
theorem SpecMap_affineOpen_baseRingHom {X : Scheme.{u}} {A : CommRingCat.{u}}
    (f : X ⟶ Spec A) {U : X.Opens} (hU : IsAffineOpen U) :
    Spec.map ((Scheme.ΓSpecIso A).inv ≫ f.appLE ⊤ U (by simp)) = hU.fromSpec ≫ f := by
  have hA : (isAffineOpen_top (Spec A)).fromSpec = Spec.map (Scheme.ΓSpecIso A).inv := by
    rw [IsAffineOpen.fromSpec_top]
    apply (cancel_mono (Spec A).isoSpec.hom).mp
    change (Spec A).isoSpec.inv ≫ (Spec A).toSpecΓ =
      Spec.map (Scheme.ΓSpecIso A).inv ≫ (Spec A).toSpecΓ
    rw [SpecMap_ΓSpecIso_inv_toSpecΓ]
    exact (Spec A).isoSpec.inv_hom_id
  rw [Spec.map_comp, ← hA]
  exact IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top (Spec A)) hU _

/-- The original sections on any affine open are flat over the original base
ring with the literal action supplied by the structure morphism. -/
theorem flat_affineOpen_sections_of_relativeFlat {X : Scheme.{u}} {A : CommRingCat.{u}}
    (f : X ⟶ Spec A) (M : X.Modules) [M.IsQuasicoherent]
    (hM : relativeFlat f M) {U : X.Opens} (hU : IsAffineOpen U) :
    Module.Flat A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso A).inv ≫
        f.appLE ⊤ U (by simp)).hom).obj (ModuleCat.of Γ(X, U) Γ(M, U))) := by
  let φ : A ⟶ Γ(X, U) := (Scheme.ΓSpecIso A).inv ≫ f.appLE ⊤ U (by simp)
  let N := M.restrict hU.fromSpec
  let : N.IsQuasicoherent := isQuasicoherent_restrictFunctor hU.fromSpec M
  have hN : relativeFlat (Spec.map φ) N := by
    rw [show Spec.map φ = hU.fromSpec ≫ f from SpecMap_affineOpen_baseRingHom f hU]
    exact relativeFlat_restrict hU.fromSpec f hM
  have H := flat_moduleSpecΓFunctor_of_relativeFlat φ N hN
  let e := (ModuleCat.restrictScalars φ.hom).mapIso
    (QuasiCoherent.AffineOpenSections.toSpecTopSectionsLinearEquiv M hU).toModuleIso
  exact (Module.Flat.equiv_iff e.toLinearEquiv).mpr H

end AlgebraicGeometry.Scheme.Modules
