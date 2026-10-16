/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.FiniteModel.BaseChange

/-!
# The same finite-cover model computes native derived global sections after base change

The actual scalar extension of the same constructed finite-projective complex
maps to the original integer Cech complex of the ordinary pulled coefficient.
This literal chain map is a quasi-isomorphism, so the installed derived-global-
sections comparison gives an actual native derived-object isomorphism for
every ring map. The comparison retains the original Cech and resolution maps.

Owner extraction: original projective derived-base-change source SHA-256
`b9f94e326dbce3400648f09a8be3168066b46c2168ead1ad3d173281f23b7a90`.
Only the supplied finite affine cover replaces the coordinate family; the
actual tensor complex, original integer Cech arrow and derived units remain.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open HomologicalComplex

namespace AlgebraicGeometry.Scheme.Cohomology.FiniteCechCohomologyModel

variable {R : Type u} [CommRing R] {ι : Type u} {X : Scheme.{u}} [X.IsSeparated]
  {f : X ⟶ Spec (CommRingCat.of R)} {U : ι → X.Opens}
  {M : X.Modules} [M.IsQuasicoherent] {n : ℕ}
  (D : FiniteCechCohomologyModel R ι X f U M n)
  (hU : ∀ j, IsAffineOpen (U j)) (hcover : iSup U = ⊤)
  {B : Type u} [CommRing B] (σ : R →+* B)

/-- The native bounded-below packing of the actual scalar-extended model. -/
def baseChangePlus : CochainComplex.Plus (ModuleCat.{u} B) :=
  (ModuleCat.extendScalars σ).mapCochainComplexPlus.obj D.toPlus

include hU hcover

/-- The same scalar-extended model comparison followed by the original
finite Cech inclusion for the ordinary pulled coefficient. -/
def baseChangeToCechPlus (e : ι ≃ Fin (n + 1))
    (hflat : Scheme.Modules.relativeFlat f M) :
    let Y := pullback f (Spec.map (CommRingCat.ofHom σ))
    let p := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
    let r := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
    D.baseChangePlus σ ⟶ moduleCechComplexPlus Y
      (r.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)
      (fun j => p ⁻¹ᵁ (U j)) ((Scheme.Modules.pullback p).obj M) :=
  ⟨D.baseChangeComparison hU hcover e hflat σ ≫
    moduleFiniteCechInclusion (pullback f (Spec.map (CommRingCat.ofHom σ)))
      ((pullback.snd f (Spec.map (CommRingCat.ofHom σ))).appTop.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)
      (fun j => (pullback.fst f (Spec.map (CommRingCat.ofHom σ))) ⁻¹ᵁ
        (U j))
      ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom σ)))).obj M) n⟩

/-- The literal map to integer Cech retains the tensor of the original
source comparison and the original integer Cech base-change map. -/
theorem baseChangeToCechPlus_hom_eq (e : ι ≃ Fin (n + 1))
    (hflat : Scheme.Modules.relativeFlat f M) :
    letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    (D.baseChangeToCechPlus hU hcover σ e hflat).hom =
      ((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).map D.toCechPlus.hom ≫
        moduleCechIntBaseChangeMap f σ M U :=
  D.baseChangeComparison_inclusion hU hcover e hflat σ

/-- The literal map to original integer Cech is a quasi-isomorphism after
every ring map, with no flatness or Noetherianity hypothesis on the new ring. -/
theorem baseChangeToCechPlus_quasiIso (e : ι ≃ Fin (n + 1))
    (hflat : Scheme.Modules.relativeFlat f M) :
    QuasiIso (D.baseChangeToCechPlus hU hcover σ e hflat).hom := by
  let Y := pullback f (Spec.map (CommRingCat.ofHom σ))
  let p : Y ⟶ X := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
  let r := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
  let β := r.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
  let N := (Scheme.Modules.pullback p).obj M
  let V : ι → Y.Opens := fun j => p ⁻¹ᵁ (U j)
  let : IsAffineHom p := MorphismProperty.pullback_fst f
    (Spec.map (CommRingCat.ofHom σ))
    (inferInstance : IsAffineHom (Spec.map (CommRingCat.ofHom σ)))
  let : Y.IsSeparated := ⟨by rw [← terminal.comp_from p]; infer_instance⟩
  let : N.IsQuasicoherent := Scheme.Modules.quasicoherent_pullback p M
  let : QuasiIso (D.baseChangeComparison hU hcover e hflat σ) :=
    D.baseChangeComparison_quasiIso hU hcover e hflat σ
  let : QuasiIso (moduleFiniteCechInclusion Y β V N n) :=
    moduleFiniteCechInclusion_quasiIso Y β V N n e
      (fun j => (hU j).preimage p)
      (p.iSup_preimage_eq_top hcover)
  change QuasiIso (D.baseChangeComparison hU hcover e hflat σ ≫ moduleFiniteCechInclusion Y β V N n)
  infer_instance

local instance baseChangeDerivedSheaves (Z : Scheme.{u}) : HasDerivedCategory.{u + 1} Z.Modules :=
  HasDerivedCategory.standard _

local instance baseChangeDerivedModules (A : Type u) [CommRing A] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _

/-- The actual scalar extension of the same finite-projective model
represents installed derived global sections of the ordinary pulled
coefficient. The supplied resolution is the original native module-sheaf
injective resolution on the actual fibre product. -/
def baseChangeDerivedGlobalSectionsIso (e : ι ≃ Fin (n + 1))
    (hflat : Scheme.Modules.relativeFlat f M)
    (I : InjectiveResolution
      ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom σ)))).obj M)) :
    let Y := pullback f (Spec.map (CommRingCat.ofHom σ))
    let p := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
    let r := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
    let β := r.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
    let N := (Scheme.Modules.pullback p).obj M
    DerivedCategory.Plus.Q.obj (D.baseChangePlus σ) ≅
      (moduleGlobalSectionsFunctorOfHom Y β).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj N) := by
  let Y := pullback f (Spec.map (CommRingCat.ofHom σ))
  let p : Y ⟶ X := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
  let r := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
  let β := r.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
  let N := (Scheme.Modules.pullback p).obj M
  let V : ι → Y.Opens := fun j => p ⁻¹ᵁ (U j)
  let : IsAffineHom p := MorphismProperty.pullback_fst f
    (Spec.map (CommRingCat.ofHom σ))
    (inferInstance : IsAffineHom (Spec.map (CommRingCat.ofHom σ)))
  let : Y.IsSeparated := ⟨by rw [← terminal.comp_from p]; infer_instance⟩
  let : N.IsQuasicoherent := Scheme.Modules.quasicoherent_pullback p M
  have hV : ∀ j, IsAffineOpen (V j) :=
    fun j => (hU j).preimage p
  have haff : ∀ (q : ℕ) (a : Fin (q + 1) → ι), IsAffineOpen (∏ᶜ fun k => V (a k)) :=
    isAffineOpen_cechTuple_of_isSeparated V hV
  let : IsIso (DerivedCategory.Plus.Q.map (D.baseChangeToCechPlus hU hcover σ e hflat)) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso (ModuleCat.{u} B)) _
      (D.baseChangeToCechPlus_quasiIso hU hcover σ e hflat)
  exact asIso (DerivedCategory.Plus.Q.map (D.baseChangeToCechPlus hU hcover σ e hflat)) ≪≫
    moduleCechDerivedGlobalSectionsIso Y β V I
      (p.iSup_preimage_eq_top hcover) haff

/-- The native derived-object comparison keeps the localized original
chain map and the original Cech/injective-resolution derived comparison.
The equation is independent of the proof of affine tuple intersections. -/
theorem baseChangeDerivedGlobalSectionsIso_hom (e : ι ≃ Fin (n + 1))
    (hflat : Scheme.Modules.relativeFlat f M)
    (I : InjectiveResolution
      ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom σ)))).obj M))
    (haff : ∀ (q : ℕ) (a : Fin (q + 1) → ι),
      IsAffineOpen (∏ᶜ fun k => (pullback.fst f (Spec.map (CommRingCat.ofHom σ))) ⁻¹ᵁ
        (U (a k)))) :
    let Y := pullback f (Spec.map (CommRingCat.ofHom σ))
    let p := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
    let r := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
    let β := r.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
    let V : ι → Y.Opens := fun j => p ⁻¹ᵁ (U j)
    (D.baseChangeDerivedGlobalSectionsIso hU hcover σ e hflat I).hom =
      DerivedCategory.Plus.Q.map (D.baseChangeToCechPlus hU hcover σ e hflat) ≫
        (moduleCechDerivedGlobalSectionsIso Y β V I
          (p.iSup_preimage_eq_top hcover)
          haff).hom := rfl

end AlgebraicGeometry.Scheme.Cohomology.FiniteCechCohomologyModel
