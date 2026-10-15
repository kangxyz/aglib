/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.FiniteModel.BaseChange

/-!
# The same projective model computes native derived global sections after base change

The actual scalar extension of the same constructed finite-projective complex
maps to the original integer Cech complex of the ordinary pulled coefficient.
This literal chain map is a quasi-isomorphism, so the installed derived-global-
sections comparison gives an actual native derived-object isomorphism for
every ring map. The comparison retains the original Cech and resolution maps.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open HomologicalComplex AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.Scheme.Cohomology.ProjectiveCohomologyModel

variable {R : Type u} [CommRing R] {ι : Type u} {X : Scheme.{u}}
  {i : X ⟶ ProjectiveSpace R ι} [IsClosedImmersion i]
  {f : X ⟶ Spec (CommRingCat.of R)} {M : X.Modules} [M.IsQuasicoherent] {n : ℕ}
  (D : ProjectiveCohomologyModel R ι i f M n)
  {B : Type u} [CommRing B] (σ : R →+* B)

/-- The native bounded-below packing of the actual scalar-extended model. -/
def baseChangePlus : CochainComplex.Plus (ModuleCat.{u} B) :=
  (ModuleCat.extendScalars σ).mapCochainComplexPlus.obj D.toPlus

/-- The same scalar-extended model comparison followed by the original
finite Cech inclusion for the ordinary pulled coefficient. -/
def baseChangeToCechPlus (e : ι ≃ Fin (n + 1))
    (hflat : Scheme.Modules.relativeFlat f M) :
    let Y := pullback f (Spec.map (CommRingCat.ofHom σ))
    let p := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
    let r := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
    D.baseChangePlus σ ⟶ moduleCechComplexPlus Y
      (r.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)
      (fun j => p ⁻¹ᵁ (i ⁻¹ᵁ coordinateOpen R ι j)) ((Scheme.Modules.pullback p).obj M) :=
  ⟨D.baseChangeComparison e hflat σ ≫
    moduleFiniteCechInclusion (pullback f (Spec.map (CommRingCat.ofHom σ)))
      ((pullback.snd f (Spec.map (CommRingCat.ofHom σ))).appTop.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)
      (fun j => (pullback.fst f (Spec.map (CommRingCat.ofHom σ))) ⁻¹ᵁ
        (i ⁻¹ᵁ coordinateOpen R ι j))
      ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom σ)))).obj M) n⟩

/-- The literal map to integer Cech retains the tensor of the original
source comparison and the original integer Cech base-change map. -/
theorem baseChangeToCechPlus_hom_eq (e : ι ≃ Fin (n + 1))
    (hflat : Scheme.Modules.relativeFlat f M) :
    letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    (D.baseChangeToCechPlus σ e hflat).hom =
      ((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).map D.toCechPlus.hom ≫
        moduleCechIntBaseChangeMap f σ M (fun j => i ⁻¹ᵁ coordinateOpen R ι j) :=
  D.baseChangeComparison_inclusion e hflat σ

/-- The literal map to original integer Cech is a quasi-isomorphism after
every ring map, with no flatness or Noetherianity hypothesis on the new ring. -/
theorem baseChangeToCechPlus_quasiIso (e : ι ≃ Fin (n + 1))
    (hflat : Scheme.Modules.relativeFlat f M) :
    QuasiIso (D.baseChangeToCechPlus σ e hflat).hom := by
  let Y := pullback f (Spec.map (CommRingCat.ofHom σ))
  let p : Y ⟶ X := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
  let r := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
  let β := r.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
  let N := (Scheme.Modules.pullback p).obj M
  let V : ι → Y.Opens := fun j => p ⁻¹ᵁ (i ⁻¹ᵁ coordinateOpen R ι j)
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from i]; infer_instance⟩
  let : IsAffineHom p := MorphismProperty.pullback_fst f
    (Spec.map (CommRingCat.ofHom σ))
    (inferInstance : IsAffineHom (Spec.map (CommRingCat.ofHom σ)))
  let : Y.IsSeparated := ⟨by rw [← terminal.comp_from p]; infer_instance⟩
  let : N.IsQuasicoherent := Scheme.Modules.quasicoherent_pullback p M
  let : QuasiIso (D.baseChangeComparison e hflat σ) :=
    D.baseChangeComparison_quasiIso e hflat σ
  let : QuasiIso (moduleFiniteCechInclusion Y β V N n) :=
    moduleFiniteCechInclusion_quasiIso Y β V N n e
      (fun j => ((isAffineOpen_coordinateOpen R ι j).preimage i).preimage p)
      (p.iSup_preimage_eq_top (i.iSup_preimage_eq_top (iSup_coordinateOpen_eq_top R ι)))
  change QuasiIso (D.baseChangeComparison e hflat σ ≫ moduleFiniteCechInclusion Y β V N n)
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
  let V : ι → Y.Opens := fun j => p ⁻¹ᵁ (i ⁻¹ᵁ coordinateOpen R ι j)
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from i]; infer_instance⟩
  let : IsAffineHom p := MorphismProperty.pullback_fst f
    (Spec.map (CommRingCat.ofHom σ))
    (inferInstance : IsAffineHom (Spec.map (CommRingCat.ofHom σ)))
  let : Y.IsSeparated := ⟨by rw [← terminal.comp_from p]; infer_instance⟩
  let : N.IsQuasicoherent := Scheme.Modules.quasicoherent_pullback p M
  have hV : ∀ j, IsAffineOpen (V j) :=
    fun j => ((isAffineOpen_coordinateOpen R ι j).preimage i).preimage p
  have haff : ∀ (q : ℕ) (a : Fin (q + 1) → ι), IsAffineOpen (∏ᶜ fun k => V (a k)) := by
    intro q a
    have he : (∏ᶜ fun k => V (a k)) = ⨅ k, V (a k) := by
      apply le_antisymm
      · exact le_iInf fun k => leOfHom (Pi.π _ k)
      · exact leOfHom (Pi.lift fun k => homOfLE (iInf_le _ k))
    rw [he]
    exact IsAffineOpen.iInf (fun k => hV (a k))
  let : IsIso (DerivedCategory.Plus.Q.map (D.baseChangeToCechPlus σ e hflat)) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso (ModuleCat.{u} B)) _
      (D.baseChangeToCechPlus_quasiIso σ e hflat)
  exact asIso (DerivedCategory.Plus.Q.map (D.baseChangeToCechPlus σ e hflat)) ≪≫
    moduleCechDerivedGlobalSectionsIso Y β V I
      (p.iSup_preimage_eq_top (i.iSup_preimage_eq_top (iSup_coordinateOpen_eq_top R ι))) haff

/-- The native derived-object comparison keeps the localized original
chain map and the original Cech/injective-resolution derived comparison.
The equation is independent of the proof of affine tuple intersections. -/
theorem baseChangeDerivedGlobalSectionsIso_hom (e : ι ≃ Fin (n + 1))
    (hflat : Scheme.Modules.relativeFlat f M)
    (I : InjectiveResolution
      ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom σ)))).obj M))
    (haff : ∀ (q : ℕ) (a : Fin (q + 1) → ι),
      IsAffineOpen (∏ᶜ fun k => (pullback.fst f (Spec.map (CommRingCat.ofHom σ))) ⁻¹ᵁ
        (i ⁻¹ᵁ coordinateOpen R ι (a k)))) :
    let Y := pullback f (Spec.map (CommRingCat.ofHom σ))
    let p := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
    let r := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
    let β := r.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
    let V : ι → Y.Opens := fun j => p ⁻¹ᵁ (i ⁻¹ᵁ coordinateOpen R ι j)
    (D.baseChangeDerivedGlobalSectionsIso σ e hflat I).hom =
      DerivedCategory.Plus.Q.map (D.baseChangeToCechPlus σ e hflat) ≫
        (moduleCechDerivedGlobalSectionsIso Y β V I
          (p.iSup_preimage_eq_top (i.iSup_preimage_eq_top (iSup_coordinateOpen_eq_top R ι)))
          haff).hom := rfl

end AlgebraicGeometry.Scheme.Cohomology.ProjectiveCohomologyModel
