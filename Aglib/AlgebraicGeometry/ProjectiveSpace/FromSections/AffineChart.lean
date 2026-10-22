/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.FromSections.Naturality
public import Aglib.AlgebraicGeometry.ProjectiveSpace.AffineImmersion

/-!
# Unit sections and the standard affine chart

The ordinary projective morphism of `(1,sᵢ)` is the actual standard-chart
morphism, over the originally supplied ring homomorphism. All rings may have
nilpotents; neither a field nor a Noetherian hypothesis is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits MvPolynomial Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace.FromSections.AffineChart

variable {R S I : Type u} [CommRing R] [CommRing S]

private theorem restrict_self (Y : Scheme.{u}) (U : Y.Opens) (r : Γ(Y, U)) :
    sectionRestrict Y (show U ≤ U from le_rfl) r = r := by
  change (Y.presheaf.map (𝟙 (op U))).hom r = r
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- The original tuple, with its distinguished unit coordinate. -/
def coordinates (s : I → S) : Option I → S := fun i => i.elim 1 s

/-- The actual unit-module section morphisms of the original affine tuple. -/
def family (s : I → S) (i : Option I) :
    SheafOfModules.unit (Spec (.of S)).ringCatSheaf ⟶
      SheafOfModules.unit (Spec (.of S)).ringCatSheaf :=
  unitMul (Spec (.of S)) ((Scheme.ΓSpecIso (.of S)).inv (coordinates s i))

@[simp]
theorem family_none (s : I → S) : family s none = 𝟙 _ := by
  change unitMul (Spec (.of S)) ((Scheme.ΓSpecIso (.of S)).inv (1 : S)) = _
  rw [map_one, unitMul_one]

/-- The unit coordinate supplies generation, without assumptions on the tuple. -/
instance family_epi (s : I → S) : Epi (Sigma.desc (family s)) := by
  have h : SheafOfModules.ιFree none ≫ Sigma.desc (family s) = 𝟙 _ := by
    rw [SheafOfModules.ιFree, Sigma.ι_comp_desc, family_none]
  have : Epi (SheafOfModules.ιFree none ≫ Sigma.desc (family s)) := by
    rw [h]
    infer_instance
  exact epi_of_epi (SheafOfModules.ιFree none) (Sigma.desc (family s))

/-- The single identity frame on the entire affine scheme. -/
def frames (s : I → S) :
    SectionFrames (SheafOfModules.unit (Spec (.of S)).ringCatSheaf)
      (fun i => (SheafOfModules.unit (Spec (.of S)).ringCatSheaf).unitHomEquiv (family s i)) where
  K := PUnit.{u + 1}
  U _ := ⊤
  covers := by simp
  coordinate _ := none
  frame _ := Iso.refl _
  selected _ := by
    change (show Γ(Spec (.of S), ⊤) from
      ((SheafOfModules.unit (Spec (.of S)).ringCatSheaf).unitHomEquiv
        (family s none)).val (op ⊤)) = 1
    rw [family_none]
    rfl

@[simp]
theorem frames_coefficient (s : I → S) (i : Option I) :
    (frames s).coefficientOn PUnit.unit le_rfl i =
      (Scheme.ΓSpecIso (.of S)).inv (coordinates s i) := by
  change ((SheafOfModules.unit (Spec (.of S)).ringCatSheaf).unitHomEquiv
    (family s i)).val (op ⊤) = _
  rw [family, unitMul, Equiv.apply_symm_apply]
  change sectionRestrict (Spec (.of S)) (show ⊤ ≤ ⊤ from le_top) _ = _
  rw [restrict_self]

/-- The standard chart evaluation preserves the original base map and tuple. -/
def ringHom (φ : R →+* S) (s : I → S) : coordinateRing R (Option I) none →+* S :=
  (eval₂Hom φ s).comp (optionCoordinateRingEquivPolynomial R I).toRingHom

@[simp]
theorem ringHom_coefficient (φ : R →+* S) (s : I → S) (r : R) :
    ringHom φ s (coordinateRingCoefficient R (Option I) none r) = φ r := by
  simp [ringHom, optionCoordinateRingEquivPolynomial_coefficient]

@[simp]
theorem optionCoordinateRingEquivPolynomial_ratio (i : I) :
    optionCoordinateRingEquivPolynomial R I (coordinateRatio R (Option I) none (some i)) =
      X i := by
  classical
  change MvPolynomial.rename
    ((Equiv.optionSubtype (α := I) (β := Option I) none)
      ⟨Equiv.refl _, rfl⟩).symm
    (coordinateRingToPolynomial R (Option I) none
      (coordinateRatio R (Option I) none
        (⟨some i, Option.some_ne_none i⟩ : {j : Option I // j ≠ none}).val)) = _
  rw [coordinateRingToPolynomial_ratio, rename_X]
  rfl

@[simp]
theorem ringHom_ratio (φ : R →+* S) (s : I → S) (i : Option I) :
    ringHom φ s (coordinateRatio R (Option I) none i) = coordinates s i := by
  cases i with
  | none => simp [coordinates]
  | some i => simp [ringHom, coordinates]

/-- The literal standard affine-chart morphism, with no auxiliary field extension. -/
def map (φ : R →+* S) (s : I → S) : Spec (.of S) ⟶ ProjectiveSpace R (Option I) :=
  Spec.map (CommRingCat.ofHom (ringHom φ s)) ≫
    Proj.awayι (homogeneousSubmodule (Option I) R) (X none)
      (isHomogeneous_X R none) Nat.zero_lt_one

private theorem baseCoefficient_top (φ : R →+* S) (r : R) :
    SectionFrames.baseCoefficient (Spec.map (CommRingCat.ofHom φ)) ⊤ r =
      (Scheme.ΓSpecIso (.of S)).inv (φ r) := by
  unfold SectionFrames.baseCoefficient
  rw [RingHom.comp_apply, restrict_self]
  exact congrArg (fun f : CommRingCat.of R ⟶ Γ(Spec (.of S), ⊤) => f r)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)).symm

/-- Identification of the actual chart ring map, not just its induced point map. -/
theorem frames_chartRingHom (φ : R →+* S) (s : I → S) :
    (frames s).chartRingHom (Spec.map (CommRingCat.ofHom φ)) PUnit.unit le_rfl =
      (Scheme.ΓSpecIso (.of S)).inv.hom.comp (ringHom φ s) := by
  let f := (frames s).chartRingHom (Spec.map (CommRingCat.ofHom φ)) PUnit.unit le_rfl
  let g := (Scheme.ΓSpecIso (.of S)).inv.hom.comp (ringHom φ s)
  have h : f.comp (polynomialToCoordinateRing R (Option I) none) =
      g.comp (polynomialToCoordinateRing R (Option I) none) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change f (polynomialToCoordinateRing R (Option I) none (C r)) =
        g (polynomialToCoordinateRing R (Option I) none (C r))
      rw [polynomialToCoordinateRing_C]
      change (frames s).chartRingHom (Spec.map (CommRingCat.ofHom φ)) PUnit.unit le_rfl
        (coordinateRingCoefficient R (Option I) none r) =
          (Scheme.ΓSpecIso (.of S)).inv (ringHom φ s
            (coordinateRingCoefficient R (Option I) none r))
      exact ((frames s).chartRingHom_coefficient
        (Spec.map (CommRingCat.ofHom φ)) PUnit.unit le_rfl r).trans
          ((baseCoefficient_top φ r).trans
            (congrArg (Scheme.ΓSpecIso (.of S)).inv (ringHom_coefficient φ s r)).symm)
    · intro i
      change f (polynomialToCoordinateRing R (Option I) none (X i)) =
        g (polynomialToCoordinateRing R (Option I) none (X i))
      rw [polynomialToCoordinateRing_X]
      change (frames s).chartRingHom (Spec.map (CommRingCat.ofHom φ)) PUnit.unit le_rfl
        (coordinateRatio R (Option I) none i.val) =
          (Scheme.ΓSpecIso (.of S)).inv (ringHom φ s
            (coordinateRatio R (Option I) none i.val))
      exact ((frames s).chartRingHom_ratio
        (Spec.map (CommRingCat.ofHom φ)) PUnit.unit le_rfl i.val).trans
          ((frames_coefficient s i.val).trans
            (congrArg (Scheme.ΓSpecIso (.of S)).inv (ringHom_ratio φ s i.val)).symm)
  have h' := congrArg (fun k => k.comp (coordinateRingToPolynomial R (Option I) none)) h
  simpa only [RingHom.comp_assoc, polynomialToCoordinateRing_comp_coordinateRingToPolynomial,
    RingHom.comp_id] using h'

/-- The one-chart section construction is the original standard affine-chart map. -/
theorem frames_map (φ : R →+* S) (s : I → S) :
    (frames s).map (Spec.map (CommRingCat.ofHom φ)) = map φ s := by
  apply (frames s).sourceOpenCover.hom_ext
  intro k
  cases k
  change (⊤ : (Spec (.of S)).Opens).ι ≫
    (frames s).map (Spec.map (CommRingCat.ofHom φ)) =
      (⊤ : (Spec (.of S)).Opens).ι ≫ map φ s
  refine ((frames s).ι_map (Spec.map (CommRingCat.ofHom φ)) PUnit.unit).trans ?_
  rw [SectionFrames.chartMap, frames_chartRingHom]
  change (⊤ : (Spec (.of S)).Opens).toSpecΓ ≫
      Spec.map (CommRingCat.ofHom (ringHom φ s) ≫ (Scheme.ΓSpecIso (.of S)).inv) ≫ _ = _
  rw [Spec.map_comp, Scheme.Opens.toSpecΓ_top]
  simp only [Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv_assoc, map]
  rfl

/-- The standard affine-chart map retains exactly the original structural map. -/
@[reassoc]
theorem map_toSpec (φ : R →+* S) (s : I → S) :
    map φ s ≫ toSpec R (Option I) = Spec.map (CommRingCat.ofHom φ) := by
  rw [← frames_map φ s]
  exact (frames s).map_toSpec (Spec.map (CommRingCat.ofHom φ))

/-- Ordinary finite-family `FromSections` agrees with the original affine-chart
morphism. The line-rank proof is immaterial; the section morphisms are unchanged. -/
theorem mapOfFiniteFamily_eq [Finite I] (φ : R →+* S) (s : I → S)
    (h : IsLocallyRankOne (Spec (.of S))
      (SheafOfModules.unit (Spec (.of S)).ringCatSheaf)) :
    mapOfFiniteFamily (Spec.map (CommRingCat.ofHom φ))
      (SheafOfModules.unit (Spec (.of S)).ringCatSheaf) h (family s) = map φ s := by
  trans (frames s).map (Spec.map (CommRingCat.ofHom φ))
  · apply SectionFrames.map_eq_of_iso _ _ _ (Iso.refl _)
    intro i O
    simp only [generatingSectionsOfFamily_section]
    rfl
  · exact frames_map φ s

/-- The same standard-chart map is the existing affine-presentation construction,
with evaluation at the original tuple as its polynomial presentation. -/
theorem map_eq_affinePresentationImmersion [Algebra R S] (s : I → S) :
    map (algebraMap R S) s = affinePresentationImmersion R S I (aeval s) := by
  rw [affinePresentationImmersion_eq]
  rfl

end AlgebraicGeometry.ProjectiveSpace.FromSections.AffineChart
