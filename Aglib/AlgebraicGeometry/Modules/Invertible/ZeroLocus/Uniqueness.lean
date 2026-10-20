/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.ZeroLocus
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Aglib.AlgebraicGeometry.IdealSheaf.Modules

/- Interface migration basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original mathematical and construction source identities are retained. -/
/-!
# Actual zero-scheme invariance and recovery of a closed immersion

The image ideal is unchanged by precomposition with a module isomorphism
or postcomposition with an automorphism of the structure module. The latter
is proved sectionwise by linearity and its actual inverse. The sectionwise
image of the actual kernel inclusion is precisely the morphism kernel ideal.
The native ideal-subscheme functor and native source-to-image isomorphism
therefore recover the given closed immersion with an explicit inclusion
square. No geometric uniqueness or Abel inverse theorem is a premise.

Manuscript application: K2-018 `prop:k2018-arithmetic-characters` and
`lem:k2018-geometric-exact-order`, mathematical-source revision
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Frozen engineering basis: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.
-/

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Divisors.Relative.Uniqueness` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`864b76f0bf41d7352d0b2c7398df8e61ed9666a489bd02b02babb0dbb4c49638`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Hom
namespace AlgebraicGeometry.Scheme.Modules.Hom
universe u
variable {X : Scheme.{u}} {M N : X.Modules}
variable (e : M ≅ N) (χ : N ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf))
theorem sectionImageIdeal_precomp_iso (U : X.Opens) :
    sectionImageIdeal (e.hom ≫ χ) U = sectionImageIdeal χ U := by
  ext a
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨e.hom.val.app (op U) m, hm⟩
  · rintro ⟨n, hn⟩
    refine ⟨e.inv.val.app (op U) n, ?_⟩
    change χ.val.app (op U) (e.hom.val.app (op U) (e.inv.val.app (op U) n)) = a
    have he := congrArg (fun k : N ⟶ N ↦ k.val.app (op U) n) e.inv_hom_id
    change e.hom.val.app (op U) (e.inv.val.app (op U) n) = n at he
    rw [he]
    exact hn

theorem imageIdealData_precomp_iso : imageIdealData (e.hom ≫ χ) = imageIdealData χ := by
  unfold imageIdealData
  congr 1
  funext U
  exact sectionImageIdeal_precomp_iso e χ U

variable (v : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ≅
  (show X.Modules from SheafOfModules.unit X.ringCatSheaf))
theorem sectionImageIdeal_postcomp_unit_iso
    (φ : M ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf)) (U : X.Opens) :
    sectionImageIdeal (φ ≫ v.hom) U = sectionImageIdeal φ U := by
  let q : M.val.obj (op U) →ₗ[Γ(X,U)] Γ(X,U) := (φ.val.app (op U)).hom
  let v₁ : Γ(X,U) →ₗ[Γ(X,U)] Γ(X,U) := (v.hom.val.app (op U)).hom
  let v₂ : Γ(X,U) →ₗ[Γ(X,U)] Γ(X,U) := (v.inv.val.app (op U)).hom
  have hs (w : Γ(X,U) →ₗ[Γ(X,U)] Γ(X,U)) (b : Γ(X,U)) : w b = w 1 * b := by
    have hh := w.map_smul b (1 : Γ(X,U))
    simpa only [smul_eq_mul, mul_one, mul_comm] using hh
  ext a
  constructor
  · rintro ⟨m, rfl⟩
    refine ⟨v₁ 1 • m, ?_⟩
    change q (v₁ 1 • m) = v₁ (q m)
    rw [q.map_smul]
    exact (hs v₁ (q m)).symm
  · rintro ⟨m, rfl⟩
    refine ⟨v₂ 1 • m, ?_⟩
    change v₁ (q (v₂ 1 • m)) = q m
    rw [q.map_smul]
    change v₁ (v₂ 1 * q m) = q m
    rw [← hs v₂]
    exact congrArg (fun z : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ↦ z.val.app (op U) (q m))
          v.inv_hom_id

theorem imageIdealData_postcomp_unit_iso
    (φ : M ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf)) :
    imageIdealData (φ ≫ v.hom) = imageIdealData φ := by
  unfold imageIdealData
  congr 1
  funext U
  exact sectionImageIdeal_postcomp_unit_iso v φ U

variable {φ : M ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf)}
variable {ψ : N ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf)}
def zeroOverIso_of_imageIdealData_eq (h : imageIdealData φ = imageIdealData ψ) :
    Over.mk (zeroInclusion φ) ≅ Over.mk (zeroInclusion ψ) :=
  (Scheme.IdealSheafData.subschemeFunctor X).mapIso (eqToIso (congrArg op h))

def zeroSchemeIso_of_imageIdealData_eq (h : imageIdealData φ = imageIdealData ψ) :
    zeroScheme φ ≅ zeroScheme ψ :=
  (Over.forget X).mapIso (zeroOverIso_of_imageIdealData_eq h)

@[reassoc (attr := simp)] theorem zeroSchemeIso_of_imageIdealData_eq_inclusion
    (h : imageIdealData φ = imageIdealData ψ) :
    (zeroSchemeIso_of_imageIdealData_eq h).hom ≫ zeroInclusion ψ = zeroInclusion φ :=
  Over.w (zeroOverIso_of_imageIdealData_eq h).hom

variable {D : Scheme.{u}} (i : D ⟶ X)
theorem sectionImageIdeal_idealInclusion (U : X.Opens) :
    sectionImageIdeal (idealInclusion i) U = RingHom.ker (i.app U).hom := by
  ext a
  constructor
  · rintro ⟨m, rfl⟩
    change (idealInclusion i).val.app (op U) m ∈ RingHom.ker (i.app U).hom
    rw [← idealSectionsEquiv_val]
    exact (idealSectionsEquiv i U m).property
  · intro ha
    refine ⟨(idealSectionsEquiv i U).symm ⟨a, ha⟩, ?_⟩
    change (idealInclusion i).val.app (op U) ((idealSectionsEquiv i U).symm ⟨a, ha⟩) = a
    rw [← idealSectionsEquiv_val]
    exact congrArg Subtype.val ((idealSectionsEquiv i U).apply_symm_apply ⟨a, ha⟩)

theorem imageIdealData_idealInclusion : imageIdealData (idealInclusion i) = i.ker := by
  unfold imageIdealData Scheme.Hom.ker
  congr 1
  funext U
  exact sectionImageIdeal_idealInclusion i U

variable [IsClosedImmersion i]
def zeroOverIso_of_ideal_eq (h : imageIdealData φ = i.ker) :
    Over.mk (zeroInclusion φ) ≅ Over.mk i :=
  (Scheme.IdealSheafData.subschemeFunctor X).mapIso (eqToIso (congrArg op h)) ≪≫
    (Over.isoMk (asIso i.toImage) i.toImage_imageι).symm

def zeroIdealInclusionIso : zeroScheme (idealInclusion i) ≅ D :=
  (Over.forget X).mapIso (zeroOverIso_of_ideal_eq i (imageIdealData_idealInclusion i))

@[reassoc (attr := simp)] theorem zeroIdealInclusionIso_inclusion :
    (zeroIdealInclusionIso i).hom ≫ i = zeroInclusion (idealInclusion i) :=
  Over.w (zeroOverIso_of_ideal_eq i (imageIdealData_idealInclusion i)).hom

def zeroSchemeIso_of_ideal_square
    (e : (show X.Modules from idealModule i) ≅ M)
    (h : e.hom ≫ φ = idealInclusion i) : zeroScheme φ ≅ D := by
  have he : imageIdealData φ = i.ker := by
    rw [← imageIdealData_precomp_iso e φ, h, imageIdealData_idealInclusion]
  exact (Over.forget X).mapIso (zeroOverIso_of_ideal_eq i he)

@[reassoc (attr := simp)] theorem zeroSchemeIso_of_ideal_square_inclusion
    (e : (show X.Modules from idealModule i) ≅ M)
    (h : e.hom ≫ φ = idealInclusion i) :
    (zeroSchemeIso_of_ideal_square i e h).hom ≫ i = zeroInclusion φ := by
  exact Over.w (zeroOverIso_of_ideal_eq i
    (by rw [← imageIdealData_precomp_iso e φ, h, imageIdealData_idealInclusion])).hom
end AlgebraicGeometry.Scheme.Modules.Hom
