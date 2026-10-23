/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Twisting
public import Aglib.AlgebraicGeometry.ProjectiveSpace.HomogeneousSections
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.RightUnit

/-!
# Base change of homogeneous polynomial sections

For a ring map `φ : R →+* S` and `π = ProjectiveSpace.map φ ι : P_S ⟶ P_R`, a global section of
`O_R(n)` pulls back to a global section of `π^* O_R(n)`, through the unit `η` of the
pullback-pushforward adjunction at `⊤`. Under the base-change isomorphism
`twistingPullbackIso φ ι n : π^* O_R(n) ≅ O_S(n)`, the pullback of the section of a homogeneous
polynomial `p` is the section of the polynomial with coefficients mapped by `φ`
(`twistingPullbackIso_hom_unit_homogeneousSection`):
`(twistingPullbackIso φ ι n).hom (η (homogeneousSection R ι n p)) =
homogeneousSection S ι n ((gradedMap φ).gradedAddHom n p)`, with the coefficient map
`(gradedMap φ).gradedAddHom n : R[x]_n → S[x]_n` of `RingTheory/MvPolynomial/GradedMap`.

The proof is a chart computation. Sections of `O_S(n)` are determined by their frame coefficients
on the standard charts (`twistingSectionsEquiv`); the pulled-back frame `Xᵢ^n` goes to the frame
`Xᵢ^n` (`twistingPullbackIso_hom_generator`), and the coefficient `p / Xᵢ^n` of the section of
`p` goes to `φ(p) / Xᵢ^n` under `π` (`appLE_homogeneousChartSection`, from
`awayToSection_comp_appLE_map` of `ProjectiveSpace/BaseChange/Twisting`).

The unit twist `O(n) ⊗ 𝒪` is handled by `twistingTensorPullbackIso_rightUnitor`: the comparison
`twistingTensorPullbackIso φ ι n 𝒪`, followed by `pullbackUnitIso` on the second factor, matches
`twistingPullbackIso` through the right unitors (`pullbackTensorMap_rightUnit`).
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite MonoidalCategory MvPolynomial HomogeneousLocalization
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace

variable {R S : Type u} [CommRing R] [CommRing S]

-- `Away.map_mk` must match the coefficient map through its graded and ring-hom coercions.
set_option backward.isDefEq.respectTransparency false in
/-- The chart function `p / Xᵢ^n` pulls back to `φ(p) / Xᵢ^n` under `ProjectiveSpace.map φ ι`. -/
theorem appLE_homogeneousChartSection (φ : R →+* S) (ι : Type u) (n : ℕ)
    (p : homogeneousSubmodule ι R n) (i : ι)
    (e : coordinateOpen S ι i ≤ map φ ι ⁻¹ᵁ coordinateOpen R ι i) :
    ((map φ ι).appLE (coordinateOpen R ι i) (coordinateOpen S ι i) e).hom
        (homogeneousChartSection R ι n p i) =
      homogeneousChartSection S ι n ((gradedMap (ι := ι) φ).gradedAddHom n p) i := by
  have hs : X i ∈ homogeneousSubmodule ι R 1 := isHomogeneous_X R i
  have hV : coordinateOpen S ι i ≤
      Proj.basicOpen (homogeneousSubmodule ι S) (gradedMap φ (X i)) := by
    change _ ≤ Proj.basicOpen (homogeneousSubmodule ι S) (MvPolynomial.map φ (X i))
    rw [map_X]
    exact le_rfl
  have h₁ := congrArg (fun g => g.hom (homogeneousChartSection R ι n p i))
    (Scheme.Hom.appLE_map (map φ ι)
      (le_rfl : Proj.basicOpen (homogeneousSubmodule ι S) (gradedMap φ (X i)) ≤
        map φ ι ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule ι R) (X i)) (homOfLE hV).op)
  have h₃ := ConcreteCategory.congr_hom (awayToSection_comp_appLE_map φ ι (X i) hs)
    (homogeneousChartFraction R ι n p i)
  refine h₁.symm.trans ?_
  change sectionRestrict (ProjectiveSpace S ι) hV
      (((Proj.awayToSection (homogeneousSubmodule ι R) (X i) ≫
        (map φ ι).appLE (Proj.basicOpen (homogeneousSubmodule ι R) (X i))
          (Proj.basicOpen (homogeneousSubmodule ι S) (gradedMap φ (X i))) le_rfl).hom)
        (homogeneousChartFraction R ι n p i)) = _
  rw [h₃]
  change sectionRestrict (ProjectiveSpace S ι) hV
      ((Proj.awayToSection (homogeneousSubmodule ι S) (gradedMap φ (X i))).hom
        (Away.map (gradedMap φ) (X i) (homogeneousChartFraction R ι n p i))) =
    sectionRestrict (ProjectiveSpace S ι) le_rfl
      ((Proj.awayToSection (homogeneousSubmodule ι S) (X i)).hom
        (homogeneousChartFraction S ι n ((gradedMap (ι := ι) φ).gradedAddHom n p) i))
  rw [homogeneousChartFraction, homogeneousChartFraction, Away.map_mk]
  exact sectionRestrict_awayToSection_congr ι (by simp) rfl _ _ _ _ hV _

-- Module sections over `Γ(P_S, V)` are presented through the sheaf of rings, and the unit of the
-- adjunction is linear for the pushed-forward module structure.
set_option backward.isDefEq.respectTransparency false in
/-- **Pullback of a homogeneous polynomial section**: under `twistingPullbackIso φ ι n`, the
pullback (adjunction unit at `⊤`) of the section of `p` is the section of `φ(p)`. -/
theorem twistingPullbackIso_hom_unit_homogeneousSection (φ : R →+* S) (ι : Type u) (n : ℕ)
    (p : homogeneousSubmodule ι R n) :
    (twistingPullbackIso φ ι n).hom.val.app (op ⊤)
        (((Scheme.Modules.pullbackPushforwardAdjunction (map φ ι)).unit.app
          (twistingSheaf R ι n)).val.app (op ⊤) (homogeneousSection R ι n p)) =
      homogeneousSection S ι n ((gradedMap (ι := ι) φ).gradedAddHom n p) := by
  let M := twistingSheaf R ι (n : ℤ)
  let P := (Scheme.Modules.pullback (map φ ι)).obj M
  let u := ((Scheme.Modules.pullbackPushforwardAdjunction (map φ ι)).unit.app M).val
  let hs := homogeneousSection R ι n p
  apply TopCat.Sheaf.eq_of_locally_eq'
    ⟨(twistingSheaf S ι n).presheaf, (twistingSheaf S ι n).isSheaf⟩
    (coordinateOpen S ι) ⊤ (fun _ => homOfLE le_top)
    (by rw [iSup_coordinateOpen_eq_top])
  intro i
  change (twistingSheaf S ι n).val.map (homOfLE le_top).op _ =
    (twistingSheaf S ι n).val.map (homOfLE le_top).op _
  apply (twistingSectionsEquiv S ι n i le_rfl).injective
  rw [homogeneousSection_local]
  have e : coordinateOpen S ι i ≤ map φ ι ⁻¹ᵁ coordinateOpen R ι i :=
    (map_preimage_coordinateOpen φ ι i).ge
  let a := homogeneousChartSection R ι n p i
  let g := twistingGenerator R ι n i (le_refl (coordinateOpen R ι i))
  have F1 : M.val.map (homOfLE (le_top : coordinateOpen R ι i ≤ ⊤)).op hs = a • g := by
    rw [← twistingSectionsEquiv_smul_generator R ι n i le_rfl
      (M.val.map (homOfLE (le_top : coordinateOpen R ι i ≤ ⊤)).op hs)]
    rw [homogeneousSection_local]
  have F3 : u.app (op (coordinateOpen R ι i))
      (M.val.map (homOfLE (le_top : coordinateOpen R ι i ≤ ⊤)).op hs) =
      P.val.map (homOfLE (le_top : map φ ι ⁻¹ᵁ coordinateOpen R ι i ≤ ⊤)).op
        (u.app (op ⊤) hs) :=
    PresheafOfModules.naturality_apply u _ hs
  have F4 : P.val.map (homOfLE (le_top : coordinateOpen S ι i ≤ ⊤)).op (u.app (op ⊤) hs) =
      P.val.map (homOfLE e).op
        (P.val.map (homOfLE (le_top : map φ ι ⁻¹ᵁ coordinateOpen R ι i ≤ ⊤)).op
          (u.app (op ⊤) hs)) :=
    PresheafOfModules.map_comp_apply P.val _ _ _
  rw [← PresheafOfModules.naturality_apply (twistingPullbackIso φ ι n).hom.val, F4, ← F3, F1]
  have F2 : u.app (op (coordinateOpen R ι i)) (a • g) =
      (map φ ι).app (coordinateOpen R ι i) a •
        (show Γ(P, map φ ι ⁻¹ᵁ coordinateOpen R ι i) from u.app (op (coordinateOpen R ι i)) g) :=
    (u.app _).hom.map_smul a g
  have F5 : P.val.map (homOfLE e).op (u.app (op (coordinateOpen R ι i)) g) =
      twistingPullbackGenerator φ ι n i (le_refl (coordinateOpen S ι i)) := rfl
  rw [F2, PresheafOfModules.map_smul, F5]
  rw [((twistingPullbackIso φ ι n).hom.val.app _).hom.map_smul, twistingPullbackIso_hom_generator,
    LinearEquiv.map_smul, twistingSectionsEquiv_generator, smul_eq_mul, mul_one]
  exact appLE_homogeneousChartSection φ ι n p i e

-- The unit module appears both as `𝟙_` and as `SheafOfModules.unit` of the sheaf of rings.
set_option backward.isDefEq.respectTransparency false in
/-- **Base change of the unit twist against the right unitors**: the comparison
`twistingTensorPullbackIso φ ι d 𝒪`, followed by `pullbackUnitIso` on the second factor, is
`twistingPullbackIso φ ι d` through the right unitors. -/
theorem twistingTensorPullbackIso_rightUnitor (φ : R →+* S) (ι : Type u) (d : ℤ) :
    (Scheme.Modules.pullback (map φ ι)).map (ρ_ (twistingSheaf R ι d)).inv ≫
        (twistingTensorPullbackIso φ ι d (𝟙_ _)).hom ≫
        (twistingSheaf S ι d ◁ (Scheme.Modules.pullbackUnitIso (map φ ι)).hom) =
      (twistingPullbackIso φ ι d).hom ≫ (ρ_ (twistingSheaf S ι d)).inv := by
  rw [twistingTensorPullbackIso_hom]
  change _ ≫ (Scheme.Modules.pullbackTensorMap _ _ _ ≫
    ((twistingPullbackIso φ ι d).hom ▷ _)) ≫ (_ ◁ (Scheme.Modules.pullbackUnitIso _).hom) = _
  rw [Category.assoc, ← whisker_exchange]
  have h := Scheme.Modules.pullbackTensorMap_rightUnit (map φ ι) (twistingSheaf R ι d)
  calc _ = ((Scheme.Modules.pullback (map φ ι)).map (ρ_ (twistingSheaf R ι d)).inv ≫
        Scheme.Modules.pullbackTensorMap _ _ (𝟙_ _) ≫
          (_ ◁ (Scheme.Modules.pullbackUnitIso _).hom)) ≫
        ((twistingPullbackIso φ ι d).hom ▷ _) := by simp only [Category.assoc]; rfl
    _ = _ := by rw [h, rightUnitor_inv_naturality]; rfl

end AlgebraicGeometry.ProjectiveSpace
