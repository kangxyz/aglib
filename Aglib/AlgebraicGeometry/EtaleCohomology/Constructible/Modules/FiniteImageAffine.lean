/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FiniteImageRadicialNoetherian
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FiniteEtaleImage
public import Aglib.AlgebraicGeometry.Morphisms.Finite.GenericRadicialEtaleAffine

/-! # Actual generic constructibility of finite images on affine schemes

The genuine geometric factorization is applied to the original finite map.
Its radicial image is constructible over its Noetherian intermediate scheme;
the subsequent finite etale image and original finite base change identify
the result with the original direct image restricted to the produced open.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

/-- A finite image with reduced affine source is genuinely constructible on
an actual nonempty affine open of the integral Noetherian affine target. -/
theorem exists_nonempty_open_constructible_finiteImage_of_reduced_source
    (R : Type r) [CommRing R] {Y X : Scheme.{u}}
    [IsAffine Y] [IsReduced Y] [IsAffine X] [IsIntegral X] [IsNoetherian X]
    (f : Y ⟶ X) [IsFinite f] (F : ModuleSheaf R Y) (hF : IsConstructible F) :
    ∃ (U : Scheme.{u}) (j : U ⟶ X), IsAffine U ∧ IsOpenImmersion j ∧ Nonempty U ∧
      IsConstructible ((moduleInverseImage R j).obj ((moduleDirectImage R f).obj F)) := by
  obtain ⟨U, hUa, hU, B, r, g, hr, hs, hu, hg, hge, hcomp⟩ :=
    Scheme.FiniteGenericFactorization.exists_affine_open_finite_radicial_etale_factorization f
  let : IsAffine U.toScheme := hUa
  let : IsFinite r := hr
  let : Surjective r := hs
  let : UniversallyInjective r := hu
  let : IsFinite g := hg
  let : Etale g := hge
  let : IsLocallyNoetherian B := LocallyOfFiniteType.isLocallyNoetherian g
  let : CompactSpace B := QuasiCompact.compactSpace_of_compactSpace g
  let : IsNoetherian B := ⟨⟩
  let p := pullback.fst f U.ι
  let FU := (moduleInverseImage R p).obj F
  have hrad := isConstructible_finiteRadicialDirectImage_of_noetherian R r
    (isConstructible_pullback p hF)
  have het := isConstructible_finiteEtaleDirectImage g hrad
  have htotal : IsConstructible ((moduleDirectImage R (pullback.snd f U.ι)).obj FU) := by
    let e := (moduleDirectImageCompIso R g r).app FU ≪≫
      eqToIso (congrArg (fun a => (moduleDirectImage R a).obj FU) hcomp)
    exact (isConstructible_iff_of_iso e).mp het
  refine ⟨U, U.ι, hUa, inferInstance, ⟨⟨genericPoint X, hU⟩⟩, ?_⟩
  exact (isConstructible_iff_of_iso
    ((finiteImageBaseChangeIso R f (pullback.snd f U.ι) U.ι p
      (IsPullback.of_hasPullback f U.ι)).app F)).mpr htotal

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
