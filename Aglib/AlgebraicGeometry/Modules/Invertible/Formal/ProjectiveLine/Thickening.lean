/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.IdealPowers.ThickeningTransitions
public import Aglib.AlgebraicGeometry.IdealSheaf.Colon
public import Aglib.RingTheory.Ideal.PowerQuotientSquareZero

/-!
# Intrinsic square-zero kernels of the original thickening transitions

The literal transition between base ideal thickenings is a pullback of the
original quotient factor map. Its intrinsic kernel ideal sheaf is therefore
the inverse image of the original spectral kernel. Positive successor maps
have square-zero kernel, without any flat tensor identification.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of A)) {J K : Ideal A}

/-- The original thickening transition retains its original base structure map. -/
@[reassoc (attr := simp)]
theorem idealThickeningMap_structure (h : J ≤ K) :
    idealThickeningMap f h ≫ idealThickeningStructure f J =
      idealThickeningStructure f K ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)) :=
  Limits.pullback.lift_snd _ _ _

/-- The literal original transition is a base change of the quotient factor map. -/
theorem idealThickeningMap_isPullback (h : J ≤ K) :
    IsPullback (idealThickeningMap f h) (idealThickeningStructure f K)
      (idealThickeningStructure f J)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))) := by
  apply IsPullback.of_right _ (idealThickeningMap_structure f h)
    (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
  rw [idealThickeningMap_ι, idealThickeningBaseMap_comp]
  exact IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)))

/-- Every original thickening transition is a closed immersion. -/
instance idealThickeningMap_isClosedImmersion (h : J ≤ K) :
    IsClosedImmersion (idealThickeningMap f h) := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))) :=
    IsClosedImmersion.spec_of_surjective _ (Ideal.Quotient.factor_surjective h)
  exact MorphismProperty.of_isPullback (idealThickeningMap_isPullback f h).flip inferInstance

/-- The intrinsic kernel of the original transition is the actual inverse-image
ideal of the original quotient factor's spectral kernel. -/
theorem idealThickeningMap_ker (h : J ≤ K) :
    (idealThickeningMap f h).ker =
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))).ker.comap
        (idealThickeningStructure f J) := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))) :=
    IsClosedImmersion.spec_of_surjective _ (Ideal.Quotient.factor_surjective h)
  let H := idealThickeningMap_isPullback f h
  have he := congrArg Scheme.Hom.ker H.isoPullback_hom_fst
  rw [Scheme.Hom.ker_comp_of_isIso] at he
  exact he.symm.trans (
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))) (idealThickeningStructure f J))

private theorem square_zero_comap_of_injective {R S : Type u}
    [CommRing R] [CommRing S] (g : R →+* S) (hg : Function.Injective g)
    (I : Ideal S) (hI : I ^ 2 = ⊥) : (I.comap g) ^ 2 = ⊥ := by
  rw [pow_two]
  apply le_antisymm _ bot_le
  apply Ideal.mul_le.mpr
  intro x hx y hy
  apply Ideal.mem_bot.mpr
  apply hg
  rw [map_mul, map_zero]
  exact I.mul_eq_zero_of_mem_of_square_zero hI hx hy

/-- A square-zero ring kernel gives the intrinsic square-zero spectral kernel. -/
theorem specMap_kernel_sq {R S : CommRingCat.{u}} (g : R ⟶ S)
    (hg : RingHom.ker g.hom ^ 2 = ⊥) : (Spec.map g).ker ^ 2 = ⊥ := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  change (Spec.map g).ker.ideal ⟨⊤, isAffineOpen_top _⟩ ^ 2 = ⊥
  rw [Scheme.Hom.ker_apply]
  change RingHom.ker (Spec.map g).appTop.hom ^ 2 = ⊥
  have he : RingHom.ker (Spec.map g).appTop.hom =
      (RingHom.ker g.hom).comap (Scheme.ΓSpecIso R).hom.hom := by
    rw [RingHom.comap_ker, ← CommRingCat.hom_comp, ← Scheme.ΓSpecIso_naturality,
      CommRingCat.hom_comp]
    exact (RingHom.ker_comp_of_injective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso S).hom).injective).symm
  rw [he]
  exact square_zero_comap_of_injective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).hom).injective _ hg

/-- The actual geometric kernel is square zero whenever the original quotient
factor has square-zero ring kernel. -/
theorem idealThickeningMap_ker_sq (h : J ≤ K)
    (hker : RingHom.ker (Ideal.Quotient.factor h) ^ 2 = ⊥) :
    (idealThickeningMap f h).ker ^ 2 = ⊥ := by
  rw [idealThickeningMap_ker, ← Scheme.IdealSheafData.comap_pow,
    specMap_kernel_sq (CommRingCat.ofHom (Ideal.Quotient.factor h)) hker,
    Scheme.IdealSheafData.comap_bot]

/-- Every original positive successor map of ideal-power thickenings has
intrinsic square-zero kernel, over arbitrary schemes and arbitrary base rings. -/
theorem idealThickeningMap_powSucc_ker_sq (I : Ideal A) (n : ℕ) :
    (idealThickeningMap f (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) :
      I ^ (n + 1 + 1) ≤ I ^ (n + 1))).ker ^ 2 = ⊥ :=
  idealThickeningMap_ker_sq f _ (Ideal.Quotient.ker_factorPowSucc_sq I n)

end AlgebraicGeometry.Scheme.Modules
