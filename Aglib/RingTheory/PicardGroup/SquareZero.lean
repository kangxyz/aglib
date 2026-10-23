/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.SquareZeroMorphisms
public import Aglib.Algebra.Category.ModuleCat.SquareZeroProjective
public import Mathlib.RingTheory.PicardGroup

/-!
# Invertible modules over a square-zero extension

An invertible module lifts across a surjective square-zero ring map. Lift
the module and a tensor inverse as finite projectives, then lift the original
evaluation isomorphism. The original homomorphism of ring Picard groups is
bijective. This is an affine result; general scheme Picard restriction need
not be injective across a nilpotent thickening.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory
open scoped TensorProduct

universe u

namespace ModuleCat

variable {R S : Type u} [CommRing R] [CommRing S]
  (f : R →+* S) (hsurj : Function.Surjective f) (hf : RingHom.ker f ^ 2 = ⊥)

include hsurj hf

/-- A projective module whose original square-zero reduction is invertible
is itself invertible. Finiteness is a consequence, rather than a premise. -/
theorem invertible_of_extendScalars_of_projective (M : ModuleCat.{u} R)
    [Module.Projective R M] [Module.Invertible S ((extendScalars f).obj M)] :
    Module.Invertible R M := by
  let := f.toAlgebra
  let D : ModuleCat.{u} S := ModuleCat.of S (Module.Dual S ((extendScalars f).obj M))
  obtain ⟨N, hfin, hproj, ⟨e⟩⟩ := exists_finite_projective_lift_of_square_zero f hsurj hf D
  let := hfin
  let := hproj
  let T : ModuleCat.{u} R := ModuleCat.of R (N ⊗[R] M)
  let U : ModuleCat.{u} R := ModuleCat.of R R
  let eT : (extendScalars f).obj T ≅ (extendScalars f).obj U :=
    (TensorProduct.AlgebraTensorModule.distribBaseChange R S N M).toModuleIso ≪≫
      (TensorProduct.congr e.toLinearEquiv
        (LinearEquiv.refl S ((extendScalars f).obj M))).toModuleIso ≪≫
      (Module.Invertible.linearEquiv S ((extendScalars f).obj M)).toModuleIso ≪≫
      (TensorProduct.AlgebraTensorModule.rid R S S).symm.toModuleIso
  obtain ⟨g, hg⟩ := extendScalars_map_surjective_of_projective f hsurj T U eT.hom
  change (extendScalars f).map g = eT.hom at hg
  have : IsIso ((extendScalars f).map g) := by rw [hg]; infer_instance
  have : IsIso g := isIso_of_extendScalars_map_isIso_of_projective f hsurj hf g
  exact Module.Invertible.right (asIso g).toLinearEquiv

/-- Every actual invertible module lifts, with an actual isomorphism from
its original scalar extension to the specified module. -/
theorem exists_invertible_lift_of_square_zero (M : ModuleCat.{u} S)
    [Module.Invertible S M] :
    ∃ N : ModuleCat.{u} R, Module.Invertible R N ∧
      Nonempty ((extendScalars f).obj N ≅ M) := by
  obtain ⟨N, _, hproj, ⟨e⟩⟩ := exists_finite_projective_lift_of_square_zero f hsurj hf M
  let := hproj
  have : Module.Invertible S ((extendScalars f).obj N) :=
    Module.Invertible.congr e.symm.toLinearEquiv
  exact ⟨N, invertible_of_extendScalars_of_projective f hsurj hf N, ⟨e⟩⟩

end ModuleCat

namespace CommRing.Pic

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The original map on ring Picard groups is bijective across every
surjective square-zero extension. -/
theorem mapRingHom_bijective_of_square_zero (f : R →+* S)
    (hsurj : Function.Surjective f) (hf : RingHom.ker f ^ 2 = ⊥) :
    Function.Bijective (mapRingHom f) := by
  let := f.toAlgebra
  constructor
  · intro a b hab
    have hab' : Pic.mk S (S ⊗[R] a) = Pic.mk S (S ⊗[R] b) := hab
    obtain ⟨e⟩ := mk_eq_mk_iff.mp hab'
    obtain ⟨e', _⟩ := ModuleCat.exists_iso_lift_of_square_zero f hsurj hf
      (ModuleCat.of R a) (ModuleCat.of R b) e.toModuleIso
    exact ext_iff.mpr ⟨e'.toLinearEquiv⟩
  · intro b
    obtain ⟨N, hN, ⟨e⟩⟩ := ModuleCat.exists_invertible_lift_of_square_zero f hsurj hf
      (ModuleCat.of S b)
    let := hN
    refine ⟨Pic.mk R N, mk_eq_iff.mpr ⟨?_⟩⟩
    exact TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S)
      (mk.linearEquiv R N) ≪≫ₗ e.toLinearEquiv

/-- The equivalence retains the original forward homomorphism on Picard groups. -/
def squareZeroEquiv (f : R →+* S) (hsurj : Function.Surjective f)
    (hf : RingHom.ker f ^ 2 = ⊥) : Pic R ≃* Pic S :=
  MulEquiv.ofBijective (mapRingHom f) (mapRingHom_bijective_of_square_zero f hsurj hf)

@[simp]
theorem squareZeroEquiv_apply (f : R →+* S) (hsurj : Function.Surjective f)
    (hf : RingHom.ker f ^ 2 = ⊥) (a : Pic R) :
    squareZeroEquiv f hsurj hf a = mapRingHom f a := rfl

end CommRing.Pic
