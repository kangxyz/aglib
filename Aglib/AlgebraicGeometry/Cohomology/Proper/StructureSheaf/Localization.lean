/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.LocalProperties.Exactness
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Localization inputs for structure-map bijectivity

Two general facts used to pass from local rings of a test scheme to its affine
opens.

* `CommRingCat.bijective_localizedModuleMap_of_isPushout`: in a pushout square of
  commutative rings whose left arrow is a localization at a prime `P`, bijectivity of
  the right-hand arrow gives bijectivity of the top arrow after localization at `P`
  (as a module map over the source ring). The proof uses native
  `CommRingCat.isPushout_iff_isPushout`, `isLocalizedModule_iff_isBaseChange` and
  `IsLocalizedModule.map_iso_commute`.
* `AlgebraicGeometry.Scheme.flat_fromSpecStalk`: the canonical morphism
  `Spec O_{X,x} ⟶ X` is flat, since it is a localization followed by an affine open
  immersion.

Intended owners: the ring statement belongs with Mathlib/Aglib `RingTheory`
localization, the scheme statement with `AlgebraicGeometry.Stalk`.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace CommRingCat

/-- In a pushout square of commutative rings whose left arrow is a localization at a
prime `P`, bijectivity of the opposite arrow gives bijectivity of the top arrow after
localization at `P`. The top ring is a module over the source through the top arrow. -/
theorem bijective_localizedModuleMap_of_isPushout {A B C D : CommRingCat.{u}}
    {ψ : A ⟶ C} {ι : A ⟶ B} {κ : C ⟶ D} {ψ' : B ⟶ D} (H : IsPushout ψ ι κ ψ')
    (P : Ideal A) [P.IsPrime]
    (hP : letI := ι.hom.toAlgebra; IsLocalization.AtPrime B P)
    (hψ' : Function.Bijective ψ') :
    let := ψ.hom.toAlgebra
    Function.Bijective (LocalizedModule.map P.primeCompl (Algebra.linearMap A C)) := by
  let := ψ.hom.toAlgebra
  let := ι.hom.toAlgebra
  let := κ.hom.toAlgebra
  let := ψ'.hom.toAlgebra
  let : Algebra A D := (ψ ≫ κ).hom.toAlgebra
  have hw : ∀ a : A, κ (ψ a) = ψ' (ι a) := fun a => by
    simpa using ConcreteCategory.congr_hom H.w a
  have : IsScalarTower A C D := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower A B D := IsScalarTower.of_algebraMap_eq (fun a => hw a)
  have hPO : Algebra.IsPushout A C B D := CommRingCat.isPushout_iff_isPushout.mp H
  have : IsLocalization P.primeCompl B := hP
  have hκ : IsLocalizedModule P.primeCompl (IsScalarTower.toAlgHom A C D).toLinearMap :=
    (isLocalizedModule_iff_isBaseChange P.primeCompl B _).mpr hPO.symm.out
  let F := Algebra.linearMap A C
  let ιl := Algebra.linearMap A B
  let κl := (IsScalarTower.toAlgHom A C D).toLinearMap
  let ψl := (IsScalarTower.toAlgHom A B D).toLinearMap
  have hmap : IsLocalizedModule.map P.primeCompl ιl κl F = ψl := by
    apply IsLocalizedModule.ext P.primeCompl ιl (IsLocalizedModule.map_units κl)
    rw [IsLocalizedModule.map_comp]
    apply LinearMap.ext
    intro a
    exact hw a
  have hb : Function.Bijective (IsLocalizedModule.map P.primeCompl ιl κl F) := by
    rw [hmap]
    exact hψ'
  have hc := IsLocalizedModule.map_iso_commute P.primeCompl ιl κl F
  have e : (IsLocalizedModule.map P.primeCompl (LocalizedModule.mkLinearMap P.primeCompl A)
      (LocalizedModule.mkLinearMap P.primeCompl C) F : _ → _) =
      (IsLocalizedModule.iso P.primeCompl κl).symm ∘
        (IsLocalizedModule.map P.primeCompl ιl κl F) ∘ (IsLocalizedModule.iso P.primeCompl ιl) := by
    funext x
    have hx := congrArg (fun L => L x) hc
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at hx
    rw [Function.comp_apply, Function.comp_apply, hx, LinearEquiv.symm_apply_apply]
  change Function.Bijective (IsLocalizedModule.map P.primeCompl
    (LocalizedModule.mkLinearMap P.primeCompl A) (LocalizedModule.mkLinearMap P.primeCompl C) F)
  rw [e]
  exact (LinearEquiv.bijective _).comp (hb.comp (LinearEquiv.bijective _))

end CommRingCat

namespace AlgebraicGeometry.Scheme

/-- The canonical morphism from the spectrum of a local ring of a scheme is flat. -/
instance flat_fromSpecStalk (X : Scheme.{u}) (x : X) : Flat (X.fromSpecStalk x) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  rw [← hV.fromSpecStalk_eq_fromSpecStalk hxV, IsAffineOpen.fromSpecStalk]
  have : Flat (Spec.map (X.presheaf.germ V x hxV)) := by
    rw [Flat.SpecMap_iff]
    let := (X.presheaf.germ V x hxV).hom.toAlgebra
    have := hV.isLocalization_stalk ⟨x, hxV⟩
    exact IsLocalization.flat (X.presheaf.stalk x) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl
  infer_instance

end AlgebraicGeometry.Scheme
