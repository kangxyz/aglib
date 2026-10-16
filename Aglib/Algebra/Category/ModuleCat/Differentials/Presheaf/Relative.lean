/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.Algebra.Ring.ULift

/-!
# Universal relative differentials across different presheaf categories

For the original morphism `φ : S ⟶ F.op ⋙ R`, form the original absolute
differential presheaves, the actual pullback-adjoint differential map, and
its native cokernel. This represents the existing `Derivation φ` interface.
The native presheaf pullback adjunction is the only size-dependent input;
it already exists for same-universe small categories, including scheme opens.
The identity-functor comparison retains the original universal derivation
of the native `relativeDifferentials'` object.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

universe u v₁ v₂ u₁ u₂

namespace PresheafOfModulesOfCommRing.DifferentialsConstruction

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- The canonical integer constants, raised only to the coefficient-ring universe. -/
def integerConstants (R : Dᵒᵖ ⥤ CommRingCat.{u}) :
    (Functor.const Dᵒᵖ).obj (CommRingCat.of (ULift.{u} ℤ)) ⟶ R where
  app X := CommRingCat.ofHom ((Int.castRingHom (R.obj X)).comp ULift.ringEquiv.toRingHom)
  naturality X Y f := by
    ext a
    exact (map_intCast (R.map f).hom a.down).symm

/-- Absolute differentials are the native differential presheaf relative to integer constants. -/
abbrev absoluteDifferentials (R : Dᵒᵖ ⥤ CommRingCat.{u}) :
    PresheafOfModulesOfCommRing.{u} R := relativeDifferentials' (integerConstants R)

/-- The original absolute universal derivation. -/
abbrev absoluteDerivation (R : Dᵒᵖ ⥤ CommRingCat.{u}) :
    (absoluteDifferentials R).Derivation' (integerConstants R) := derivation' (integerConstants R)

variable {F : C ⥤ D} {S : Cᵒᵖ ⥤ CommRingCat.{u}} {R : Dᵒᵖ ⥤ CommRingCat.{u}}

/-- Every native relative derivation is an absolute derivation with the identical values. -/
def absoluteOfRelative {φ : S ⟶ F.op ⋙ R} {M : PresheafOfModulesOfCommRing.{u} R}
    (d : M.Derivation φ) : M.Derivation' (integerConstants R) where
  d := d.d
  d_mul := d.d_mul
  d_map := d.d_map
  d_app {X} a := by
    change d.d (a.down : R.obj X) = 0
    rw [← zsmul_one, map_zsmul, d.d_one, smul_zero]

/-- The native absolute differential map associated to a relative derivation. -/
def absoluteDesc {φ : S ⟶ F.op ⋙ R} {M : PresheafOfModulesOfCommRing.{u} R}
    (d : M.Derivation φ) : absoluteDifferentials R ⟶ M :=
  (isUniversal' (integerConstants R)).desc (absoluteOfRelative d)

/-- Absolute descent evaluates on the original absolute differential as the given derivation. -/
@[simp]
theorem absoluteDesc_d {φ : S ⟶ F.op ⋙ R} {M : PresheafOfModulesOfCommRing.{u} R}
    (d : M.Derivation φ) (X : Dᵒᵖ) (a : R.obj X) :
    (absoluteDesc d).app X ((absoluteDerivation R).d a) = d.d a :=
  Derivation.congr_d ((isUniversal' (integerConstants R)).fac (absoluteOfRelative d)) a

variable (φ : S ⟶ F.op ⋙ R)

/-- Pullback of ring sections followed by the original absolute differential. -/
def absolutePushforwardDerivation :
    ((pushforward φ).obj (absoluteDifferentials R)).Derivation' (integerConstants S) where
  d {X} := (absoluteDerivation R).d.comp (φ.app X).hom.toAddMonoidHom
  d_mul {X} a b :=
    (congrArg (absoluteDerivation R).d ((φ.app X).hom.map_mul a b)).trans
      ((absoluteDerivation R).d_mul _ _)
  d_map {X Y} f a := by
    have h : φ.app Y (S.map f a) = R.map (F.op.map f) (φ.app X a) :=
      ConcreteCategory.congr_hom (φ.naturality f) a
    exact (congrArg (absoluteDerivation R).d h).trans ((absoluteDerivation R).d_map _ _)
  d_app {X} a := by
    change (absoluteDerivation R).d (φ.app X (a.down : S.obj X)) = 0
    rw [map_intCast (φ.app X).hom, ← zsmul_one, map_zsmul,
      (absoluteDerivation R).d_one, smul_zero]

/-- The original absolute differential map on the pushforward side of the native adjunction. -/
def absolutePushforwardMap : absoluteDifferentials S ⟶
    (pushforward φ).obj (absoluteDifferentials R) :=
  (isUniversal' (integerConstants S)).desc (absolutePushforwardDerivation φ)

@[simp]
theorem absolutePushforwardMap_d (X : Cᵒᵖ) (a : S.obj X) :
    (absolutePushforwardMap φ).app X ((absoluteDerivation S).d a) =
      (absoluteDerivation R).d (φ.app X a) :=
  Derivation.congr_d ((isUniversal' (integerConstants S)).fac
    (absolutePushforwardDerivation φ)) a

variable [(pushforward.{u} φ).IsRightAdjoint]

/-- The actual pullback-adjoint absolute differential map whose cokernel is relative. -/
def absolutePullbackMap :
    (pullback φ).obj (absoluteDifferentials S) ⟶ absoluteDifferentials R :=
  ((pullbackPushforwardAdjunction φ).homEquiv _ _).symm (absolutePushforwardMap φ)

/-- The adjoint is exactly the original map on absolute differentials. -/
@[simp]
theorem absolutePullbackMap_adjoint :
    (pullbackPushforwardAdjunction φ).homEquiv _ _ (absolutePullbackMap φ) =
      absolutePushforwardMap φ := Equiv.apply_symm_apply _ _

/-- An absolute differential map factors through the relative cokernel exactly when it
annihilates the original base sections. -/
theorem absolutePullbackMap_comp_eq_zero_iff {M : PresheafOfModulesOfCommRing.{u} R}
    (k : absoluteDifferentials R ⟶ M) :
    absolutePullbackMap φ ≫ k = 0 ↔
      ∀ (X : Cᵒᵖ) (a : S.obj X),
        k.app (F.op.obj X) ((absoluteDerivation R).d (φ.app X a)) = 0 := by
  let A := pullbackPushforwardAdjunction φ
  have hz : A.homEquiv (absoluteDifferentials S) M 0 = 0 := by
    rw [Adjunction.homEquiv_unit]
    have h : (pushforward φ).map
        (0 : (pullback φ).obj (absoluteDifferentials S) ⟶ M) = 0 := by
      ext X x
      rfl
    rw [h, HasZeroMorphisms.comp_zero]
  have he : A.homEquiv (absoluteDifferentials S) M (absolutePullbackMap φ ≫ k) =
      absolutePushforwardMap φ ≫ (pushforward φ).map k := by
    rw [A.homEquiv_naturality_right, absolutePullbackMap_adjoint]
  constructor
  · intro h X a
    have hk : absolutePushforwardMap φ ≫ (pushforward φ).map k = 0 := by
      rw [← he, h, hz]
    have hk' := congrArg (fun t => t.app X ((absoluteDerivation S).d a)) hk
    change k.app (F.op.obj X)
      ((absolutePushforwardMap φ).app X ((absoluteDerivation S).d a)) = 0 at hk'
    rwa [absolutePushforwardMap_d] at hk'
  · intro h
    apply (A.homEquiv (absoluteDifferentials S) M).injective
    rw [he, hz]
    apply (isUniversal' (integerConstants S)).postcomp_injective
    ext X a
    change k.app (F.op.obj X)
      ((absolutePushforwardMap φ).app X ((absoluteDerivation S).d a)) = 0
    rw [absolutePushforwardMap_d]
    exact h X a

/-- The relative differential presheaf is the native cokernel of the original differential map. -/
def relativeDifferentials : PresheafOfModulesOfCommRing.{u} R :=
  cokernel (absolutePullbackMap φ)

/-- The original absolute derivation followed by the actual cokernel projection. -/
def derivation : (relativeDifferentials φ).Derivation φ where
  d := ((absoluteDerivation R).postcomp (cokernel.π (absolutePullbackMap φ))).d
  d_mul := ((absoluteDerivation R).postcomp (cokernel.π (absolutePullbackMap φ))).d_mul
  d_map := ((absoluteDerivation R).postcomp (cokernel.π (absolutePullbackMap φ))).d_map
  d_app {X} a :=
    (absolutePullbackMap_comp_eq_zero_iff φ (cokernel.π (absolutePullbackMap φ))).mp
      (cokernel.condition (absolutePullbackMap φ)) X a

/-- The relative universal derivation is literally the original cokernel projection on `d a`. -/
theorem derivation_d (X : Dᵒᵖ) (a : R.obj X) :
    (derivation φ).d a =
      (cokernel.π (absolutePullbackMap φ)).app X ((absoluteDerivation R).d a) := rfl

/-- The original cokernel descent associated to a native relative derivation. -/
def relativeDesc {M : PresheafOfModulesOfCommRing.{u} R} (d : M.Derivation φ) :
    relativeDifferentials φ ⟶ M :=
  cokernel.desc (absolutePullbackMap φ) (absoluteDesc d)
    ((absolutePullbackMap_comp_eq_zero_iff φ (absoluteDesc d)).mpr (fun X a => by
      rw [absoluteDesc_d]
      exact d.d_app a))

/-- Relative descent preserves the exact original derivation values. -/
@[simp]
theorem relativeDesc_d {M : PresheafOfModulesOfCommRing.{u} R} (d : M.Derivation φ)
    (X : Dᵒᵖ) (a : R.obj X) :
    (relativeDesc φ d).app X ((derivation φ).d a) = d.d a := by
  have h := congrArg (fun t => t.app X ((absoluteDerivation R).d a))
    (cokernel.π_desc (absolutePullbackMap φ) (absoluteDesc d)
      ((absolutePullbackMap_comp_eq_zero_iff φ (absoluteDesc d)).mpr (fun Y b => by
        rw [absoluteDesc_d]
        exact d.d_app b)))
  exact h.trans (absoluteDesc_d d X a)

/-- The native cokernel construction is universal for the original relative derivations. -/
def isUniversal : (derivation φ).Universal where
  desc d := relativeDesc φ d
  fac d := by
    ext X a
    exact relativeDesc_d φ d X a
  postcomp_injective α β h := by
    apply (cancel_epi (cokernel.π (absolutePullbackMap φ))).mp
    apply (isUniversal' (integerConstants R)).postcomp_injective
    ext X a
    exact Derivation.congr_d h a

/-- Actual relative differentials exist whenever the native presheaf pullback exists.
This theorem leaves the pre-existing identity-case instance and its priority unchanged. -/
theorem hasDifferentials : HasDifferentials φ :=
  ⟨relativeDifferentials φ, derivation φ, ⟨isUniversal φ⟩⟩

/-- The original relative derivation represents the actual morphisms out of the cokernel. -/
def relativeDifferentialsHomEquiv (M : PresheafOfModulesOfCommRing.{u} R) :
    (relativeDifferentials φ ⟶ M) ≃ M.Derivation φ where
  toFun k := (derivation φ).postcomp k
  invFun d := relativeDesc φ d
  left_inv k := (isUniversal φ).postcomp_injective _ _
    ((isUniversal φ).fac ((derivation φ).postcomp k))
  right_inv d := (isUniversal φ).fac d

/-- The universal equivalence evaluates the original morphism on the original differential. -/
theorem relativeDifferentialsHomEquiv_apply (M : PresheafOfModulesOfCommRing.{u} R)
    (k : relativeDifferentials φ ⟶ M) (X : Dᵒᵖ) (a : R.obj X) :
    (relativeDifferentialsHomEquiv φ M k).d a = k.app X ((derivation φ).d a) := rfl

/-- The inverse equivalence is the original cokernel descent. -/
theorem relativeDifferentialsHomEquiv_symm (M : PresheafOfModulesOfCommRing.{u} R)
    (d : M.Derivation φ) :
    (relativeDifferentialsHomEquiv φ M).symm d = relativeDesc φ d := rfl

/-- Descent commutes with the original coefficient morphisms. -/
theorem relativeDesc_postcomp {M N : PresheafOfModulesOfCommRing.{u} R}
    (d : M.Derivation φ) (k : M ⟶ N) :
    relativeDesc φ (d.postcomp k) = relativeDesc φ d ≫ k := by
  apply (isUniversal φ).postcomp_injective
  ext X a
  change (relativeDesc φ (d.postcomp k)).app X ((derivation φ).d a) =
    k.app X ((relativeDesc φ d).app X ((derivation φ).d a))
  rw [relativeDesc_d, relativeDesc_d]
  rfl

section Identity

variable {S' : Dᵒᵖ ⥤ CommRingCat.{u}} (ψ : S' ⟶ R)
  [(pushforward.{u} (F := 𝟭 D) ψ).IsRightAdjoint]

/-- For the identity functor, the actual cokernel object is canonically the original
native relative differential presheaf, with both universal derivations unchanged. -/
def relativeDifferentialsIdIso :
    relativeDifferentials (F := 𝟭 D) ψ ≅ relativeDifferentials' ψ where
  hom := relativeDesc (F := 𝟭 D) ψ (derivation' ψ)
  inv := (isUniversal' ψ).desc (derivation (F := 𝟭 D) ψ)
  hom_inv_id := by
    apply (isUniversal (F := 𝟭 D) ψ).postcomp_injective
    ext X a
    exact (congrArg
      (((isUniversal' ψ).desc (derivation (F := 𝟭 D) ψ)).app X)
      (relativeDesc_d (F := 𝟭 D) ψ (derivation' ψ) X a)).trans
      (Derivation.congr_d ((isUniversal' ψ).fac (derivation (F := 𝟭 D) ψ)) a)
  inv_hom_id := by
    apply (isUniversal' ψ).postcomp_injective
    ext X a
    exact (congrArg ((relativeDesc (F := 𝟭 D) ψ (derivation' ψ)).app X)
      (Derivation.congr_d ((isUniversal' ψ).fac (derivation (F := 𝟭 D) ψ)) a)).trans
      (relativeDesc_d (F := 𝟭 D) ψ (derivation' ψ) X a)

/-- The identity-functor comparison sends the actual cokernel differential to the native one. -/
@[simp]
theorem relativeDifferentialsIdIso_hom_d (X : Dᵒᵖ) (a : R.obj X) :
    (relativeDifferentialsIdIso ψ).hom.app X ((derivation (F := 𝟭 D) ψ).d a) =
      (derivation' ψ).d a := relativeDesc_d (F := 𝟭 D) ψ (derivation' ψ) X a

/-- The inverse comparison preserves the same original differential, without a sign or unit. -/
@[simp]
theorem relativeDifferentialsIdIso_inv_d (X : Dᵒᵖ) (a : R.obj X) :
    (relativeDifferentialsIdIso ψ).inv.app X ((derivation' ψ).d a) =
      (derivation (F := 𝟭 D) ψ).d a :=
  Derivation.congr_d ((isUniversal' ψ).fac (derivation (F := 𝟭 D) ψ)) a

end Identity

end PresheafOfModulesOfCommRing.DifferentialsConstruction
