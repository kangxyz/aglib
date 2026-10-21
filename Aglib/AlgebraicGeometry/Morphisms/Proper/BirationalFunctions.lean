/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.Map
public import Aglib.AlgebraicGeometry.Properties.Normal.Affine
public import Aglib.AlgebraicGeometry.Properties.Normal.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Functions under a universally closed birational morphism

The actual map on affine sections is integral by universal closedness. Its embedding into
the source function field, transported through the actual birational field map, identifies
it with the integrally closed target section ring. Affine sheaf locality then proves that
the original map `O_Y -> f_* O_X` is an isomorphism.

This is an ordinary structure-sheaf result. The geometric connectedness of arbitrary fibres
remains a separate obligation in the proper-birational connectedness theorem.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

private theorem bijective_of_integral_of_fraction_field
    {A B K L : Type u} [CommRing A] [IsIntegrallyClosed A]
    [CommRing B] [CommRing K] [CommRing L] [Algebra A K] [IsFractionRing A K]
    (φ : A →+* B) (j : B →+* L) (e : K ≃+* L)
    (hj : Function.Injective j) (hφ : φ.IsIntegral)
    (hcomm : j.comp φ = e.toRingHom.comp (algebraMap A K)) :
    Function.Bijective φ := by
  let t : B →+* K := e.symm.toRingHom.comp j
  have ht : t.comp φ = algebraMap A K := by
    ext a
    change e.symm (j (φ a)) = algebraMap A K a
    rw [show j (φ a) = e (algebraMap A K a) from DFunLike.congr_fun hcomm a]
    exact e.symm_apply_apply _
  constructor
  · intro a b hab
    apply IsFractionRing.injective A K
    apply e.injective
    calc
      e (algebraMap A K a) = j (φ a) := (DFunLike.congr_fun hcomm a).symm
      _ = j (φ b) := congrArg j hab
      _ = e (algebraMap A K b) := DFunLike.congr_fun hcomm b
  · intro b
    have hb : _root_.IsIntegral A (t b) := by
      change (algebraMap A K).IsIntegralElem (t b)
      rw [← ht]
      exact (hφ b).map t
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hb
    refine ⟨a, hj ?_⟩
    calc
      j (φ a) = e (algebraMap A K a) := DFunLike.congr_fun hcomm a
      _ = e (t b) := congrArg e ha
      _ = j b := e.apply_symm_apply _

private theorem functionFieldMap_germ_open
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] (U : Y.Opens)
    [Nonempty U] [Nonempty (f ⁻¹ᵁ U)] :
    Y.germToFunctionField U ≫ CommRingCat.ofHom (functionFieldMap f) =
      f.app U ≫ X.germToFunctionField (f ⁻¹ᵁ U) := by
  change Y.presheaf.germ U _ _ ≫
    (Y.presheaf.stalkSpecializes
      (specializes_of_eq (map_genericPoint_of_isDominant X f)) ≫
        f.stalkMap (genericPoint X)) = _
  rw [← Category.assoc, TopCat.Presheaf.germ_stalkSpecializes]
  exact f.germ_stalkMap U (genericPoint X) _

private theorem isIntegral_app_of_universallyClosed
    {X Y : Scheme.{u}} (f : X ⟶ Y) [UniversallyClosed f]
    (U : Y.Opens) (hU : IsAffineOpen U) : (f.app U).hom.IsIntegral := by
  let : IsAffine U.toScheme := hU
  have hint := isIntegral_appTop_of_universallyClosed (f ∣_ U)
  rw [morphismRestrict_appTop, CommRingCat.hom_comp,
    RingHom.isIntegral_respectsIso.cancel_right_isIso] at hint
  have hint : (f.app (U.ι ''ᵁ ⊤)).hom.IsIntegral := hint
  rwa [Scheme.Opens.ι_image_top] at hint

/-- The original section map of a universally closed birational morphism is bijective
on each actual affine open of the normal integral target. -/
theorem bijective_app_of_isAffineOpen_of_universallyClosed_birational
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [UniversallyClosed f] [IsDominant f]
    (hY : NormalStalks Y)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (U : Y.Opens) (hU : IsAffineOpen U) : Function.Bijective (f.app U) := by
  classical
  by_cases hne : Nonempty U
  · let : Nonempty U := hne
    let : Nonempty (f ⁻¹ᵁ U) := by
      refine ⟨⟨genericPoint X, ?_⟩⟩
      change f (genericPoint X) ∈ U
      rw [map_genericPoint_of_isDominant X f]
      exact ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr (by simpa using hne)
    let (y : Y) : IsIntegrallyClosed (Y.presheaf.stalk y) := (hY y).2
    let : IsIntegrallyClosed Γ(Y, U) :=
      isIntegrallyClosed_sections_of_isAffineOpen Y U hU
    let : IsFractionRing Γ(Y, U) Y.functionField :=
      functionField_isFractionRing_of_isAffineOpen Y U hU
    let : IsIso (CommRingCat.ofHom (functionFieldMap f)) := hff
    let e : Y.functionField ≃+* X.functionField :=
      (asIso (CommRingCat.ofHom (functionFieldMap f))).commRingCatIsoToRingEquiv
    apply bijective_of_integral_of_fraction_field (f.app U).hom
      (X.germToFunctionField (f ⁻¹ᵁ U)).hom e
      (X.germToFunctionField_injective (f ⁻¹ᵁ U))
      (isIntegral_app_of_universallyClosed f U hU)
    exact (congrArg CommRingCat.Hom.hom (functionFieldMap_germ_open f U)).symm
  · have hbot : U = ⊥ := by
      apply bot_unique
      intro y hy
      exact (hne ⟨⟨y, hy⟩⟩).elim
    subst U
    have : Subsingleton Γ(X, f ⁻¹ᵁ (⊥ : Y.Opens)) := by
      rw [Scheme.Hom.preimage_bot]
      infer_instance
    constructor
    · intro a b _
      exact Subsingleton.elim _ _
    · intro b
      exact ⟨0, Subsingleton.elim _ _⟩

/-- Normality of the target and the actual birational field map identify the original
structure sheaf with its ordinary pushforward under a universally closed morphism. -/
theorem isIso_c_of_universallyClosed_birational
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [UniversallyClosed f] [IsDominant f]
    (hY : NormalStalks Y)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f))) : IsIso f.c := by
  let F : Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj X.sheaf := ⟨f.c⟩
  have hF : IsIso F := by
    refine TopCat.Sheaf.isIso_iff_isIso_basis
      (B := fun U : Y.affineOpens => (U : Y.Opens)) ?_ ?_
    · rw [Subtype.range_coe]
      exact Y.isBasis_affineOpens
    · intro U
      rw [ConcreteCategory.isIso_iff_bijective]
      exact bijective_app_of_isAffineOpen_of_universallyClosed_birational f hY hff U.val U.2
  exact (inferInstance : IsIso ((sheafToPresheaf _ _).map F))

/-- Proper birational morphisms onto a normal integral target preserve the actual
structure sheaf. This conclusion does not require local Noetherianity. -/
theorem isIso_c_of_isProper_birational
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsProper f] [IsDominant f]
    (hY : NormalStalks Y)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f))) : IsIso f.c :=
  isIso_c_of_universallyClosed_birational f hY hff

end AlgebraicGeometry.Scheme
