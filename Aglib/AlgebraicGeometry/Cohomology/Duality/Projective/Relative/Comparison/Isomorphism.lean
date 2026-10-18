/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Comparison.Restriction
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Identity

/-!
# The original restriction maps along scheme isomorphisms

The native restriction and derived functors remain equivalences along a scheme
isomorphism. This proves bijectivity of the same source and target restriction
maps used in the Serre square, for transport to the supplied affine polynomial
model and from an affine scheme to its spectrum.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
universe u
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory

namespace AlgebraicGeometry.Scheme.Cohomology

private theorem rightDerived_equivalence
    {A B : Type*} [Category* A] [Abelian A] [HasDerivedCategory A] [EnoughInjectives A]
    [Category* B] [Abelian B] [HasDerivedCategory B] [EnoughInjectives B]
    (F : A ⥤ B) [F.Additive] [F.IsEquivalence] : F.rightDerivedFunctorPlus.IsEquivalence := by
  let E := F.asEquivalence
  let G := E.inverse
  let : E.functor.Additive := inferInstanceAs F.Additive
  let : G.Additive := E.inverse_additive
  let : G.IsEquivalence := E.isEquivalence_inverse
  let η : F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus ≅
      𝟭 (DerivedCategory.Plus A) :=
    (F.rightDerivedFunctorPlusCompIsoOfPreservesInjectives G).symm ≪≫
      (F ⋙ G).rightDerivedFunctorPlusIso E.unitIso.symm ≪≫
        Functor.rightDerivedFunctorPlusIdIso A
  let ε : G.rightDerivedFunctorPlus ⋙ F.rightDerivedFunctorPlus ≅
      𝟭 (DerivedCategory.Plus B) :=
    (G.rightDerivedFunctorPlusCompIsoOfPreservesInjectives F).symm ≪≫
      (G ⋙ F).rightDerivedFunctorPlusIso E.counitIso ≪≫
        Functor.rightDerivedFunctorPlusIdIso B
  exact Functor.IsEquivalence.mk' G.rightDerivedFunctorPlus η.symm ε

/-- The actual right-derived restriction along a scheme isomorphism is an equivalence. -/
theorem derivedRestriction_isEquivalence_of_isIso
    {U Y : Scheme.{u}} (j : U ⟶ Y) [IsIso j] :
    (Scheme.Modules.restrictFunctor j).rightDerivedFunctorPlus.IsEquivalence := by
  let η : Scheme.Modules.pushforward j ⋙ Scheme.Modules.pushforward (inv j) ≅ 𝟭 U.Modules :=
    Scheme.Modules.pushforwardComp j (inv j) ≪≫
      eqToIso (congrArg (fun k : U ⟶ U => Scheme.Modules.pushforward k) (IsIso.hom_inv_id j)) ≪≫
        Scheme.Modules.pushforwardId U
  let ε : Scheme.Modules.pushforward (inv j) ⋙ Scheme.Modules.pushforward j ≅ 𝟭 Y.Modules :=
    Scheme.Modules.pushforwardComp (inv j) j ≪≫
      eqToIso (congrArg (fun k : Y ⟶ Y => Scheme.Modules.pushforward k) (IsIso.inv_hom_id j)) ≪≫
        Scheme.Modules.pushforwardId Y
  let : (Scheme.Modules.pushforward j).IsEquivalence :=
    Functor.IsEquivalence.mk' (Scheme.Modules.pushforward (inv j)) η.symm ε
  let : (Scheme.Modules.restrictFunctor j).IsEquivalence :=
    (Scheme.Modules.restrictAdjunction j).isEquivalence_left_of_isEquivalence_right
  exact rightDerived_equivalence (Scheme.Modules.restrictFunctor j)

private theorem shifted_map_bijective
    {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
    (F : C ⥤ D) [F.CommShift ℤ] [F.Full] [F.Faithful] (K L : C) (k : ℤ) :
    Function.Bijective (fun a : ShiftedHom K L k => a.map F) := by
  let E := Iso.homCongr (Iso.refl (F.obj K)) ((F.commShiftIso k).app L)
  have heq : (fun a : ShiftedHom K L k => a.map F) =
      E ∘ (F.map (X := K) (Y := L⟦k⟧)) := by
    funext a
    simp only [E, Function.comp_apply, Iso.homCongr_apply, Iso.refl_inv,
      Category.id_comp, Iso.app_hom, ShiftedHom.map]
  rw [heq]
  exact E.bijective.comp ((Functor.FullyFaithful.ofFullyFaithful F).map_bijective _ _)

variable {W X U Y : Scheme.{u}} (p : X ⟶ Y) (i : W ⟶ X) (q : W ⟶ U) (j : U ⟶ Y)
  [IsOpenImmersion i] [IsOpenImmersion j] (H : IsPullback i q p j)

/-- A scheme isomorphism makes the original coefficient Ext restriction bijective. -/
theorem relativeProjectiveExtRestriction_bijective_of_isIso [IsIso i]
    (n : ℕ) (N : Y.Modules) (M : X.Modules) (r : ℕ) :
    Function.Bijective (relativeProjectiveExtRestriction p i q j H n N M r) := by
  let F := (Scheme.Modules.restrictFunctor i).rightDerivedFunctorPlus
  let : F.IsEquivalence := derivedRestriction_isEquivalence_of_isIso i
  let V := (relativeTopDifferentialCoefficientsFunctor p n).obj N
  let V' := (relativeTopDifferentialCoefficientsFunctor q n).obj (N.restrict j)
  let S := DerivedCategory.Plus.singleFunctor X.Modules 0
  let A := (Ext.homPlusAddEquiv (X := M) (Y := V) r).toEquiv
  let s := ((Scheme.Modules.restrictFunctor i).rightDerivedFunctorPlusSingleIso 0).app M
  let t := ((Scheme.Modules.restrictFunctor i).rightDerivedFunctorPlusSingleIso 0).app V ≪≫
    (DerivedCategory.Plus.singleFunctor W.Modules 0).mapIso
      ((relativeTopDifferentialCoefficientsRestrictionIso p i q j H.w n).app N)
  let B := Iso.homCongr s
    ((shiftFunctor (DerivedCategory.Plus W.Modules) (r : ℤ)).mapIso t)
  have heq : (fun x => (relativeProjectiveExtRestriction p i q j H n N M r x).homPlus) =
      B ∘ ((fun a : ShiftedHom (S.obj M) (S.obj V) (r : ℤ) => a.map F) ∘ A) := by
    funext x
    rw [relativeProjectiveExtRestriction_homPlus]
    simp only [A, B, t, Function.comp_apply, Iso.homCongr_apply,
      Functor.mapIso_hom, Iso.trans_hom, Iso.app_hom]
    rfl
  have hb : Function.Bijective
      (fun x => (relativeProjectiveExtRestriction p i q j H n N M r x).homPlus) := by
    rw [heq]
    exact B.bijective.comp ((shifted_map_bijective F (S.obj M) (S.obj V) (r : ℤ)).comp
      A.bijective)
  exact (Equiv.comp_bijective (relativeProjectiveExtRestriction p i q j H n N M r)
    (Ext.homPlusAddEquiv (X := M.restrict i) (Y := V') r).toEquiv).mp hb

/-- Original target restriction, before any coefficient counit. -/
def relativeProjectiveTargetRestriction (n : ℤ) (N : Y.Modules) (M : X.Modules) (r : ℤ)
    (a : ShiftedHom ((Scheme.Modules.derivedPushforwardPlus p).obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M))
      ((DerivedCategory.Plus.singleFunctor Y.Modules n).obj N) r) :
    ShiftedHom ((Scheme.Modules.derivedPushforwardPlus q).obj
        ((DerivedCategory.Plus.singleFunctor W.Modules 0).obj (M.restrict i)))
      ((DerivedCategory.Plus.singleFunctor U.Modules n).obj (N.restrict j)) r :=
  (relativeProjectiveSourceRestrictionIso p i q j H M).inv ≫
    a.map (Scheme.Modules.restrictFunctor j).rightDerivedFunctorPlus ≫
    (((Scheme.Modules.restrictFunctor j).rightDerivedFunctorPlusSingleIso n).hom.app N)⟦r⟧'

/-- A scheme isomorphism makes the original derived target restriction bijective. -/
theorem relativeProjectiveTargetRestriction_bijective_of_isIso [IsIso j]
    (n : ℤ) (N : Y.Modules) (M : X.Modules) (r : ℤ) :
    Function.Bijective (relativeProjectiveTargetRestriction p i q j H n N M r) := by
  let F := (Scheme.Modules.restrictFunctor j).rightDerivedFunctorPlus
  let : F.IsEquivalence := derivedRestriction_isEquivalence_of_isIso j
  let K := (Scheme.Modules.derivedPushforwardPlus p).obj
    ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)
  let L := (DerivedCategory.Plus.singleFunctor Y.Modules n).obj N
  let B := Iso.homCongr (relativeProjectiveSourceRestrictionIso p i q j H M)
    ((shiftFunctor (DerivedCategory.Plus U.Modules) r).mapIso
      (((Scheme.Modules.restrictFunctor j).rightDerivedFunctorPlusSingleIso n).app N))
  have heq : relativeProjectiveTargetRestriction p i q j H n N M r =
      B ∘ (fun a : ShiftedHom K L r => a.map F) := by
    funext a
    rfl
  rw [heq]
  exact B.bijective.comp (shifted_map_bijective F K L r)

end AlgebraicGeometry.Scheme.Cohomology
