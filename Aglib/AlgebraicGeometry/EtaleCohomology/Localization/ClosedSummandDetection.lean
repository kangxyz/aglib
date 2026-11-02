/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.Cohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.OrdinaryBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.NativeAdjunctionUnderlying
public import Aglib.CategoryTheory.Adjunction.UnderlyingHomEquiv

/-! # Original closed-summand classes detected after finite pullback

Finite canonical exchange and the original cohomology equivalence detect the
original adjunct summand in all degrees. The hypothesis is zero of the class
after the original coefficient arrow on the closed pullback, not zero of its
unmapped restriction. No effacement or support induction is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u eT eV uM vM uN vN

attribute [local instance] hasSheafifyLarge

variable {X Z T W : Scheme.{u}}
  [HasExt.{eT} (AbelianSheaf.{u, u + 1} T)]
  [HasExt.{eV} (AbelianSheaf.{u, u + 1} W)]

/-- Original coefficient isomorphisms detect zero in every degree. -/
private theorem finiteSummand_map_detects_zero
    {F G : AbelianSheaf.{u, u + 1} T} (a : F ⟶ G) [IsIso a]
    (q : ℕ) (x : Sheaf.H.{eT} F q) (hx : Sheaf.H.map a q x = 0) : x = 0 := by
  have hz := congrArg (Sheaf.H.map (inv a) q) hx
  simpa only [← Sheaf.H.map_comp_apply, IsIso.hom_inv_id,
    Sheaf.H.map_id_apply, map_zero] using hz

omit [HasExt.{eT} (AbelianSheaf.{u, u + 1} T)]
  [HasExt.{eV} (AbelianSheaf.{u, u + 1} W)] in
/-- The original mate and coefficient adjunct give the literal closed-side
arrow. This is an equation, not an additional compatibility hypothesis. -/
theorem baseChangeMap_adjunct_counit
    (i : Z ⟶ X) (i' : W ⟶ T) (b : T ⟶ X) (b' : W ⟶ Z)
    (h : i' ≫ b = b' ≫ i) {F : AbelianSheaf.{u, u + 1} X}
    {A : AbelianSheaf.{u, u + 1} Z} (a : (inverseImage i).obj F ⟶ A) :
    (inverseImage i').map ((inverseImage b).map ((inverseImageAdjunction i).homEquiv F A a)) ≫
        (inverseImage i').map ((baseChangeMap i i' b b' h).app A) ≫
        (inverseImageAdjunction i').counit.app ((inverseImage b').obj A) =
      (inverseImageSquareIso i i' b b' h).hom.app F ≫ (inverseImage b').map a := by
  let k := (inverseImageAdjunction i).homEquiv F A a
  have hn := (inverseImageSquareIso i i' b b' h).hom.naturality k
  dsimp only [Functor.comp_map] at hn
  have ha : (inverseImage i).map k ≫ (inverseImageAdjunction i).counit.app A = a := by
    exact ((inverseImageAdjunction i).homEquiv F A).symm_apply_apply a
  rw [baseChangeMap_counit, ← Category.assoc, hn, Category.assoc,
    ← Functor.map_comp, ha]

/-- Finite ordinary exchange and the original finite cohomology equivalence
turn zero of the closed coefficient class into zero of the original adjunct
summand, including degree zero. -/
theorem finiteAdjunctSummand_eq_zero
    (i : Z ⟶ X) [IsFinite i] (i' : W ⟶ T) (b : T ⟶ X) (b' : W ⟶ Z)
    (h : IsPullback b' i' i b) {F : AbelianSheaf.{u, u + 1} X}
    {A : AbelianSheaf.{u, u + 1} Z} (a : (inverseImage i).obj F ⟶ A)
    (q : ℕ) (x : Sheaf.H.{eT} ((inverseImage b).obj F) q)
    (hx : Sheaf.H.map
      ((inverseImageSquareIso i i' b b' h.w.symm).hom.app F ≫ (inverseImage b').map a) q
      (cohomologyPullback i' ((inverseImage b).obj F) q x) = 0) :
    Sheaf.H.map ((inverseImage b).map ((inverseImageAdjunction i).homEquiv F A a)) q x = 0 := by
  let : IsFinite i' := MorphismProperty.of_isPullback h (inferInstance : IsFinite i)
  let β := (baseChangeMap i i' b b' h.w.symm).app A
  let : IsIso β := Finite.finiteBaseChange_app_isIso i i' b b' h A
  apply finiteSummand_map_detects_zero β q
  apply (Finite.finiteCohomologyDirectImageAddEquiv i' ((inverseImage b').obj A) q).injective
  rw [map_zero, Finite.finiteCohomologyDirectImageAddEquiv_apply,
    cohomologyPullback_coefficientMap, cohomologyPullback_coefficientMap,
    ← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply]
  rw [baseChangeMap_adjunct_counit]
  exact hx

omit [HasExt.{eT} (AbelianSheaf.{u, u + 1} T)]
  [HasExt.{eV} (AbelianSheaf.{u, u + 1} W)] in
/-- The original closed-pullback coefficient arrow, formed before cohomology
and before native module specialization. -/
def underlyingClosedPullbackCoefficientMap
    (i : Z ⟶ X) (i' : W ⟶ T) (b : T ⟶ X) (b' : W ⟶ Z)
    (h : i' ≫ b = b' ≫ i)
    {M : Type uM} [Category.{vM} M] {N : Type uN} [Category.{vN} N]
    {L : M ⥤ N}
    (U : M ⥤ AbelianSheaf.{u, u + 1} X) (V : N ⥤ AbelianSheaf.{u, u + 1} Z)
    (e : L ⋙ V ≅ U ⋙ inverseImage i)
    (I : M) (J : N) (a : L.obj I ⟶ J) :
    (inverseImage i').obj ((inverseImage b).obj (U.obj I)) ⟶
      (inverseImage b').obj (V.obj J) :=
  (inverseImageSquareIso i i' b b' h).hom.app (U.obj I) ≫
    (inverseImage b').map (e.inv.app I ≫ V.map a)

/-- The entire underlying-adjunct transport is proved before native module
specialization. Compatibility is obtained from the given original mate law. -/
theorem underlyingFiniteAdjunctSummand_eq_zero
    (i : Z ⟶ X) [IsFinite i] (i' : W ⟶ T) (b : T ⟶ X) (b' : W ⟶ Z)
    (h : IsPullback b' i' i b)
    {M : Type uM} [Category.{vM} M] {N : Type uN} [Category.{vN} N]
    {L : M ⥤ N} {R : N ⥤ M} (adj : L ⊣ R)
    (U : M ⥤ AbelianSheaf.{u, u + 1} X) (V : N ⥤ AbelianSheaf.{u, u + 1} Z)
    (e : L ⋙ V ≅ U ⋙ inverseImage i) (d : R ⋙ U ≅ V ⋙ directImage i)
    (hmate : (mateEquiv adj (inverseImageAdjunction i)
      (TwoSquare.mk _ _ _ _ e.inv)).natTrans = d.hom)
    (I : M) (J : N) (a : L.obj I ⟶ J) (q : ℕ)
    (x : Sheaf.H.{eT} ((inverseImage b).obj (U.obj I)) q)
    (hx : Sheaf.H.map
      (underlyingClosedPullbackCoefficientMap i i' b b' h.w.symm U V e I J a) q
      (cohomologyPullback i' ((inverseImage b).obj (U.obj I)) q x) = 0) :
    Sheaf.H.map ((inverseImage b).map (U.map (adj.homEquiv I J a))) q x = 0 := by
  have he := underlying_homEquiv_of_mate adj (inverseImageAdjunction i)
    (TwoSquare.mk _ _ _ _ e.inv) d.hom hmate I J a
  have hz := finiteAdjunctSummand_eq_zero i i' b b' h (e.inv.app I ≫ V.map a) q x hx
  rw [← he, Functor.map_comp, Sheaf.H.map_comp_apply] at hz
  exact finiteSummand_map_detects_zero ((inverseImage b).map (d.hom.app J)) q _ hz

open Coefficients

omit [HasExt.{eT} (AbelianSheaf.{u, u + 1} T)]
  [HasExt.{eV} (AbelianSheaf.{u, u + 1} W)] in
/-- The native closed coefficient arrow is the same shared original square
and underlying inverse-image construction, not a replacement mate. -/
def moduleClosedPullbackCoefficientMap
    (i : Z ⟶ X) (i' : W ⟶ T) (b : T ⟶ X) (b' : W ⟶ Z)
    (h : i' ≫ b = b' ≫ i) (Λ : Type (u + 1)) [Ring Λ]
    (I : ModuleSheaf X Λ) (J : ModuleSheaf Z Λ)
    (a : (moduleInverseImage i Λ).obj I ⟶ J) :
    (inverseImage i').obj ((inverseImage b).obj
      ((SheafOfModules.toSheaf (constantRing X Λ)).obj I)) ⟶
    (inverseImage b').obj ((SheafOfModules.toSheaf (constantRing Z Λ)).obj J) :=
  underlyingClosedPullbackCoefficientMap i i' b b' h
    (SheafOfModules.toSheaf (constantRing X Λ))
    (SheafOfModules.toSheaf (constantRing Z Λ))
    (moduleInverseImageUnderlyingIso Λ i) I J a

/-- The closed coefficient class after the original `a` detects the literal
module adjunct summand used by open/closed detection. No zero restriction,
injectivity, higher-image vanishing or q0 comparison is assumed. -/
theorem moduleClosedSummand_eq_zero
    (i : Z ⟶ X) [IsFinite i] (i' : W ⟶ T) (b : T ⟶ X) (b' : W ⟶ Z)
    (h : IsPullback b' i' i b) (Λ : Type (u + 1)) [Ring Λ]
    (I : ModuleSheaf X Λ) (J : ModuleSheaf Z Λ)
    (a : (moduleInverseImage i Λ).obj I ⟶ J) (q : ℕ)
    (x : Sheaf.H.{eT} ((inverseImage b).obj
      ((SheafOfModules.toSheaf (constantRing X Λ)).obj I)) q)
    (hx : Sheaf.H.map
      (moduleClosedPullbackCoefficientMap i i' b b' h.w.symm Λ I J a) q
      (cohomologyPullback i' _ q x) = 0) :
    Sheaf.H.map ((inverseImage b).map
      ((SheafOfModules.toSheaf (constantRing X Λ)).map
        ((moduleInverseImageAdjunction i Λ).homEquiv I J a))) q x = 0 := by
  have hz := underlyingFiniteAdjunctSummand_eq_zero i i' b b' h
    (moduleInverseImageAdjunction i Λ)
    (SheafOfModules.toSheaf (constantRing X Λ))
    (SheafOfModules.toSheaf (constantRing Z Λ))
    (moduleInverseImageUnderlyingIso Λ i) (moduleDirectImageUnderlyingIso i Λ)
    (mate_moduleInverseImageUnderlyingIso_inv (Λ := Λ) (f := i)) I J a q x hx
  exact hz

end AlgebraicGeometry.Scheme.EtaleCohomology
