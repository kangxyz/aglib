/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.InternalHom.ExtAcyclic
public import Aglib.Algebra.Homology.DerivedCategory.Ext.LeftExactComparison

/-!
# Original Ext and cohomology of internal Hom at an acyclic coefficient

The native internal-Hom/global-Hom comparison and the proved injective-image
acyclicity discharge the corresponding premises of the generic left-exact
construction. Only actual acyclicity of the specified target for internal Hom
remains a hypothesis. The output is the existing original Sheaf.H and retains
the original forward map, degree-zero unit and coefficient maps.

This conditional supplier is not a finite-locally-constant vanishing theorem.
An application to roots of unity must prove the remaining internal-Hom
acyclicity; neither local freeness nor exactness of tensor is presumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open SheafOfModules.InternalHom

universe c h eM eA

namespace CategoryTheory.Sheaf.InternalExt

variable {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c h} RingCat.{max c h})]
  (R : Sheaf J CommRingCat.{max c h}) [HasSheafify J AddCommGrpCat.{max c h}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c h}]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{max c h})]
  [∀ W : C, HasFiniteProducts (Over W)]
  [HasExt.{eM} (SheafOfModulesOfCommRing R)]
  [HasExt.{eA} (Sheaf J AddCommGrpCat.{max c h})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{max c h})]
  {T : C} (hT : IsTerminal T)

local instance : EnoughInjectives (SheafOfModulesOfCommRing R) :=
  SheafOfModules.enoughInjectivesLarge.{c, h, 0}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)

include hT in
/-- The proved injective-image premise at the literal native internal-Hom functor object. -/
theorem homFunctor_injective_ext_subsingleton (M I : SheafOfModulesOfCommRing R)
    [Injective I] (q : ℕ) :
    Subsingleton (Ext.{eM}
      (SheafOfModules.liftedUnit.{c, h, max c h, max c h}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
      ((homFunctor.{c, h, 0} R M).obj I) (q + 1)) :=
  ext_subsingleton_of_injective R hT M I q

/-- The generic original comparison at the native internal Hom and selected lifted unit. -/
def moduleExtAddEquivOfAcyclic (M N : SheafOfModulesOfCommRing R)
    (hN : ∀ q : ℕ, IsZero (((homFunctor.{c, h, 0} R M).rightDerived (q + 1)).obj N))
    (q : ℕ) :
    Ext.{eM} M N q ≃+ Ext.{eM}
      (SheafOfModules.liftedUnit.{c, h, max c h, max c h}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
      ((homFunctor.{c, h, 0} R M).obj N) q :=
  Functor.extAddEquivOfLeftExactAcyclic.{_, _, _, eM, eM} (homFunctor.{c, h, 0} R M) _
    (liftedUnitCoyonedaIso.{c, h, 0} R M)
    (homFunctor_injective_ext_subsingleton R hT M) N hN q

/-- The original comparison when the specified target is acyclic for internal Hom. -/
def extCohomologyAddEquivOfAcyclic (M N : SheafOfModulesOfCommRing R)
    (hN : ∀ q : ℕ, IsZero (((homFunctor.{c, h, 0} R M).rightDerived (q + 1)).obj N))
    (q : ℕ) :
    Ext.{eM} M N q ≃+ Sheaf.H.{eA}
      ((SheafOfModules.toSheaf ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).obj
        (sheaf R M N)) q :=
  (moduleExtAddEquivOfAcyclic R hT M N hN q).trans
    (ModuleCoefficients.moduleExtCohomologyAddEquivLargeScalars hT
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
      ((homFunctor.{c, h, 0} R M).obj N) q)

/-- The forward map is the native module Ext comparison followed by original cohomologyMap. -/
theorem extCohomologyAddEquivOfAcyclic_apply (M N : SheafOfModulesOfCommRing R)
    (hN : ∀ q : ℕ, IsZero (((homFunctor.{c, h, 0} R M).rightDerived (q + 1)).obj N))
    (q : ℕ) (x : Ext.{eM} M N q) :
    extCohomologyAddEquivOfAcyclic R hT M N hN q x =
      ModuleCoefficients.cohomologyMap hT
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
        ((homFunctor.{c, h, 0} R M).obj N) q
        (moduleExtAddEquivOfAcyclic R hT M N hN q x) := rfl

/-- Degree zero retains the original lifted-unit arrow and the original forgetting map. -/
theorem extCohomologyAddEquivOfAcyclic_mk₀ (M N : SheafOfModulesOfCommRing R)
    (hN : ∀ q : ℕ, IsZero (((homFunctor.{c, h, 0} R M).rightDerived (q + 1)).obj N))
    (f : M ⟶ N) :
    extCohomologyAddEquivOfAcyclic R hT M N hN 0 (Ext.mk₀ f) =
      ModuleCoefficients.cohomologyMap hT
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (sheaf R M N) 0
        (Ext.mk₀ ((liftedUnitCoyonedaIso.{c, h, 0} R M).inv.app N f)) := by
  rw [extCohomologyAddEquivOfAcyclic_apply]
  exact congrArg
    (ModuleCoefficients.cohomologyMap hT
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
      ((homFunctor.{c, h, 0} R M).obj N) 0)
    (Functor.extAddEquivOfLeftExactAcyclic_mk₀.{_, _, _, eM, eM} (homFunctor.{c, h, 0} R M) _
      (liftedUnitCoyonedaIso.{c, h, 0} R M)
      (homFunctor_injective_ext_subsingleton R hT M) N hN f)

/-- The all-degree comparison specializes to the already proved unconditional degree-zero map. -/
theorem extCohomologyAddEquivOfAcyclic_zero (M N : SheafOfModulesOfCommRing R)
    (hN : ∀ q : ℕ, IsZero (((homFunctor.{c, h, 0} R M).rightDerived (q + 1)).obj N)) :
    extCohomologyAddEquivOfAcyclic R hT M N hN 0 = extZeroCohomologyAddEquiv R hT M N := by
  apply AddEquiv.ext
  intro x
  obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective M N).surjective x
  rw [extCohomologyAddEquivOfAcyclic_mk₀, extZeroCohomologyAddEquiv_mk₀]

/-- Naturality uses the original internal-Hom coefficient map and original Sheaf.H.map. -/
theorem extCohomologyAddEquivOfAcyclic_naturality (M : SheafOfModulesOfCommRing R)
    {N N' : SheafOfModulesOfCommRing R} (f : N ⟶ N')
    (hN : ∀ q : ℕ, IsZero (((homFunctor.{c, h, 0} R M).rightDerived (q + 1)).obj N))
    (hN' : ∀ q : ℕ, IsZero (((homFunctor.{c, h, 0} R M).rightDerived (q + 1)).obj N'))
    (q : ℕ) (x : Ext.{eM} M N q) :
    extCohomologyAddEquivOfAcyclic R hT M N' hN' q
        (x.comp (Ext.mk₀ f) (Nat.add_zero q)) =
      Sheaf.H.map ((SheafOfModules.toSheaf
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).map
          (SheafOfModules.InternalHom.map R (𝟙 M) f)) q
        (extCohomologyAddEquivOfAcyclic R hT M N hN q x) := by
  simp only [extCohomologyAddEquivOfAcyclic_apply]
  dsimp only [moduleExtAddEquivOfAcyclic]
  rw [Functor.extAddEquivOfLeftExactAcyclic_naturality,
    ModuleCoefficients.cohomologyMap_naturality]
  rfl

end CategoryTheory.Sheaf.InternalExt

namespace CategoryTheory.Sheaf.InternalExt

/-- The original cohomology comparison followed by a reverse Ext arrow, formed as one
shared additive map before specializing the coefficient carriers. -/
def cohomologyExtReverseAfterComparison
    {A B D : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup D]
    (E : B ≃+ D) (r : B →+ A) : D →+ A :=
  r.comp E.symm.toAddMonoidHom

private theorem reverseAfterComparison_eq_inv
    {A B D : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup D]
    (F : A ≃+ B) (E : B ≃+ D) (T : A ≃+ D) (r : B →+ A)
    (hT : T = F.trans E) (hr : r = F.symm.toAddMonoidHom) :
    cohomologyExtReverseAfterComparison E r = T.symm.toAddMonoidHom := by
  rw [hT, hr]
  rfl

private theorem inverseComparison_square
    {A A' B B' : Type*}
    [AddCommGroup A] [AddCommGroup A'] [AddCommGroup B] [AddCommGroup B']
    (E : A ≃+ B) (E' : A' ≃+ B') (r : B →+ A) (r' : B' →+ A')
    (hr : r = E.symm.toAddMonoidHom) (hr' : r' = E'.symm.toAddMonoidHom)
    (f : A → A') (g : B → B')
    (hE : ∀ x, E' (f x) = g (E x)) (x : B) : r' (g x) = f (r x) := by
  rw [hr, hr']
  change E'.symm (g x) = f (E.symm x)
  apply E'.injective
  simpa only [AddEquiv.apply_symm_apply] using (hE (E.symm x)).symm

variable {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c h} RingCat.{max c h})]
  (R : Sheaf J CommRingCat.{max c h}) [HasSheafify J AddCommGrpCat.{max c h}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c h}]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{max c h})]
  [∀ W : C, HasFiniteProducts (Over W)]
  [HasExt.{eM} (SheafOfModulesOfCommRing R)]
  [HasExt.{eA} (Sheaf J AddCommGrpCat.{max c h})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{max c h})]
  {T : C} (hT : IsTerminal T)

local instance : EnoughInjectives (SheafOfModulesOfCommRing R) :=
  SheafOfModules.enoughInjectivesLarge.{c, h, 0}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)

/-- The canonical reverse module-Ext arrow exists for every original source and target.
Its only image-acyclicity input is the already proved native injective-image theorem. -/
def moduleExtReverse (M N : SheafOfModulesOfCommRing R) (q : ℕ) :
    Ext.{eM}
      (SheafOfModules.liftedUnit.{c, h, max c h, max c h}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
      (sheaf R M N) q →+ Ext.{eM} M N q :=
  Functor.extReverseOfLeftExact.{_, _, _, eM, eM} (homFunctor.{c, h, 0} R M)
    (SheafOfModules.liftedUnit.{c, h, max c h, max c h}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (liftedUnitCoyonedaIso.{c, h, 0} R M)
    (homFunctor_injective_ext_subsingleton R hT M) N q

/-- The cohomology-to-Ext map uses the original module-unit comparison and the canonical
reverse composition map. It is defined without finite local constancy or target acyclicity. -/
def cohomologyExtReverse (M N : SheafOfModulesOfCommRing R) (q : ℕ) :
    Sheaf.H.{eA}
      ((SheafOfModules.toSheaf ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).obj
        (sheaf R M N)) q →+ Ext.{eM} M N q :=
  cohomologyExtReverseAfterComparison
    (ModuleCoefficients.moduleExtCohomologyAddEquivLargeScalars hT
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (sheaf R M N) q)
    (moduleExtReverse R hT M N q)

/-- Actual target acyclicity identifies the all-target reverse module arrow with the
inverse of the original forward equivalence. -/
theorem moduleExtReverse_eq_symm (M N : SheafOfModulesOfCommRing R)
    (hN : ∀ q : ℕ, IsZero (((homFunctor.{c, h, 0} R M).rightDerived (q + 1)).obj N))
    (q : ℕ) :
    moduleExtReverse R hT M N q =
      (moduleExtAddEquivOfAcyclic R hT M N hN q).symm.toAddMonoidHom :=
  Functor.extReverseOfLeftExact_eq_symm.{_, _, _, eM, eM}
    (homFunctor.{c, h, 0} R M)
    (SheafOfModules.liftedUnit.{c, h, max c h, max c h}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (liftedUnitCoyonedaIso.{c, h, 0} R M)
    (homFunctor_injective_ext_subsingleton R hT M) N hN q

/-- For an acyclic target, the original forward cohomology equivalence is exactly the
inverse of the canonical map defined at every source and target. -/
theorem cohomologyExtReverse_eq_symm (M N : SheafOfModulesOfCommRing R)
    (hN : ∀ q : ℕ, IsZero (((homFunctor.{c, h, 0} R M).rightDerived (q + 1)).obj N))
    (q : ℕ) :
    cohomologyExtReverse R hT M N q =
      (extCohomologyAddEquivOfAcyclic R hT M N hN q).symm.toAddMonoidHom := by
  exact reverseAfterComparison_eq_inv
    (moduleExtAddEquivOfAcyclic R hT M N hN q)
    (ModuleCoefficients.moduleExtCohomologyAddEquivLargeScalars hT
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (sheaf R M N) q)
    (extCohomologyAddEquivOfAcyclic R hT M N hN q) (moduleExtReverse R hT M N q)
    rfl (moduleExtReverse_eq_symm R hT M N hN q)

/-- At an actually acyclic target, degree zero retains the existing original
Hom/unit/cohomology normalization. -/
theorem cohomologyExtReverse_zero_of_acyclic (M N : SheafOfModulesOfCommRing R)
    (hN : ∀ q : ℕ, IsZero (((homFunctor.{c, h, 0} R M).rightDerived (q + 1)).obj N)) :
    cohomologyExtReverse R hT M N 0 =
      (extZeroCohomologyAddEquiv R hT M N).symm.toAddMonoidHom := by
  rw [cohomologyExtReverse_eq_symm R hT M N hN 0,
    extCohomologyAddEquivOfAcyclic_zero R hT M N hN]

/-- The canonical reverse arrow on actually acyclic targets preserves the original
internal-Hom coefficient maps and original Sheaf.H.map. -/
theorem cohomologyExtReverse_naturality_of_acyclic (M : SheafOfModulesOfCommRing R)
    {N N' : SheafOfModulesOfCommRing R} (f : N ⟶ N')
    (hN : ∀ q : ℕ, IsZero (((homFunctor.{c, h, 0} R M).rightDerived (q + 1)).obj N))
    (hN' : ∀ q : ℕ, IsZero (((homFunctor.{c, h, 0} R M).rightDerived (q + 1)).obj N'))
    (q : ℕ) (x : Sheaf.H.{eA}
      ((SheafOfModules.toSheaf ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).obj
        (sheaf R M N)) q) :
    cohomologyExtReverse R hT M N' q
        (Sheaf.H.map ((SheafOfModules.toSheaf
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).map
            (SheafOfModules.InternalHom.map R (𝟙 M) f)) q x) =
      (cohomologyExtReverse R hT M N q x).comp (Ext.mk₀ f) (Nat.add_zero q) := by
  exact inverseComparison_square
    (extCohomologyAddEquivOfAcyclic R hT M N hN q)
    (extCohomologyAddEquivOfAcyclic R hT M N' hN' q)
    (cohomologyExtReverse R hT M N q) (cohomologyExtReverse R hT M N' q)
    (cohomologyExtReverse_eq_symm R hT M N hN q)
    (cohomologyExtReverse_eq_symm R hT M N' hN' q)
    (fun y => y.comp (Ext.mk₀ f) (Nat.add_zero q))
    (Sheaf.H.map ((SheafOfModules.toSheaf
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).map
        (SheafOfModules.InternalHom.map R (𝟙 M) f)) q)
    (extCohomologyAddEquivOfAcyclic_naturality R hT M f hN hN' q) x

end CategoryTheory.Sheaf.InternalExt
