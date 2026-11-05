/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Constructible.GenericSupport
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Constructible.GenericTorsionCompactification
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Constructible.SingleCriterion
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Constructible.TorsionSingle
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.SingleHomology
public import Aglib.CategoryTheory.Sites.Torsion.Iso

/-! # Global compactified finiteness for original internally torsion coefficients

The intrinsic native higher-image statement contains no derived model.
One standard realization per category is used only in the support proof.
Actual generic Galois production, original localization and its original
compositors discharge the generic and boundary inputs internally.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u
attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyRingStandard
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyAbStandard
  CategoryTheory.TorsionZMod.Ringed.ringWEqualsLocallyBijectiveStandard
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

/-- Every original compactified higher image of a internally torsion constructible
module over a left-Noetherian ring is constructible. The ring and
underlying additive groups may be infinite. -/
theorem moduleCompactificationHigherImage_torsion_isConstructible
    {X S : Scheme.{u}} [IsNoetherian S]
    (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (Λ : Type (u + 1)) [Ring Λ] [IsNoetherianRing Λ]
    (F : ModuleValuedSheaf X Λ) (hF : Constructible.Modules.IsConstructible F)
    (hFt : Sheaf.IsTorsion ((Constructible.Modules.moduleUnderlying Λ X).obj F))
    (C : Hom.Compactification f) (q : ℕ) :
    Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence S Λ).inverse.obj
        ((moduleCompactificationHigherDirectImage C Λ q).obj
          ((moduleSheafEquivalence X Λ).functor.obj F))) := by
  let : ∀ Y : Scheme.{u}, HasDerivedCategory.{u + 2} (ModuleSheaf Y Λ) :=
    fun _ => HasDerivedCategory.standard _
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : IsNoetherian X := ⟨⟩
  let : ∀ Y : Scheme.{u}, (moduleSheafEquivalence Y Λ).functor.Additive := fun Y =>
    ModuleCat.Sheaf.ConstantRing.moduleSheafEquivalence_functor_additive.{u + 1, u, u + 1, u + 1}
      Y.smallEtaleTopology Λ
  let E := (moduleSheafEquivalence X Λ).functor
  let N : ModuleSheaf X Λ := E.obj F
  have hN : moduleIsTorsion X Λ N :=
    hFt.of_iso ((moduleSheafUnderlyingIso X Λ).app F)
  let K : (moduleTorsionCohomologyPlus X Λ).FullSubcategory :=
    ⟨(DerivedCategory.Plus.singleFunctor (ModuleSheaf X Λ) 0).obj N,
      moduleTorsionSingle_of_isTorsion X Λ N hN⟩
  have hglobal : ∀ n : ℤ, Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence S Λ).inverse.obj
        ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf S Λ) n).obj
          ((moduleExceptionalDirectImagePlus f Λ).obj K))) := by
    apply moduleExceptionalHomology_isConstructible_of_generic_open f Λ K
    intro Y _ _ _ j _
    let Q := Constructible.Modules.moduleInverseImage Λ j
    let : Q.IsLeftAdjoint := (Constructible.Modules.moduleImageAdjunction Λ j).isLeftAdjoint
    let : Q.Additive := Functor.additive_of_preserves_binary_products Q
    let FY := Q.obj F
    have hFY : Constructible.Modules.IsConstructible FY :=
      Constructible.Modules.isConstructible_pullback j hF
    have hFYt := (IsTorsion.inverseImage j hFt).of_mono
      ((Constructible.Modules.moduleInverseImageUnderlyingIso Λ j).hom.app F)
    obtain ⟨U, a, ha, hopen, hdense, hconn, hfin⟩ :=
      exists_dense_open_moduleCompactificationHigherImage_torsion_isConstructible
        (j ≫ f) Λ FY hFY hFYt
    let : IsAffine U := ha
    let : IsOpenImmersion a := hopen
    let : ConnectedSpace U := hconn
    refine ⟨U, a, hopen, inferInstance, ?_⟩
    rw [← Category.assoc] at hfin
    let b := a ≫ j
    let A := (Constructible.Modules.moduleInverseImage Λ a).obj FY
    let EU := (moduleSheafEquivalence U Λ).functor
    let c : (moduleInverseImage b Λ).obj N ≅ EU.obj A :=
      (moduleInverseImageTransportIso b Λ).app N ≪≫
        EU.mapIso ((moduleValuedInverseImage b Λ).mapIso
          ((moduleSheafEquivalence X Λ).unitIso.app F).symm) ≪≫
        EU.mapIso ((Constructible.Modules.moduleInverseImageComp Λ j a).app F)
    let e : (moduleDerivedInverseImage Λ b).obj K.obj ≅
        (DerivedCategory.Plus.singleFunctor (ModuleSheaf U Λ) 0).obj (EU.obj A) :=
      ((moduleInverseImage b Λ).rightDerivedFunctorPlusSingleIso 0).app N ≪≫
        (DerivedCategory.Plus.singleFunctor (ModuleSheaf U Λ) 0).mapIso c
    let D := (moduleExceptionalCompactification (b ≫ f)).toCompactification
    have hD := (moduleCompactificationSingleHomology_isConstructible_iff D Λ (EU.obj A)).mpr
      (hfin D)
    intro n
    exact (Constructible.Modules.isConstructible_iff_of_iso
      ((moduleSheafEquivalence S Λ).inverse.mapIso
        ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf S Λ) n).mapIso
          ((moduleExceptionalChosenAmbientFunctor (b ≫ f) Λ).mapIso e)))).mpr (hD n)
  let : IsLocallyNoetherian C.Xbar := LocallyOfFiniteType.isLocallyNoetherian C.p
  let : CompactSpace C.Xbar := QuasiCompact.compactSpace_of_compactSpace C.p
  let : IsNoetherian C.Xbar := ⟨⟩
  let e := (moduleExceptionalDirectImagePlusIso f Λ (Hom.Compactification.densify C)).app K ≪≫
    (moduleCompactificationDensificationIso C Λ).symm.app K
  apply (moduleCompactificationSingleHomology_isConstructible_iff C Λ N).mp ?_ q
  intro n
  exact (Constructible.Modules.isConstructible_iff_of_iso
    ((moduleSheafEquivalence S Λ).inverse.mapIso
      ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf S Λ) n).mapIso e))).mp (hglobal n)

end AlgebraicGeometry.Scheme.EtaleCohomology
