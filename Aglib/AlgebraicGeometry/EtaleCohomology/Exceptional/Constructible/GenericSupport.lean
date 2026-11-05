/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Constructible.ClosedSourceReduction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteStratification.PropertyInduction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.InverseImageTorsionCoherence

/-! # Global exceptional constructibility from actual generic-open images

The geometric support induction is instantiated on original inverse images
of one native torsion D+ input. The original inverse-image compositor
identifies each induction vertex with the corresponding localization vertex.
A supplied uniform family chooses one derived realization per scheme;
there is no change of coefficient, functor, or arrow in the induction.
The generic-open finiteness premise remains explicit in this general lemma.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u w
attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyRingStandard
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyAbStandard
  CategoryTheory.TorsionZMod.Ringed.ringWEqualsLocallyBijectiveStandard
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

/-- Generic integral-open finiteness for the original restrictions of a native
torsion D+ input implies finiteness of its original whole exceptional image.
The supplied realization family is used consistently at every source and
compactification in the actual support induction. -/
theorem moduleExceptionalHomology_isConstructible_of_generic_open
    {X S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S]
    (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (Λ : Type (u + 1)) [Ring Λ] [IsNoetherianRing Λ]
    [models : ∀ Y : Scheme.{u}, HasDerivedCategory.{w} (ModuleSheaf Y Λ)]
    (K : (moduleTorsionCohomologyPlus X Λ).FullSubcategory)
    (hgeneric : ∀ (Y : Scheme.{u}) [IsNoetherian Y] [IsAffine Y] [IsIntegral Y]
      (j : Y ⟶ X) [IsImmersion j],
      ∃ (U : Scheme.{u}) (a : U ⟶ Y) (ha : IsOpenImmersion a),
        letI := ha
        Nonempty U ∧
        ∀ n : ℤ, Constructible.Modules.IsConstructible
          ((moduleSheafEquivalence S Λ).inverse.obj
            ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf S Λ) n).obj
              ((moduleExceptionalDirectImagePlus ((a ≫ j) ≫ f) Λ).obj
                ((moduleDerivedInverseImageTorsion (a ≫ j) Λ).obj K))))) :
    ∀ n : ℤ, Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence S Λ).inverse.obj
        ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf S Λ) n).obj
          ((moduleExceptionalDirectImagePlus f Λ).obj K))) := by
  let : (moduleSheafEquivalence S Λ).inverse.Additive :=
    ModuleCat.Sheaf.ConstantRing.moduleSheafEquivalence_inverse_additive.{u + 1, u, u + 1, u + 1}
      S.smallEtaleTopology Λ
  let P : ∀ {Y : Scheme.{u}}, (Y ⟶ X) → Prop := fun {Y} j =>
    ∀ [IsNoetherian Y] [IsImmersion j], ∀ n : ℤ,
      Constructible.Modules.IsConstructible
        ((moduleSheafEquivalence S Λ).inverse.obj
          ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf S Λ) n).obj
            ((moduleExceptionalDirectImagePlus (j ≫ f) Λ).obj
              ((moduleDerivedInverseImageTorsion j Λ).obj K))))
  have hP : P (𝟙 X) := by
    apply Constructible.property_of_noetherian_generic_open_closed P
    · intro Y j hY _ _ n
      let : IsEmpty Y := hY
      exact ObjectProperty.prop_of_isZero Constructible.Modules.IsConstructible
        ((moduleSheafEquivalence S Λ).inverse.map_isZero
          ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf S Λ) n).map_isZero
            (moduleExceptional_isZero_of_empty (j ≫ f) Λ
              ((moduleDerivedInverseImageTorsion j Λ).obj K))))
    · intro Y _ _ _ j _
      obtain ⟨U, a, ha, hU, hfin⟩ := hgeneric Y j
      let : IsOpenImmersion a := ha
      refine ⟨U, a, ha, hU, ?_⟩
      intro _ _ n
      exact hfin n
    · intro Y j hj _ U a _ hU hZ _ _
      let : IsClosedImmersion j := hj
      let I := IdealSheafData.vanishingIdeal a.opensRange.compl
      let : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian a
      let : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace a
      let : IsNoetherian U := ⟨⟩
      let : IsLocallyNoetherian I.subscheme :=
        LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
      let : CompactSpace I.subscheme :=
        QuasiCompact.compactSpace_of_compactSpace I.subschemeι
      let : IsNoetherian I.subscheme := ⟨⟩
      have hc : Set.range a = (Set.range I.subschemeι)ᶜ := by
        rw [IdealSheafData.range_subschemeι,
          IdealSheafData.coe_support_vanishingIdeal]
        exact (compl_compl (Set.range a)).symm
      apply moduleExceptionalHomology_isConstructible_of_localization
        (j ≫ f) a I.subschemeι Λ hc ((moduleDerivedInverseImageTorsion j Λ).obj K)
      · intro n
        let e := (moduleDerivedInverseImageTorsionCompIso Λ j a).app K
        have h := hU n
        exact (Constructible.Modules.isConstructible_iff_of_iso
          ((moduleSheafEquivalence S Λ).inverse.mapIso
            ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf S Λ) n).mapIso
              ((moduleExceptionalDirectImagePlus (a ≫ (j ≫ f)) Λ).mapIso e)))).mp h
      · intro n
        let e := (moduleDerivedInverseImageTorsionCompIso Λ j I.subschemeι).app K
        have h := hZ n
        exact (Constructible.Modules.isConstructible_iff_of_iso
          ((moduleSheafEquivalence S Λ).inverse.mapIso
            ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf S Λ) n).mapIso
              ((moduleExceptionalDirectImagePlus (I.subschemeι ≫ (j ≫ f)) Λ).mapIso e)))).mp h
    · intro Y j hj _ hsurj hY _ _ n
      let : IsClosedImmersion j := hj
      let : Surjective j := hsurj
      let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian j
      let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace j
      let : IsNoetherian Y := ⟨⟩
      let U : X.Opens := ⊥
      let : IsEmpty U.toScheme := ⟨fun x => x.2⟩
      have hc : Set.range U.ι = (Set.range j)ᶜ := by
        rw [Set.range_eq_univ.mpr j.surjective, Set.compl_univ]
        exact Set.range_eq_empty U.ι
      have h := moduleExceptionalHomology_isConstructible_of_empty_open
        f U.ι j Λ hc K (fun q => hY q) n
      change Constructible.Modules.IsConstructible
        ((moduleSheafEquivalence S Λ).inverse.obj
          ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf S Λ) n).obj
            ((moduleExceptionalDirectImagePlus f Λ).obj
              ((moduleDerivedInverseImageTorsion (𝟙 X) Λ).obj K))))
      exact (Constructible.Modules.isConstructible_iff_of_iso
        ((moduleSheafEquivalence S Λ).inverse.mapIso
          ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf S Λ) n).mapIso
            ((moduleExceptionalDirectImagePlus f Λ).mapIso
              ((moduleDerivedInverseImageTorsionIdIso Λ X).app K))))).mpr h
  intro n
  have h := hP n
  exact (Constructible.Modules.isConstructible_iff_of_iso
    ((moduleSheafEquivalence S Λ).inverse.mapIso
      ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf S Λ) n).mapIso
        ((moduleExceptionalDirectImagePlus f Λ).mapIso
          ((moduleDerivedInverseImageTorsionIdIso Λ X).app K))))).mp h

end AlgebraicGeometry.Scheme.EtaleCohomology
