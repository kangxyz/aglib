/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleUnderlying
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.NativeAdjunctionUnderlying
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.UnderlyingComposition
public import Aglib.CategoryTheory.Sites.SheafCohomology.Slice.CoefficientMates

/-!
# The original module lower-shriek comparison and its adjunction coherence

The comparison already constructed by coefficient equivalence, slice equivalence and
coproduct sheafification is retained. Its actual mate, unit and counit identify the native
module and abelian maps; no compatibility hypothesis is added to a geometric consumer.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.TwoSquare

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  moduleForget_preservesSheafification moduleForget_preservesLeftKanExtensions
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyRingStandard
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyAbStandard
  CategoryTheory.TorsionZMod.Ringed.ringWEqualsLocallyBijectiveStandard
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] (Λ : Type (u + 1)) [Ring Λ]

/-- The actual forward slice comparison is the mate of its literal inverse comparison. -/
theorem mate_moduleEtaleSliceUnderlyingIso_inv :
    (mateEquiv (moduleEtaleSliceSheafEquivalence j Λ).toAdjunction
      (etaleSliceSheafEquivalence (Scheme.Etale.mk j)).toAdjunction
      (TwoSquare.mk _ _ _ _ (moduleEtaleSliceUnderlyingIso j Λ).inv)).natTrans =
        (moduleEtaleSliceInverseUnderlyingIso j Λ).inv :=
  mateEquiv_equivalence_comparison (moduleEtaleSliceSheafEquivalence j Λ)
    (etaleSliceSheafEquivalence (Scheme.Etale.mk j))
    (moduleEtaleSliceInverseUnderlyingIso j Λ) (moduleEtaleSliceUnderlyingIso j Λ) rfl

/-- The actual slice lower-shriek coefficient comparison has the literal restriction mate. -/
theorem mate_sliceLowerShriekCoefficientIso :
    (mateEquiv
      (Sheaf.SliceCohomology.lowerShriekAdjunction (Scheme.smallEtaleTopology X)
        (ModuleCat.{u + 1} Λ) (Scheme.Etale.mk j))
      (Sheaf.SliceCohomology.lowerShriekAdjunction (Scheme.smallEtaleTopology X)
        AddCommGrpCat.{u + 1} (Scheme.Etale.mk j))
      (TwoSquare.mk _ _ _ _
        (Sheaf.SliceCohomology.lowerShriekCoefficientIso
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
          (Scheme.Etale.mk j) (Scheme.smallEtaleTopology X)).hom)).natTrans =
      𝟙 _ :=
  Sheaf.SliceCohomology.mate_lowerShriekCoefficientIso
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) (Scheme.Etale.mk j)
    (Scheme.smallEtaleTopology X)


/-- Literal module-valued restriction and additive restriction have the same original unit. -/
theorem mate_moduleValuedEtaleRestriction :
    (mateEquiv (moduleValuedEtaleRestrictionAdjunction j Λ)
      ((siteEtalePostcomposeAdj j).sheafPushforwardContinuous
        (E := AddCommGrpCat.{u + 1}) (Scheme.smallEtaleTopology U)
        (Scheme.smallEtaleTopology X))
      (TwoSquare.mk
        (sheafCompose (Scheme.smallEtaleTopology X)
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))
        (moduleValuedEtaleRestriction j Λ) (etaleRestriction j)
        (sheafCompose (Scheme.smallEtaleTopology U)
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})) (𝟙 _))).natTrans = 𝟙 _ := by
  let e : moduleValuedEtaleRestriction j Λ ⋙
      sheafCompose (Scheme.smallEtaleTopology U)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ≅
      sheafCompose (Scheme.smallEtaleTopology X)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ⋙ etaleRestriction j := Iso.refl _
  apply mateEquiv_inv_natTrans_eq_of_unit
    (moduleValuedEtaleRestrictionAdjunction j Λ)
    ((siteEtalePostcomposeAdj j).sheafPushforwardContinuous
      (E := AddCommGrpCat.{u + 1}) (Scheme.smallEtaleTopology U)
      (Scheme.smallEtaleTopology X)) e
  intro M
  ext V x
  rfl

/-- The original module-valued inverse-image comparison agrees with literal étale restriction. -/
theorem moduleValuedInverseImageUnderlyingIso_etale :
    Functor.whiskerRight (moduleValuedInverseImageEtaleIso j Λ).hom
        (sheafCompose (Scheme.smallEtaleTopology U)
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})) =
      (moduleValuedInverseImageUnderlyingIso Λ j).hom ≫
        Functor.whiskerLeft
          (sheafCompose (Scheme.smallEtaleTopology X)
            (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))
          (inverseImageEtaleIso j).hom := by
  have hm : (mateEquiv (moduleValuedInverseImageAdjunction j Λ)
      (inverseImageAdjunction j)
      (TwoSquare.mk _ _ _ _ (moduleValuedInverseImageUnderlyingIso Λ j).inv)).natTrans =
        𝟙 _ := by
    apply mateEquiv_inv_natTrans_eq_of_unit _ _ (moduleValuedInverseImageUnderlyingIso Λ j)
    intro M
    simp only [NatTrans.id_app]
    erw [Category.id_comp]
    exact moduleValuedInverseImageUnderlyingIso_unit j Λ M
  have h := Adjunction.underlying_leftAdjointUniq
    (moduleValuedInverseImageAdjunction j Λ) (moduleValuedEtaleRestrictionAdjunction j Λ)
    (inverseImageAdjunction j)
    ((siteEtalePostcomposeAdj j).sheafPushforwardContinuous
      (E := AddCommGrpCat.{u + 1}) (Scheme.smallEtaleTopology U)
      (Scheme.smallEtaleTopology X))
    (moduleValuedInverseImageUnderlyingIso Λ j) (Iso.refl _) (Iso.refl _)
    hm (mate_moduleValuedEtaleRestriction j Λ)
  change Functor.whiskerRight (moduleValuedInverseImageEtaleIso j Λ).hom
      (sheafCompose (Scheme.smallEtaleTopology U)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})) ≫ 𝟙 _ = _ at h
  exact (Category.comp_id _).symm.trans h

/-- The original module-valued lower-shriek comparison is normalized by literal restriction. -/
theorem mate_moduleValuedLowerShriekRestrictionUnderlyingIso :
    (mateEquiv (moduleValuedLowerShriekRestrictionAdjunction j Λ)
      (etaleLowerShriekRestrictionAdjunction j)
      (TwoSquare.mk _ _ _ _ (moduleValuedLowerShriekUnderlyingIso j Λ).inv)).natTrans =
        𝟙 _ := by
  let EM := moduleEtaleSliceSheafEquivalence j Λ
  let EA := etaleSliceSheafEquivalence (Scheme.Etale.mk j)
  let A := Sheaf.SliceCohomology.lowerShriekAdjunction (Scheme.smallEtaleTopology X)
    (ModuleCat.{u + 1} Λ) (Scheme.Etale.mk j)
  let B := Sheaf.SliceCohomology.lowerShriekAdjunction (Scheme.smallEtaleTopology X)
    AddCommGrpCat.{u + 1} (Scheme.Etale.mk j)
  have ha : moduleValuedLowerShriekRestrictionAdjunction j Λ = EM.toAdjunction.comp A := by
    apply Adjunction.ext
    apply NatTrans.ext
    funext M
    change (EM.toAdjunction.comp A).unit.app M ≫ 𝟙 _ = (EM.toAdjunction.comp A).unit.app M
    exact Category.comp_id _
  rw [ha]
  exact mateEquiv_composite_comparison EM.toAdjunction EA.toAdjunction A B
    (moduleEtaleSliceUnderlyingIso j Λ)
    (Sheaf.SliceCohomology.lowerShriekCoefficientIso
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) (Scheme.Etale.mk j)
      (Scheme.smallEtaleTopology X)).symm
    (moduleValuedLowerShriekUnderlyingIso j Λ) rfl
    (moduleEtaleSliceInverseUnderlyingIso j Λ).symm (Iso.refl _) (Iso.refl _)
    (by apply Iso.ext; apply NatTrans.ext; funext M; rfl)
    (mate_moduleEtaleSliceUnderlyingIso_inv j Λ) (mate_sliceLowerShriekCoefficientIso j Λ)

/-- Transport to the original inverse images retains the same lower-shriek comparison. -/
theorem mate_moduleValuedLowerShriekUnderlyingIso_inv :
    (mateEquiv (moduleValuedLowerShriekAdjunction j Λ) (etaleLowerShriekAdjunction j)
      (TwoSquare.mk _ _ _ _ (moduleValuedLowerShriekUnderlyingIso j Λ).inv)).natTrans =
        (moduleValuedInverseImageUnderlyingIso Λ j).hom := by
  apply mateEquiv_ofNatIsoRight_comparison
    (moduleValuedLowerShriekRestrictionAdjunction j Λ) (etaleLowerShriekRestrictionAdjunction j)
    (moduleValuedInverseImageEtaleIso j Λ).symm (inverseImageEtaleIso j).symm
    (moduleValuedLowerShriekUnderlyingIso j Λ) (Iso.refl _)
    (moduleValuedInverseImageUnderlyingIso Λ j)
    (mate_moduleValuedLowerShriekRestrictionUnderlyingIso j Λ)
  have h := Iso.inv_comp_of_hom_eq_comp
    (Functor.isoWhiskerRight (moduleValuedInverseImageEtaleIso j Λ)
      (sheafCompose (Scheme.smallEtaleTopology U)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})))
    (moduleValuedInverseImageUnderlyingIso Λ j)
    (Functor.isoWhiskerLeft
      (sheafCompose (Scheme.smallEtaleTopology X)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})) (inverseImageEtaleIso j))
    (moduleValuedInverseImageUnderlyingIso_etale j Λ)
  exact h.trans (Category.id_comp _).symm

/-- The original coefficient equivalence and its existing underlying iso form a mate square. -/
theorem mate_moduleSheafUnderlyingIso_inv (Y : Scheme.{u}) :
    (mateEquiv (moduleSheafEquivalence Y Λ).toAdjunction Adjunction.id
      (TwoSquare.mk
        (sheafCompose (Scheme.smallEtaleTopology Y)
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))
        (moduleSheafEquivalence Y Λ).functor (𝟭 (AbelianSheaf.{u, u + 1} Y))
        (SheafOfModules.toSheaf (constantRing Y Λ)) (moduleSheafUnderlyingIso Y Λ).inv)).natTrans =
        (moduleSheafInverseUnderlyingIso Y Λ).hom := by
  apply mateEquiv_inv_natTrans_eq_of_unit
    (U := sheafCompose (Scheme.smallEtaleTopology Y)
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))
    (V := SheafOfModules.toSheaf (constantRing Y Λ))
    (moduleSheafEquivalence Y Λ).toAdjunction (Adjunction.id (C := AbelianSheaf.{u, u + 1} Y))
    (moduleSheafUnderlyingIso Y Λ)
  intro M
  change (sheafCompose (Scheme.smallEtaleTopology Y)
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
        ((moduleSheafEquivalence Y Λ).unitIso.hom.app M) ≫
    (moduleSheafInverseUnderlyingIso Y Λ).hom.app ((moduleSheafEquivalence Y Λ).functor.obj M) ≫
      (moduleSheafUnderlyingIso Y Λ).hom.app M = 𝟙 _
  have hu := moduleSheafEquivalence_unit_underlying Y Λ M
  have hd := moduleSheafInverseUnderlyingIso_hom_app Y Λ
    ((moduleSheafEquivalence Y Λ).functor.obj M)
  exact (congrArg₂ (fun a b => a ≫ b ≫ (moduleSheafUnderlyingIso Y Λ).hom.app M) hu hd).trans
    ((congrArg (fun a => (moduleSheafUnderlyingIso Y Λ).inv.app M ≫ a)
      (Category.id_comp ((moduleSheafUnderlyingIso Y Λ).hom.app M))).trans
        ((moduleSheafUnderlyingIso Y Λ).inv_hom_id_app M))

/-- The inverse coefficient equivalence uses its original inverse counit as unit. -/
theorem mate_moduleSheafInverseUnderlyingIso_inv (Y : Scheme.{u}) :
    (mateEquiv (moduleSheafEquivalence Y Λ).symm.toAdjunction Adjunction.id
      (TwoSquare.mk (SheafOfModules.toSheaf (constantRing Y Λ))
        (moduleSheafEquivalence Y Λ).inverse (𝟭 (AbelianSheaf.{u, u + 1} Y))
        (sheafCompose (Scheme.smallEtaleTopology Y)
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))
        (moduleSheafInverseUnderlyingIso Y Λ).inv)).natTrans =
        (moduleSheafUnderlyingIso Y Λ).hom := by
  apply mateEquiv_inv_natTrans_eq_of_unit
    (U := SheafOfModules.toSheaf (constantRing Y Λ))
    (V := sheafCompose (Scheme.smallEtaleTopology Y)
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))
    (moduleSheafEquivalence Y Λ).symm.toAdjunction
    (Adjunction.id (C := AbelianSheaf.{u, u + 1} Y)) (moduleSheafInverseUnderlyingIso Y Λ)
  intro M
  change (SheafOfModules.toSheaf (constantRing Y Λ)).map
      ((moduleSheafEquivalence Y Λ).counitIso.inv.app M) ≫
    (moduleSheafUnderlyingIso Y Λ).hom.app ((moduleSheafEquivalence Y Λ).inverse.obj M) ≫
      (moduleSheafInverseUnderlyingIso Y Λ).hom.app M = 𝟙 _
  have hc := moduleSheafEquivalence_counit_inv_underlying Y Λ M
  have hd := moduleSheafInverseUnderlyingIso_hom_app Y Λ M
  exact (congrArg₂ (fun a b => a ≫ (moduleSheafUnderlyingIso Y Λ).hom.app
      ((moduleSheafEquivalence Y Λ).inverse.obj M) ≫ b) hc hd).trans
    ((congrArg (fun a => (moduleSheafUnderlyingIso Y Λ).inv.app
      ((moduleSheafEquivalence Y Λ).inverse.obj M) ≫ a)
      (Category.comp_id ((moduleSheafUnderlyingIso Y Λ).hom.app
        ((moduleSheafEquivalence Y Λ).inverse.obj M)))).trans
          ((moduleSheafUnderlyingIso Y Λ).inv_hom_id_app
            ((moduleSheafEquivalence Y Λ).inverse.obj M)))

/-- The actual native lower-shriek comparison is the mate of the actual inverse-image comparison. -/
theorem mate_moduleLowerShriekUnderlyingIso_inv :
    (mateEquiv (moduleLowerShriekAdjunction j Λ) (etaleLowerShriekAdjunction j)
      (TwoSquare.mk _ _ _ _ (moduleLowerShriekUnderlyingIso j Λ).inv)).natTrans =
        (moduleInverseImageUnderlyingIso Λ j).hom := by
  let EU := moduleSheafEquivalence U Λ
  let EX := moduleSheafEquivalence X Λ
  let QU := SheafOfModules.toSheaf (constantRing U Λ)
  let QX := SheafOfModules.toSheaf (constantRing X Λ)
  let q := moduleLowerShriekRightIso j Λ
  let d := Functor.isoWhiskerRight q QU ≪≫ moduleInverseImageUnderlyingIso Λ j
  have ht : (mateEquiv (moduleLowerShriekTransportAdjunction j Λ)
      (etaleLowerShriekAdjunction j)
      (TwoSquare.mk _ _ _ _ (moduleLowerShriekUnderlyingIso j Λ).inv)).natTrans = d.hom := by
    let s₁ := TwoSquare.mk QU EU.inverse (𝟭 (AbelianSheaf.{u, u + 1} U))
      (sheafCompose (Scheme.smallEtaleTopology U)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))
      (moduleSheafInverseUnderlyingIso U Λ).inv
    let s₂ := TwoSquare.mk _ (moduleValuedLowerShriek j Λ) (etaleLowerShriek j) _
      (moduleValuedLowerShriekUnderlyingIso j Λ).inv
    let s₃ := TwoSquare.mk
      (sheafCompose (Scheme.smallEtaleTopology X)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))
      EX.functor (𝟭 (AbelianSheaf.{u, u + 1} X)) QX
      (moduleSheafUnderlyingIso X Λ).inv
    have hs : TwoSquare.mk _ _ _ _ (moduleLowerShriekUnderlyingIso j Λ).inv =
        (s₁ ≫ᵥ s₂) ≫ᵥ s₃ := by
      apply TwoSquare.ext
      intro M
      change (moduleLowerShriekUnderlyingIso j Λ).inv.app M =
        (etaleLowerShriek j).map ((moduleSheafInverseUnderlyingIso U Λ).inv.app M) ≫
          (moduleValuedLowerShriekUnderlyingIso j Λ).inv.app
            ((moduleSheafEquivalence U Λ).inverse.obj M) ≫
          (moduleSheafUnderlyingIso X Λ).inv.app ((moduleValuedLowerShriek j Λ).obj
            ((moduleSheafEquivalence U Λ).inverse.obj M))
      exact Functor.underlyingLowerShriek_inv_app
        (moduleSheafEquivalence U Λ).inverse (moduleValuedLowerShriek j Λ)
        (moduleSheafEquivalence X Λ).functor (SheafOfModules.toSheaf (constantRing X Λ))
        (sheafCompose (Scheme.smallEtaleTopology X)
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))
        (sheafCompose (Scheme.smallEtaleTopology U)
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))
        (etaleLowerShriek j) (SheafOfModules.toSheaf (constantRing U Λ))
        (moduleSheafUnderlyingIso X Λ) (moduleValuedLowerShriekUnderlyingIso j Λ)
        (moduleSheafInverseUnderlyingIso U Λ) (moduleLowerShriekUnderlyingIso j Λ) rfl M
    have ha : ((Adjunction.id.comp (etaleLowerShriekAdjunction j)).comp Adjunction.id) =
        etaleLowerShriekAdjunction j := by
      apply Adjunction.ext
      apply NatTrans.ext
      funext M
      simp [Adjunction.comp_unit_app, Adjunction.id]
    change (mateEquiv ((EU.symm.toAdjunction.comp
        (moduleValuedLowerShriekAdjunction j Λ)).comp EX.toAdjunction)
      (etaleLowerShriekAdjunction j) _).natTrans = _
    rw [← ha, hs, mateEquiv_hcomp, mateEquiv_hcomp]
    apply NatTrans.ext
    funext M
    simp only [TwoSquare.hComp_app, TwoSquare.natTrans]
    rw [congr_app (mate_moduleSheafInverseUnderlyingIso_inv Λ U),
      congr_app (mate_moduleValuedLowerShriekUnderlyingIso_inv j Λ),
      congr_app (mate_moduleSheafUnderlyingIso_inv Λ X)]
    simp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.id_map]
    dsimp only [d, q, QU, EU, EX]
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app]
    rw [Coefficients.moduleInverseImageUnderlyingIso_eq_original]
    simp only [moduleLowerShriekRightIso, Equivalence.coefficientRightIso, Iso.trans_hom,
      Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.assoc]
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    let N := (((moduleSheafEquivalence X Λ).inverse ⋙ moduleValuedInverseImage j Λ) ⋙
      (moduleSheafEquivalence U Λ).functor).obj M
    let a : QU.obj N ⟶ (inverseImage j).obj (QX.obj M) :=
      (moduleSheafUnderlyingIso U Λ).hom.app ((moduleValuedInverseImage j Λ).obj
        ((moduleSheafEquivalence X Λ).inverse.obj M)) ≫
      (moduleValuedInverseImageUnderlyingIso Λ j).hom.app
        ((moduleSheafEquivalence X Λ).inverse.obj M) ≫
      (inverseImage j).map ((moduleSheafInverseUnderlyingIso X Λ).hom.app M)
    change a = QU.map (𝟙 N) ≫ a
    exact ((congrArg (fun t => t ≫ a) (QU.map_id N)).trans (Category.id_comp a)).symm
  have ha : (etaleLowerShriekAdjunction j).ofNatIsoRight (Iso.refl _) =
      etaleLowerShriekAdjunction j := by
    apply Adjunction.ext
    apply NatTrans.ext
    funext M
    simp [Adjunction.ofNatIsoRight]
  rw [← ha]
  apply mateEquiv_ofNatIsoRight_comparison
    (moduleLowerShriekTransportAdjunction j Λ) (etaleLowerShriekAdjunction j)
    q (Iso.refl _) (moduleLowerShriekUnderlyingIso j Λ) d
    (moduleInverseImageUnderlyingIso Λ j) ht
  apply NatTrans.ext
  funext M
  change QU.map (q.hom.app M) ≫ (moduleInverseImageUnderlyingIso Λ j).hom.app M =
    QU.map (q.hom.app M) ≫ (moduleInverseImageUnderlyingIso Λ j).hom.app M
  rfl

/-- The whole native module counit agrees with the original abelian counit under forgetting. -/
theorem moduleLowerShriekUnderlyingIso_counit :
    Functor.whiskerRight (moduleLowerShriekAdjunction j Λ).counit
        (SheafOfModules.toSheaf (constantRing X Λ)) ≫
      (Functor.leftUnitor (SheafOfModules.toSheaf (constantRing X Λ))).hom =
    (Functor.associator (moduleInverseImage j Λ) (moduleLowerShriek j Λ)
      (SheafOfModules.toSheaf (constantRing X Λ))).hom ≫
      Functor.whiskerLeft (moduleInverseImage j Λ) (moduleLowerShriekUnderlyingIso j Λ).hom ≫
      (Functor.associator (moduleInverseImage j Λ)
        (SheafOfModules.toSheaf (constantRing U Λ)) (etaleLowerShriek j)).inv ≫
      Functor.whiskerRight (moduleInverseImageUnderlyingIso Λ j).hom (etaleLowerShriek j) ≫
      (Functor.associator (SheafOfModules.toSheaf (constantRing X Λ))
        (inverseImage j) (etaleLowerShriek j)).hom ≫
      Functor.whiskerLeft (SheafOfModules.toSheaf (constantRing X Λ))
        (etaleLowerShriekAdjunction j).counit ≫
      (Functor.rightUnitor (SheafOfModules.toSheaf (constantRing X Λ))).hom :=
  Adjunction.underlying_counit (moduleLowerShriekAdjunction j Λ) (etaleLowerShriekAdjunction j)
    (moduleLowerShriekUnderlyingIso j Λ) (moduleInverseImageUnderlyingIso Λ j)
    (mate_moduleLowerShriekUnderlyingIso_inv j Λ)

/-- Evaluation of the whole original module/abelian counit equation. -/
theorem moduleLowerShriekUnderlyingIso_counit_app (M : ModuleSheaf X Λ) :
    (SheafOfModules.toSheaf (constantRing X Λ)).map
      ((moduleLowerShriekAdjunction j Λ).counit.app M) =
    (moduleLowerShriekUnderlyingIso j Λ).hom.app ((moduleInverseImage j Λ).obj M) ≫
      (etaleLowerShriek j).map ((moduleInverseImageUnderlyingIso Λ j).hom.app M) ≫
      (etaleLowerShriekAdjunction j).counit.app
        ((SheafOfModules.toSheaf (constantRing X Λ)).obj M) :=
  Adjunction.underlying_counit_app (moduleLowerShriekAdjunction j Λ)
    (etaleLowerShriekAdjunction j) (moduleLowerShriekUnderlyingIso j Λ)
    (moduleInverseImageUnderlyingIso Λ j) (mate_moduleLowerShriekUnderlyingIso_inv j Λ) M

/-- The original native unit is normalized by the same full mate square. -/
theorem moduleLowerShriekUnderlyingIso_unit_app (M : ModuleSheaf U Λ) :
    (SheafOfModules.toSheaf (constantRing U Λ)).map
        ((moduleLowerShriekAdjunction j Λ).unit.app M) ≫
      (moduleInverseImageUnderlyingIso Λ j).hom.app ((moduleLowerShriek j Λ).obj M) ≫
      (inverseImage j).map ((moduleLowerShriekUnderlyingIso j Λ).hom.app M) =
    (etaleLowerShriekAdjunction j).unit.app
      ((SheafOfModules.toSheaf (constantRing U Λ)).obj M) :=
  Adjunction.underlying_unit_app (moduleLowerShriekAdjunction j Λ)
    (etaleLowerShriekAdjunction j) (moduleLowerShriekUnderlyingIso j Λ)
    (moduleInverseImageUnderlyingIso Λ j) (mate_moduleLowerShriekUnderlyingIso_inv j Λ) M

end AlgebraicGeometry.Scheme.EtaleCohomology
