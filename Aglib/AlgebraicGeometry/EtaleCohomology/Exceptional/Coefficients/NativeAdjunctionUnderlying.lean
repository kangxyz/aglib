/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.AdjunctionUnderlying
public import Aglib.CategoryTheory.Adjunction.UnderlyingEquivalence
public import Aglib.CategoryTheory.Adjunction.UnderlyingMate

/-!
# The original native adjunction under additive coefficient forgetting

The existing native pullback comparison preserves the original adjunction unit.
The proof uses the native module-sheafification counit and the triangle identities
of the existing coefficient equivalence. In particular, it does not replace the
specified pullback comparison by a newly chosen mate.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  moduleForget_preservesSheafification

variable (X : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ]

/-- The counit of the original coefficient equivalence has its prescribed
abelian-sheafification comparison underneath. -/
@[reassoc]
theorem moduleSheafEquivalence_counit_underlying (M : ModuleSheaf X Λ) :
    (SheafOfModules.toSheaf (constantRing X Λ)).map
        ((moduleSheafEquivalence X Λ).counitIso.hom.app M) =
      (moduleSheafUnderlyingIso X Λ).hom.app
        ((moduleSheafEquivalence X Λ).inverse.obj M) := by
  let C := CategoryTheory.TorsionZMod.Ringed.constantSheafEquivalence.{u + 1, u, u + 1, u + 1}
    (Scheme.smallEtaleTopology X) Λ
  let E := constantModuleSheafificationEquivalence X Λ
  let V := CategoryTheory.TorsionZMod.Ringed.moduleUnderlyingSheaf.{u + 1, u, u + 1, u + 1}
    (Scheme.smallEtaleTopology X)
    ((Functor.const X.Etaleᵒᵖ).obj (RingCat.of Λ))
  let U := SheafOfModules.toSheaf (constantRing X Λ)
  let c := constantModuleSheafificationUnderlyingIso X Λ
  let d := CategoryTheory.TorsionZMod.Ringed.constantSheafUnderlyingIso.{u + 1, u, u + 1, u + 1}
    (Scheme.smallEtaleTopology X) Λ
  have hc : V.map (C.counitIso.hom.app (E.inverse.obj M)) =
      d.hom.app (C.inverse.obj (E.inverse.obj M)) := by
    apply ObjectProperty.hom_ext
    ext W x
    rfl
  have hE : U.map (E.counitIso.hom.app M) =
      c.hom.app (E.inverse.obj M) := by
    exact PresheafOfModules.toSheaf_map_sheafificationAdjunction_counit_app
      (constantRingUnit X Λ) M
  simp only [moduleSheafEquivalence, moduleSheafUnderlyingIso]
  change U.map (E.functor.map (C.counitIso.hom.app (E.inverse.obj M))) ≫
      U.map (E.counitIso.hom.app M) =
    c.hom.app (C.functor.obj (C.inverse.obj (E.inverse.obj M))) ≫
      d.hom.app (C.inverse.obj (E.inverse.obj M))
  erw [hE, c.hom.naturality, hc]
  rfl

/-- The inverse counit retains the inverse of the specified underlying comparison. -/
theorem moduleSheafEquivalence_counit_inv_underlying (M : ModuleSheaf X Λ) :
    (SheafOfModules.toSheaf (constantRing X Λ)).map
        ((moduleSheafEquivalence X Λ).counitIso.inv.app M) =
      (moduleSheafUnderlyingIso X Λ).inv.app
        ((moduleSheafEquivalence X Λ).inverse.obj M) := by
  have h : (SheafOfModules.toSheaf (constantRing X Λ)).mapIso
      ((moduleSheafEquivalence X Λ).counitIso.app M) =
      (moduleSheafUnderlyingIso X Λ).app
        ((moduleSheafEquivalence X Λ).inverse.obj M) :=
    Iso.ext (moduleSheafEquivalence_counit_underlying X Λ M)
  exact congrArg Iso.inv h

/-- The already specified inverse-equivalence comparison is the identity on the
original abelian sheaf. -/
theorem moduleSheafInverseUnderlyingIso_hom_app (M : ModuleSheaf X Λ) :
    (moduleSheafInverseUnderlyingIso X Λ).hom.app M =
      𝟙 ((SheafOfModules.toSheaf (constantRing X Λ)).obj M) := by
  simp only [moduleSheafInverseUnderlyingIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.leftUnitor_hom_app,
    Category.id_comp]
  erw [moduleSheafEquivalence_counit_underlying, Iso.inv_hom_id_app_assoc]

/-- The fixed inverse-equivalence comparison is the identity natural isomorphism. -/
theorem moduleSheafInverseUnderlyingIso_eq_refl :
    moduleSheafInverseUnderlyingIso X Λ =
      Iso.refl (SheafOfModules.toSheaf (constantRing X Λ)) := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  exact moduleSheafInverseUnderlyingIso_hom_app X Λ M

/-- The equivalence unit becomes the inverse of the existing underlying comparison. -/
theorem moduleSheafEquivalence_unit_underlying (M : ModuleValuedSheaf X Λ) :
    (sheafCompose (Scheme.smallEtaleTopology X)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
          ((moduleSheafEquivalence X Λ).unitIso.hom.app M) =
      (moduleSheafUnderlyingIso X Λ).inv.app M := by
  exact Equivalence.unit_map_eq_inv (moduleSheafEquivalence X Λ)
    (sheafCompose (Scheme.smallEtaleTopology X)
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))
    (moduleSheafUnderlyingIso X Λ)
    (moduleSheafEquivalence_counit_underlying X Λ) M

variable {X} {S : Scheme.{u}} (f : S ⟶ X)

/-- The inverse direct-image transport has exactly the existing coefficient
comparison underneath; restriction of scalars retains every additive map. -/
theorem moduleDirectImageTransportIso_inv_underlying (M : ModuleSheaf S Λ) :
    (SheafOfModules.toSheaf (constantRing X Λ)).map
        ((moduleDirectImageTransportIso f Λ).inv.app M) =
      (moduleSheafUnderlyingIso X Λ).hom.app
        ((moduleValuedDirectImage f Λ).obj
          ((moduleSheafEquivalence S Λ).inverse.obj M)) := by
  have hq : (sheafCompose (Scheme.smallEtaleTopology X)
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
        ((moduleDirectImageComparison f Λ).inv.app M) =
      𝟙 ((SheafOfModules.toSheaf (constantRing X Λ)).obj
        ((moduleDirectImage f Λ).obj M)) := by
    apply ObjectProperty.hom_ext
    ext W x
    rfl
  have ht := Equivalence.transportRightIso_inv_app (moduleSheafEquivalence X Λ)
    (moduleDirectImage f Λ) (moduleSheafEquivalence S Λ).inverse
    (moduleValuedDirectImage f Λ) (moduleDirectImageComparison f Λ) M
  have hn := Equivalence.map_functor_comp_counit (moduleSheafEquivalence X Λ)
    (sheafCompose (Scheme.smallEtaleTopology X)
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))
    (moduleSheafUnderlyingIso X Λ)
    (moduleSheafEquivalence_counit_underlying X Λ)
    ((moduleDirectImageComparison f Λ).inv.app M)
  exact (congrArg (SheafOfModules.toSheaf (constantRing X Λ)).map ht).trans
    (hn.trans ((congrArg (fun k =>
      (moduleSheafUnderlyingIso X Λ).hom.app
        ((moduleValuedDirectImage f Λ).obj
          ((moduleSheafEquivalence S Λ).inverse.obj M)) ≫ k) hq).trans
      (Category.comp_id _)))

/-- The unit transported through the existing equivalences becomes the original
module-valued unit, after its specified underlying comparison. -/
@[reassoc]
theorem moduleTransportAdjunction_unit_underlying (M : ModuleSheaf X Λ) :
    (SheafOfModules.toSheaf (constantRing X Λ)).map
        ((moduleTransportAdjunction f Λ).unit.app M) ≫
      (directImage f).map ((moduleSheafUnderlyingIso S Λ).hom.app
        ((moduleValuedInverseImage f Λ).obj
          ((moduleSheafEquivalence X Λ).inverse.obj M))) =
      (sheafCompose (Scheme.smallEtaleTopology X)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
          ((moduleValuedInverseImageAdjunction f Λ).unit.app
            ((moduleSheafEquivalence X Λ).inverse.obj M)) := by
  let EX := moduleSheafEquivalence X Λ
  let ES := moduleSheafEquivalence S Λ
  let U := SheafOfModules.toSheaf (constantRing X Λ)
  let V := sheafCompose (Scheme.smallEtaleTopology X)
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  let P := (moduleValuedInverseImage f Λ).obj (EX.inverse.obj M)
  let a := (moduleValuedInverseImageAdjunction f Λ).unit.app (EX.inverse.obj M)
  let b := (moduleValuedDirectImage f Λ).map (ES.unitIso.hom.app P)
  let k := (directImage f).map ((moduleSheafUnderlyingIso S Λ).hom.app P)
  have hk : V.map b ≫ k = 𝟙 _ := by
    have h := congrArg (fun z => (directImage f).map z ≫ k)
      (moduleSheafEquivalence_unit_underlying S Λ P)
    exact h.trans ((directImage f).mapIso ((moduleSheafUnderlyingIso S Λ).app P)).inv_hom_id
  have hn := NatIso.inv_map_map_hom_comp (moduleSheafUnderlyingIso X Λ) a b k hk
  have ht := Adjunction.equivalence_transport_unit EX ES
    (moduleValuedInverseImageAdjunction f Λ) (moduleDirectImageTransportIso f Λ) M
  have hm := congrArg (fun z => U.map z ≫ k) ht
  simp only [Functor.map_comp] at hm
  have hc := congrArg₂ (fun p q => p ≫ U.map (EX.functor.map a) ≫
      U.map (EX.functor.map b) ≫ q ≫ k)
    (moduleSheafEquivalence_counit_inv_underlying X Λ M)
    (moduleDirectImageTransportIso_inv_underlying Λ f (ES.functor.obj P))
  exact hm.trans (hc.trans hn)

/-- The fixed native inverse-image comparison preserves the original native
unit and the original abelian unit. -/
@[reassoc]
theorem moduleInverseImageUnderlyingIso_unit (M : ModuleSheaf X Λ) :
    (SheafOfModules.toSheaf (constantRing X Λ)).map
        ((moduleInverseImageAdjunction f Λ).unit.app M) ≫
      (directImage f).map ((moduleInverseImageUnderlyingIso Λ f).hom.app M) =
    (inverseImageAdjunction f).unit.app
      ((SheafOfModules.toSheaf (constantRing X Λ)).obj M) := by
  have hu := congrArg (SheafOfModules.toSheaf (constantRing X Λ)).map
    (moduleInverseImageTransportIso_unit f Λ M)
  simp only [Functor.map_comp] at hu
  change (SheafOfModules.toSheaf (constantRing X Λ)).map
      ((moduleInverseImageAdjunction f Λ).unit.app M) ≫
    (directImage f).map ((SheafOfModules.toSheaf (constantRing S Λ)).map
      ((moduleInverseImageTransportIso f Λ).hom.app M)) =
    (SheafOfModules.toSheaf (constantRing X Λ)).map
      ((moduleTransportAdjunction f Λ).unit.app M) at hu
  have he : (moduleInverseImageUnderlyingIso Λ f).hom.app M =
      (SheafOfModules.toSheaf (constantRing S Λ)).map
        ((moduleInverseImageTransportIso f Λ).hom.app M) ≫
      (moduleSheafUnderlyingIso S Λ).hom.app
        ((moduleValuedInverseImage f Λ).obj
          ((moduleSheafEquivalence X Λ).inverse.obj M)) ≫
      (moduleValuedInverseImageUnderlyingIso Λ f).hom.app
        ((moduleSheafEquivalence X Λ).inverse.obj M) := by
    unfold moduleInverseImageUnderlyingIso
    rw [moduleSheafInverseUnderlyingIso_eq_refl]
    exact Functor.underlyingComparison_hom_app
      (moduleSheafEquivalence X Λ).inverse (moduleValuedInverseImage f Λ)
      (moduleSheafEquivalence S Λ).functor (SheafOfModules.toSheaf (constantRing S Λ))
      (sheafCompose (Scheme.smallEtaleTopology S)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))
      (sheafCompose (Scheme.smallEtaleTopology X)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))
      (inverseImage f) (moduleInverseImage f Λ) (moduleInverseImageTransportIso f Λ)
      (moduleSheafUnderlyingIso S Λ) (moduleValuedInverseImageUnderlyingIso Λ f) M
  have hh := congrArg (fun z =>
    (SheafOfModules.toSheaf (constantRing X Λ)).map
      ((moduleInverseImageAdjunction f Λ).unit.app M) ≫ (directImage f).map z) he
  let x := (SheafOfModules.toSheaf (constantRing S Λ)).map
    ((moduleInverseImageTransportIso f Λ).hom.app M)
  let y := (moduleSheafUnderlyingIso S Λ).hom.app
    ((moduleValuedInverseImage f Λ).obj
      ((moduleSheafEquivalence X Λ).inverse.obj M))
  let z := (moduleValuedInverseImageUnderlyingIso Λ f).hom.app
    ((moduleSheafEquivalence X Λ).inverse.obj M)
  have hmap := ((directImage f).map_comp x (y ≫ z)).trans
    (congrArg (fun q => (directImage f).map x ≫ q) ((directImage f).map_comp y z))
  have hh' := hh.trans (congrArg (fun q =>
    (SheafOfModules.toSheaf (constantRing X Λ)).map
      ((moduleInverseImageAdjunction f Λ).unit.app M) ≫ q) hmap)
  have ht := moduleTransportAdjunction_unit_underlying Λ f M
  have hv := moduleValuedInverseImageUnderlyingIso_unit f Λ
    ((moduleSheafEquivalence X Λ).inverse.obj M)
  exact hh'.trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ _ ≫ _) hu).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ _) ht).trans hv))))

/-- The inverse of the fixed native pullback comparison has the original
direct-image comparison as its mate. -/
theorem mate_moduleInverseImageUnderlyingIso_inv :
    (mateEquiv (moduleInverseImageAdjunction f Λ) (inverseImageAdjunction f)
      (TwoSquare.mk _ _ _ _ (moduleInverseImageUnderlyingIso Λ f).inv)).natTrans =
        (moduleDirectImageUnderlyingIso f Λ).hom := by
  apply mateEquiv_inv_natTrans_eq_of_unit (moduleInverseImageAdjunction f Λ)
    (inverseImageAdjunction f) (moduleInverseImageUnderlyingIso Λ f)
    (moduleDirectImageUnderlyingIso f Λ).hom
  intro M
  exact (congrArg (fun z => (SheafOfModules.toSheaf (constantRing X Λ)).map
      ((moduleInverseImageAdjunction f Λ).unit.app M) ≫ z)
    (Category.id_comp ((directImage f).map
      ((moduleInverseImageUnderlyingIso Λ f).hom.app M)))).trans
        (moduleInverseImageUnderlyingIso_unit Λ f M)

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
