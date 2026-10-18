/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.AffineDeterminant
public import Aglib.AlgebraicGeometry.Modules.ExteriorPower.OpenRestriction
public import Aglib.AlgebraicGeometry.Modules.Restriction.Unit
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.ScalarAdjunction
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Hom

/-!
# The original ambient coefficient bridge on an affine open square

The mixed pullback/restriction square retains the original unit maps.
Original affine sections become the same unit tensors under pullback.
These section and wedge computations compare the actual framed ambient
coefficient maps when both affine rings change.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules.Differentials
open scoped TensorProduct ChangeOfRings

universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The original mixed open square preserves the original structure-module units. -/
@[reassoc] theorem canonicalOpenPullbackSquare_unit
    {W X V Y : Scheme.{u}} (p : W ⟶ X) (q : W ⟶ V) (f : X ⟶ Y) (j : V ⟶ Y)
    [IsOpenImmersion p] [IsOpenImmersion j] (h : p ≫ f = q ≫ j) :
    (pullbackOpenSquare p q f j h).hom.app (SheafOfModules.unit Y.ringCatSheaf) ≫
        (pullback q).map (restrictUnitIso j).hom ≫ (pullbackUnitIso q).hom =
      (restrictFunctor p).map (pullbackUnitIso f).hom ≫ (restrictUnitIso p).hom := by
  simp only [pullbackOpenSquare, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom, Category.assoc]
  rw [← Functor.map_comp_assoc, restrictFunctorIsoPullback_inv_unit]
  change (restrictFunctorIsoPullback p).hom.app ((pullback f).obj
      (SheafOfModules.unit Y.ringCatSheaf)) ≫
    (pullbackComp p f).hom.app (SheafOfModules.unit Y.ringCatSheaf) ≫
    (pullbackCongr h).hom.app (SheafOfModules.unit Y.ringCatSheaf) ≫
    (pullbackComp q j).inv.app (SheafOfModules.unit Y.ringCatSheaf) ≫
    (pullback q).map (pullbackUnitIso j).hom ≫ (pullbackUnitIso q).hom = _
  rw [← pullbackUnitIso_comp q j, Iso.inv_hom_id_app_assoc,
    pullbackUnitIso_congr h, pullbackUnitIso_comp p f]
  have hn := (restrictFunctorIsoPullback p).hom.naturality (pullbackUnitIso f).hom
  change (restrictFunctor p).map (pullbackUnitIso f).hom ≫
      (restrictFunctorIsoPullback p).hom.app (SheafOfModules.unit X.ringCatSheaf) =
    (restrictFunctorIsoPullback p).hom.app ((pullback f).obj
      (SheafOfModules.unit Y.ringCatSheaf)) ≫ (pullback p).map (pullbackUnitIso f).hom at hn
  rw [← Category.assoc, ← hn, Category.assoc]
  exact congrArg (fun k => (restrictFunctor p).map (pullbackUnitIso f).hom ≫ k)
    (restrictFunctorIsoPullback_hom_unit p)

/-- The original affine vector as a morphism from the actual structure module. -/
def canonicalAffineUnitSection {A : CommRingCat.{u}} (E : ModuleCat.{u} A) (x : E) :
    SheafOfModules.unit (Spec A).ringCatSheaf ⟶ tilde E :=
  (unitHomGlobalSectionsEquiv (Spec A) (tilde E)).symm (tilde.toOpen E ⊤ x)

/-- The section morphism has the original associated-sheaf value on every open. -/
theorem canonicalAffineUnitSection_app {A : CommRingCat.{u}} (E : ModuleCat.{u} A)
    (x : E) (U : (Spec A).Opens) :
    (canonicalAffineUnitSection E x).val.app (op U) (1 : Γ(Spec A, U)) =
      tilde.toOpen E U x := by
  rw [show (canonicalAffineUnitSection E x).val.app (op U) (1 : Γ(Spec A, U)) =
      (1 : Γ(Spec A, U)) • (tilde E).presheaf.map U.leTop.op (tilde.toOpen E ⊤ x) from
    unitHomGlobalSectionsEquiv_symm_app (Spec A) (tilde E) (tilde.toOpen E ⊤ x) U 1]
  rw [one_smul]
  exact ConcreteCategory.congr_hom (tilde.toOpen_res E ⊤ U U.leTop) x

/-- The native affine pullback comparison sends the original section to the
original unit tensor, with the actual pullback unit retained. -/
theorem canonicalAffineUnitSection_pullback {A B : CommRingCat.{u}} (σ : A ⟶ B)
    (E : ModuleCat.{u} A) (x : E) :
    (pullbackUnitIso (Spec.map σ)).inv ≫
        (pullback (Spec.map σ)).map (canonicalAffineUnitSection E x) ≫
        (tildePullbackIso σ).hom.app E =
      canonicalAffineUnitSection ((ModuleCat.extendScalars σ.hom).obj E)
        ((1 : B) ⊗ₜ[A,σ.hom] x) := by
  apply (cancel_epi (pullbackUnitIso (Spec.map σ)).hom).mp
  rw [Iso.hom_inv_id_assoc]
  apply ((pullbackPushforwardAdjunction (Spec.map σ)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    pullbackUnitIso_homEquiv]
  apply (unitHomGlobalSectionsEquiv (Spec A)
    ((pushforward (Spec.map σ)).obj
      (tilde ((ModuleCat.extendScalars σ.hom).obj E)))).injective
  have hu := ConcreteCategory.congr_hom (tildePullbackIso_globalSections_unit σ E) x
  rw [Adjunction.homEquiv_unit]
  change ((tildePullbackIso σ).hom.app E).val.app (op ⊤)
      (((pullbackPushforwardAdjunction (Spec.map σ)).unit.app (tilde E)).val.app (op ⊤)
        ((canonicalAffineUnitSection E x).val.app (op ⊤) (1 : Γ(Spec A, ⊤)))) =
    (canonicalAffineUnitSection ((ModuleCat.extendScalars σ.hom).obj E)
      ((1 : B) ⊗ₜ[A,σ.hom] x)).val.app (op ⊤)
        ((Spec.map σ).appTop.hom (1 : Γ(Spec A, ⊤)))
  rw [canonicalAffineUnitSection_app E x ⊤,
    show (Spec.map σ).appTop.hom (1 : Γ(Spec A, ⊤)) = (1 : Γ(Spec B, ⊤)) from
      (Spec.map σ).appTop.hom.map_one, canonicalAffineUnitSection_app]
  exact hu

end AlgebraicGeometry.Scheme.Modules
