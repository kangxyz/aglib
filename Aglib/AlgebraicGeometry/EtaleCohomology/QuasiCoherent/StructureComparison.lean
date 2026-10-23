/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.SectionScalars
public import Aglib.AlgebraicGeometry.EtaleCohomology.StructureSheaf.Basic

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.AdditiveTransport

/-! # Comparison with the original additive structure coefficient

The target is the published structure coefficient, with its original global
section restrictions. No second structure sheaf is introduced.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

attribute [local instance] isQuasicoherent_unit

/-- The native pullback of a unit-module section is the original ring-section map. -/
theorem nativeUnitSectionPullback {U V : Scheme.{u}} (f : U ⟶ V) (r : Γ(V, ⊤)) :
    Scheme.Modules.Hom.app (pullbackUnitIso f).hom ⊤
        (nativeSectionPullback f (SheafOfModules.unit V.ringCatSheaf) r) =
      f.appTop.hom r := by
  rw [nativeSectionPullback_eq_unit]
  have h := pullbackUnitIso_homEquiv f
  change (pullbackPushforwardAdjunction f).unit.app
      (SheafOfModules.unit V.ringCatSheaf) ≫
    (pushforward f).map (pullbackUnitIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom at h
  exact congrArg (fun k : SheafOfModules.unit V.ringCatSheaf ⟶
      (pushforward f).obj (SheafOfModules.unit U.ringCatSheaf) =>
    Scheme.Modules.Hom.app k ⊤ r) h

/-- The native unit comparison commutes with every original over-site restriction. -/
theorem unitSections_naturality (X : Scheme.{u}) {T U : Over X} (f : U ⟶ T)
    (s : Γ((pullback T.hom).obj (SheafOfModules.unit X.ringCatSheaf), ⊤)) :
    Scheme.Modules.Hom.app (pullbackUnitIso U.hom).hom ⊤
      ((sectionsPresheaf X (SheafOfModules.unit X.ringCatSheaf)).map f.op s) =
    f.left.appTop.hom (Scheme.Modules.Hom.app (pullbackUnitIso T.hom).hom ⊤ s) := by
  rw [sectionsPresheaf_map_eq, ← nativeSectionPullback_eq_unit]
  have h : ((pullbackComp f.left T.hom).hom.app (SheafOfModules.unit X.ringCatSheaf) ≫
      (pullbackCongr (Over.w f)).hom.app (SheafOfModules.unit X.ringCatSheaf)) ≫
      (pullbackUnitIso U.hom).hom =
    (pullback f.left).map (pullbackUnitIso T.hom).hom ≫ (pullbackUnitIso f.left).hom := by
    rw [Category.assoc, pullbackUnitIso_congr, pullbackUnitIso_comp]
  have he := congrArg (fun k => Scheme.Modules.Hom.app k ⊤
    (nativeSectionPullback f.left
      ((pullback T.hom).obj (SheafOfModules.unit X.ringCatSheaf)) s)) h
  change _ = Scheme.Modules.Hom.app (pullbackUnitIso f.left).hom ⊤
    (Scheme.Modules.Hom.app ((pullback f.left).map (pullbackUnitIso T.hom).hom) ⊤
      (nativeSectionPullback f.left
        ((pullback T.hom).obj (SheafOfModules.unit X.ringCatSheaf)) s)) at he
  rw [nativeSectionPullback_naturality, nativeUnitSectionPullback] at he
  exact he

/-- On each test scheme the comparison is evaluation of the actual pullback-unit isomorphism. -/
def unitSectionsAddEquiv (X : Scheme.{u}) (T : Over X) :
    Γ((pullback T.hom).obj (SheafOfModules.unit X.ringCatSheaf), ⊤) ≃+ Γ(T.left, ⊤) :=
  ((SheafOfModules.evaluation T.left.ringCatSheaf (op ⊤)).mapIso
    (pullbackUnitIso T.hom)).toLinearEquiv.toAddEquiv

/-- The genuine quasi-coherent unit coefficient is the published additive structure sheaf. -/
def additiveUnitStructureIso (X : Scheme.{u}) :
    additiveCoefficient X (SheafOfModules.unit X.ringCatSheaf) ≅
      additiveStructureSheaf X :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (liftTransportNativeIso (homPresheaf X (SheafOfModules.unit X.ringCatSheaf))
      (fun T => AddCommGrpCat.of Γ((pullback T.hom).obj (SheafOfModules.unit X.ringCatSheaf), ⊤))
      (sectionsEquiv X (SheafOfModules.unit X.ringCatSheaf))
      (fun f => sectionsAddHom X (SheafOfModules.unit X.ringCatSheaf) f)
      (fun f s => sectionsAddHom_apply X (SheafOfModules.unit X.ringCatSheaf) f s)
      (Scheme.Etale.forget X)
      (structurePresheaf X ⋙ forget₂ CommRingCat.{u} RingCat.{u} ⋙
        forget₂ RingCat.{u} AddCommGrpCat.{u})
      (fun T => unitSectionsAddEquiv X ((Scheme.Etale.forget X).obj T))
      (fun f s => unitSections_naturality X ((Scheme.Etale.forget X).map f) s))

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
