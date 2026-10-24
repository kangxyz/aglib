/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Root.Basic

/-! # Fixed-target root transport and original pullback coherence -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules.Invertible.Root

universe u

variable {X : Scheme.{u}} {L : LineBundle X} {n : ℕ}

/-- Transport the actual root bundle through a specified original bundle isomorphism. -/
def Pair.mapBundle (P : Pair L n) (M : LineBundle X) (e : M.val ≅ P.bundle.val) : Pair L n where
  bundle := M
  powerIso := TrivializedPower.powerIso X e n ≪≫ P.powerIso

/-- Root-bundle transport retains its specified original isomorphism. -/
def mapBundleIso (P : Pair L n) (M : LineBundle X) (e : M.val ≅ P.bundle.val) :
    Iso (P.mapBundle M e) P where
  bundleIso := e
  comm := rfl

/-- Transport to an actual target and back retains the root pair. -/
def mapTargetCancelIso {L' : LineBundle X} (P : Pair L n) (e : L.val ≅ L'.val) :
    Iso ((P.mapTarget e).mapTarget e.symm) P where
  bundleIso := CategoryTheory.Iso.refl _
  comm := by
    change (TrivializedPower.powerIso X (CategoryTheory.Iso.refl P.bundle.val) n).hom ≫
        P.powerIso.hom = (P.powerIso.hom ≫ e.hom) ≫ e.inv
    rw [UnitPower.powerIso_refl]
    simp only [CategoryTheory.Iso.refl_hom, Category.id_comp, Category.assoc,
      CategoryTheory.Iso.hom_inv_id, Category.comp_id]

/-- The original identity pullback, including transport of the fixed target. -/
def pullbackIdIso (P : Pair L n) :
    Iso ((P.pullback (𝟙 X)).mapTarget ((Scheme.Modules.pullbackId X).app L.val)) P where
  bundleIso := (Scheme.Modules.pullbackId X).app P.bundle.val
  comm := by
    change (TrivializedPower.powerIso X ((Scheme.Modules.pullbackId X).app P.bundle.val) n).hom ≫
        P.powerIso.hom =
      (PowerPullback.pullbackPowerIso (𝟙 X) P.bundle n).inv ≫
        (Scheme.Modules.pullback (𝟙 X)).map P.powerIso.hom ≫
          (Scheme.Modules.pullbackId X).hom.app L.val
    apply (PowerPullback.pullbackPowerIso (𝟙 X) P.bundle n).eq_inv_comp.mpr
    rw [← Category.assoc, PowerPullbackNaturality.pullbackPowerIso_id]
    exact ((Scheme.Modules.pullbackId X).hom.naturality P.powerIso.hom).symm

/-- The native composite pullback comparison is an actual root-pair isomorphism,
with the original target comparison kept explicitly. -/
def pullbackCompIso {Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {L : LineBundle Z} (P : Pair L n) :
    Iso (P.pullback (f ≫ g))
      (((P.pullback g).pullback f).mapTarget ((Scheme.Modules.pullbackComp f g).app L.val)) where
  bundleIso := ((Scheme.Modules.pullbackComp f g).app P.bundle.val).symm
  comm := by
    change (TrivializedPower.powerIso X
        ((Scheme.Modules.pullbackComp f g).app P.bundle.val).symm n).hom ≫
      ((PowerPullback.pullbackPowerIso f (pullbackLineBundle g P.bundle) n).inv ≫
        (Scheme.Modules.pullback f).map
          ((PowerPullback.pullbackPowerIso g P.bundle n).inv ≫
            (Scheme.Modules.pullback g).map P.powerIso.hom) ≫
        (Scheme.Modules.pullbackComp f g).hom.app L.val) =
      (PowerPullback.pullbackPowerIso (f ≫ g) P.bundle n).inv ≫
        (Scheme.Modules.pullback (f ≫ g)).map P.powerIso.hom
    apply (PowerPullback.pullbackPowerIso (f ≫ g) P.bundle n).eq_inv_comp.mpr
    rw [← Category.assoc, ← PowerPullbackNaturality.pullbackPowerIso_comp]
    simp only [Category.assoc, CategoryTheory.Iso.hom_inv_id_assoc, Functor.map_comp]
    have hcancel := CategoryTheory.Iso.hom_inv_id_assoc
      ((Scheme.Modules.pullback f).mapIso (PowerPullback.pullbackPowerIso g P.bundle n))
      ((Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map P.powerIso.hom) ≫
        (Scheme.Modules.pullbackComp f g).hom.app L.val)
    erw [hcancel]
    erw [← (Scheme.Modules.pullbackComp f g).inv.naturality_assoc P.powerIso.hom]
    let z := (Scheme.Modules.pullback (f ≫ g)).map P.powerIso.hom
    change z ≫ (((Scheme.Modules.pullbackComp f g).app L.val).inv ≫
      ((Scheme.Modules.pullbackComp f g).app L.val).hom) = z
    exact (congrArg (fun k => z ≫ k)
      ((Scheme.Modules.pullbackComp f g).app L.val).inv_hom_id).trans (Category.comp_id z)

end AlgebraicGeometry.Scheme.Modules.Invertible.Root
