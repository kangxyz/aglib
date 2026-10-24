/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Power.UnitPower
public import Aglib.AlgebraicGeometry.Modules.Invertible.Power.PullbackNaturality

/-! # Roots of a fixed actual line bundle

A root pair retains its target line bundle and its specified tensor-power
isomorphism. Its pullback uses the original tensor-power comparison. The
definitions and their isomorphisms include level zero; invertibility and
positivity enter only the later lifting theorems.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules.Invertible.Root

universe u

variable {X : Scheme.{u}} (L : LineBundle X) (n : ℕ)

/-- An actual nth root of the fixed target line bundle. -/
structure Pair where
  /-- The actual root line bundle. -/
  bundle : LineBundle X
  /-- The prescribed isomorphism to the fixed target. -/
  powerIso : (tensorPowerLineBundle X bundle n).val ≅ L.val

variable {L n}

/-- An isomorphism of root pairs preserves their specified power maps. -/
structure Iso (P Q : Pair L n) where
  /-- The original isomorphism of the root bundles. -/
  bundleIso : P.bundle.val ≅ Q.bundle.val
  /-- The exact tensor-power compatibility equation. -/
  comm : (TrivializedPower.powerIso X bundleIso n).hom ≫ Q.powerIso.hom = P.powerIso.hom

/-- The actual root pair gives the corresponding equality of Picard classes. -/
theorem Pair.nsmul_class (P : Pair L n) :
    n • classOf X P.bundle = classOf X L := by
  rw [← classOf_tensorPower]
  exact Quotient.sound ⟨P.powerIso⟩

/-- The identity root-pair isomorphism. -/
def Iso.refl (P : Pair L n) : Iso P P where
  bundleIso := CategoryTheory.Iso.refl _
  comm := by rw [UnitPower.powerIso_refl]; exact Category.id_comp _

/-- Composition retains the original power equation. -/
def Iso.trans {P Q T : Pair L n} (a : Iso P Q) (b : Iso Q T) : Iso P T where
  bundleIso := a.bundleIso ≪≫ b.bundleIso
  comm := by
    rw [UnitPower.powerIso_trans, CategoryTheory.Iso.trans_hom, Category.assoc,
      b.comm, a.comm]

/-- Inversion retains the original power equation. -/
def Iso.symm {P Q : Pair L n} (a : Iso P Q) : Iso Q P where
  bundleIso := a.bundleIso.symm
  comm := by
    apply (cancel_epi (TrivializedPower.powerIso X a.bundleIso n).hom).mp
    rw [← Category.assoc, UnitPower.powerIso_symm, CategoryTheory.Iso.symm_hom,
      CategoryTheory.Iso.hom_inv_id, Category.id_comp, a.comm]

/-- Transport only the specified target, along an actual target isomorphism. -/
def Pair.mapTarget {L' : LineBundle X} (P : Pair L n) (e : L.val ≅ L'.val) : Pair L' n where
  bundle := P.bundle
  powerIso := P.powerIso ≪≫ e

/-- Target transport preserves actual root-pair isomorphisms. -/
def Iso.mapTarget {L' : LineBundle X} {P Q : Pair L n}
    (a : Iso P Q) (e : L.val ≅ L'.val) : Iso (P.mapTarget e) (Q.mapTarget e) where
  bundleIso := a.bundleIso
  comm := by
    change (TrivializedPower.powerIso X a.bundleIso n).hom ≫
      (Q.powerIso.hom ≫ e.hom) = P.powerIso.hom ≫ e.hom
    rw [← Category.assoc, a.comm]

variable {Y : Scheme.{u}} (f : X ⟶ Y) {L : LineBundle Y}

/-- Pull back the fixed target and its root through the original tensor-power comparison. -/
def Pair.pullback (P : Pair L n) : Pair (pullbackLineBundle f L) n where
  bundle := pullbackLineBundle f P.bundle
  powerIso := (PowerPullback.pullbackPowerIso f P.bundle n).symm ≪≫
    (Scheme.Modules.pullback f).mapIso P.powerIso

/-- Original root-pair isomorphisms pull back with the native power comparison. -/
def Iso.pullback {P Q : Pair L n} (a : Iso P Q) : Iso (P.pullback f) (Q.pullback f) where
  bundleIso := (Scheme.Modules.pullback f).mapIso a.bundleIso
  comm := by
    change (TrivializedPower.powerIso X
        ((Scheme.Modules.pullback f).mapIso a.bundleIso) n).hom ≫
      ((PowerPullback.pullbackPowerIso f Q.bundle n).inv ≫
        (Scheme.Modules.pullback f).map Q.powerIso.hom) =
      (PowerPullback.pullbackPowerIso f P.bundle n).inv ≫
        (Scheme.Modules.pullback f).map P.powerIso.hom
    rw [← Category.assoc, PowerPullbackNaturality.pullbackPowerIso_inv_naturality,
      Category.assoc, ← Functor.map_comp, a.comm]

end AlgebraicGeometry.Scheme.Modules.Invertible.Root
