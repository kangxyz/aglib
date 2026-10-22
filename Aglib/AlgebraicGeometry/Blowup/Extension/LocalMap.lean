/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.OpenExtension
public import Aglib.AlgebraicGeometry.Blowup.FlatBaseChange
public import Aglib.AlgebraicGeometry.Morphisms.Restrict.Agreement

/-!
# Transporting maps to a local blowup

A map to the blowup of an extended centre induces a map to the original local
blowup on the literal pullback of the base open. The native flat-base-change
comparison supplies this map. Compatibility with a prescribed map on another
open is retained on the literal intersection pullback, without separatedness,
Noetherianity, or a unit-centre hypothesis.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Blowup.LocalMap

variable {X V T : Scheme.{u}} (q : V ⟶ X) [IsOpenImmersion q] [QuasiCompact q]
    (J : V.IdealSheafData) (BL : BlowupDatum J) (BG : BlowupDatum (J.map q))
    (t : T ⟶ X) (a : T ⟶ BG.Y) (ha : a ≫ BG.map = t)

/-- The original local blowup is the literal pullback of any universal blowup
representative of its extended centre. -/
theorem isPullback : IsPullback
    (BaseChange.map q (J.comap_map_of_isOpenImmersion q) BG BL) BL.map BG.map q :=
  BaseChange.isPullback_of_flat q inferInstance (J.comap_map_of_isOpenImmersion q) BG BL

/-- The induced map to the original local blowup, using the inverse of the
native cartesian comparison rather than an independently supplied lift. -/
def lift : pullback t q ⟶ BL.Y :=
  pullback.lift (pullback.fst t q ≫ a) (pullback.snd t q)
    (by rw [Category.assoc, ha, pullback.condition]) ≫
      (isPullback q J BL BG).isoPullback.inv

/-- The induced local map has the original second pullback projection as its
structural map to the base open. -/
@[reassoc (attr := simp)]
theorem lift_map : lift q J BL BG t a ha ≫ BL.map = pullback.snd t q := by
  rw [lift, Category.assoc, (isPullback q J BL BG).isoPullback_inv_snd,
    pullback.lift_snd]

/-- Agreement on a protected open survives transport to the original local
blowup, on the actual pullback intersection with that open. -/
theorem lift_agrees {P : Scheme.{u}} (U : X.Opens) (g : U.toScheme ⟶ P)
    (F : BL.Y ⟶ P)
    (h : (BL.map ⁻¹ᵁ (q ⁻¹ᵁ U)).ι ≫ F =
      (BL.map ∣_ (q ⁻¹ᵁ U)) ≫ (q ∣_ U) ≫ g) :
    pullback.fst (pullback.fst t q) (t ⁻¹ᵁ U).ι ≫ lift q J BL BG t a ha ≫ F =
      pullback.snd (pullback.fst t q) (t ⁻¹ᵁ U).ι ≫ (t ∣_ U) ≫ g := by
  exact Hom.agreement_on_pullback_restriction q t BL.map
    (lift q J BL BG t a ha) (lift_map q J BL BG t a ha) U g F h

end AlgebraicGeometry.Scheme.Blowup.LocalMap
