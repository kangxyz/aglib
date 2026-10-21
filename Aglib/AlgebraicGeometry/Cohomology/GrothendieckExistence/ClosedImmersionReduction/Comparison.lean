/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.ClosedImmersionReduction.Pushforward

/-! # Completion commutes with actual closed pushforward -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] {X Y : Scheme.{u}}
  (i : X ⟶ Y) [IsClosedImmersion i] (f : Y ⟶ Spec (CommRingCat.of A))
  (I : Ideal A) (F : X.Modules) [F.IsQuasicoherent]

local notation "KX" => idealThickeningIdealSheaf (i ≫ f) I
local notation "KY" => idealThickeningIdealSheaf f I

/-- Native completion transitions commute with the closed-pushforward comparison. -/
@[reassoc]
theorem closedPushforwardNativeQuotientIso_transition {n m : ℕ} (h : n ≤ m) :
    (pushforward i).map (idealSheafQuotientMap X (KX ^ m)
      (idealSheaf_pow_le X KX h) F) ≫
      (closedPushforwardNativeQuotientIso i f I F n).hom =
    (closedPushforwardNativeQuotientIso i f I F m).hom ≫
      idealSheafQuotientMap Y (KY ^ m) (idealSheaf_pow_le Y KY h)
        ((pushforward i).obj F) := by
  apply (cancel_epi ((pushforward i).map
    ((idealSheafQuotientUnit X (KX ^ m)).app F))).mp
  rw [← Functor.map_comp_assoc, idealSheafQuotientUnit_map,
    closedPushforwardNativeQuotientIso_unit i f I F n,
    ← Category.assoc, closedPushforwardNativeQuotientIso_unit i f I F m,
    idealSheafQuotientUnit_map]

/-- The native completion diagram comparison, preserving the original tower. -/
def closedPushforwardCompletionDiagramIso :
    idealSheafQuotientTower X KX F ⋙ pushforward i ≅
      idealSheafQuotientTower Y KY ((pushforward i).obj F) :=
  NatIso.ofComponents (fun n => closedPushforwardNativeQuotientIso i f I F n.unop)
    (by
      intro m n g
      exact closedPushforwardNativeQuotientIso_transition i f I F (leOfHom g.unop))

end AlgebraicGeometry.Scheme.Cohomology
