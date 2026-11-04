/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.WeilPairing.FrameClass
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedKernel.CoverTerminalPullback.RootCharacter

/-! The positive original Weil character on the direct marked kernel. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory
open Scheme.Group Scheme.Group.BaseChange Scheme.Group.MultiplicativeGroup
open Scheme.OverField Scheme.EtaleCohomology.RepresentedKernel
open scoped CategoryTheory.MonObj

universe u

attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Scheme.RelativePicard

open KernelFramePushout

variable {k : Type u} [Field k] (A : Grp (FScheme k))
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf A.X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  [IsHProjective A.X.hom] [GeometricallyIntegral A.X.hom] [Smooth A.X.hom]
  [IsSeparated P.obj.hom] [IsCommMonObj A.X]
  (n : ℕ) (hn : 0 < n) (t : (𝟙_ (FScheme k)) ⟶ (dualMultiplicationKernel A P R n).X)

set_option hygiene false in
local notation "T₀" => (𝟙_ (FScheme k))
set_option hygiene false in
local notation "qₙ" => MultiplicationKernel.multiplicationHom A n
set_option hygiene false in
local notation "K" => Kernel.group (qₙ)
set_option hygiene false in
local notation "A₀" => baseChangedGroup (T₀).hom A
set_option hygiene false in
local notation "K₀" => baseChangedGroup (T₀).hom (K)

variable {Z : Scheme.{u}}

/-- The positive fixed-slot Weil character on the original multiplication kernel over the base. -/
def multiplicationTerminalRootCharacter (d : Z ⟶ Base k) :
    baseChangedGroup d (K) ⟶ rootsGroupScheme Z n := by
  letI : IsFinite (K).X.hom := Multiplication.kernelGroup_isFinite_of_pos A n hn
  letI : IsCommMonObj (K).X := Kernel.isCommMonObj_group (qₙ)
  exact terminalRootCharacterBaseChange d (K) n
    (_root_.AlgebraicGeometry.Scheme.Group.CartierDuality.characterRoots (K) (T₀)
      (t ≫ (multiplicationKernelCartierHom A P R n hn).hom.hom) n
      (Kernel.multiplication_kernel_pow_eq_one A n))

/-- The original terminal family character, pulled back to the curve, is the direct marked
kernel character after the same comparisons used for the graph boundary. -/
theorem multiplicationTerminalRootCharacter_pullback
    (f : Z ⟶ (A₀).X.left) (d : Z ⟶ Base k) (h : f ≫ (A₀).X.hom = d) :
    (groupSchemeBaseChangeComp f (A₀).X.hom).inv.app (K₀) ≫
        (terminalGroupComparison h).hom.app (K) ≫
        multiplicationTerminalRootCharacter A P R n hn t d =
      (Over.pullback f).mapGrp.map (multiplicationFamilyRootCharacter A P R n hn t) ≫
        (MultiplicativeBaseChange.rootsBaseChangeIso f n).hom := by
  let : IsFinite (K).X.hom := Multiplication.kernelGroup_isFinite_of_pos A n hn
  let : IsCommMonObj (K).X := Kernel.isCommMonObj_group (qₙ)
  let χ := _root_.AlgebraicGeometry.Scheme.Group.CartierDuality.characterRoots (K) (T₀)
    (t ≫ (multiplicationKernelCartierHom A P R n hn).hom.hom) n
    (Kernel.multiplication_kernel_pow_eq_one A n)
  exact terminalRootCharacterBaseChange_comp f (A₀).X.hom d h (K) n χ

end AlgebraicGeometry.Scheme.RelativePicard
