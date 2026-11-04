/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.WeilPairing.Polarization
public import Aglib.AlgebraicGeometry.Group.CartierDuality.CharacterRoots

/-! Evaluation of the original terminal Weil character at a field point. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open Scheme.OverField Scheme.Group Scheme.Group.BaseChange
open Scheme.Group.MultiplicativeGroup
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Cartier

variable {k : Type u} [Field k] (G : Grp (FScheme k))
  [IsFinite G.X.hom] [IsCommMonObj G.X]

set_option hygiene false in
local notation "T₀" => (𝟙_ (FScheme k))

omit [IsFinite G.X.hom] [IsCommMonObj G.X] in
/-- On the terminal test, the original inverse identity comparison gives the original lift. -/
theorem originalTerminalGroupPoint_left (x : (T₀) ⟶ G.X) :
    (x ≫ (groupSchemeBaseChangeId.inv.app G).hom.hom).left = (lift x (𝟙 (T₀))).left := by
  apply pullback.hom_ext
  · simp only [Over.comp_left, Over.lift_left, Category.assoc,
      groupSchemeBaseChangeId_inv_app_left, pullback.lift_fst, Category.comp_id]
    erw [pullback.lift_fst]
  · simp only [Over.comp_left, Over.lift_left, Category.assoc,
      groupSchemeBaseChangeId_inv_app_left, pullback.lift_snd, Over.w, Over.id_left]
    erw [pullback.lift_snd]
    rfl

/-- The terminal character evaluated on the original point gives the original root evaluation. -/
theorem originalTerminalCharacterSection
    (n : ℕ) (hkill : (𝟙 G.X) ^ n = 1)
    (x : (T₀) ⟶ G.X) (p : (T₀) ⟶ (CartierDuality.dualGroup G).X) :
    let χ := _root_.AlgebraicGeometry.Scheme.Group.CartierDuality.characterRoots G (T₀) p n hkill
    x ≫ (groupSchemeBaseChangeId.inv.app G).hom.hom ≫ χ.hom.hom =
      lift x p ≫ CartierDuality.evaluationRoots G n hkill := by
  intro χ
  let z := x ≫ (groupSchemeBaseChangeId.inv.app G).hom.hom
  let E := rootsHomEquiv (Base k) n (T₀)
  apply E.injective
  apply Subtype.ext
  rw [← Category.assoc]
  have h₁ := congrArg Subtype.val
    ((rootsRepresentable (Base k) n).homEquiv_comp z χ.hom.hom)
  have h₂ :=
    CartierDuality.evaluationRoots_units_eq_characterRoots_on_section G (T₀) p n hkill x
  change (E (z ≫ χ.hom.hom)).val = Units.map z.left.appTop.hom.toMonoidHom
    (rootsHomEquiv (Base k) n _ χ.hom.hom).val at h₁
  dsimp only [z] at h₁
  rw [originalTerminalGroupPoint_left G x] at h₁
  exact h₁.trans h₂.symm

end Cartier

section Principal

variable {k : Type u} [Field k] (A : Grp (FScheme k))
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf A.X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  [IsHProjective A.X.hom] [GeometricallyIntegral A.X.hom] [Smooth A.X.hom]
  [IsSeparated P.obj.hom] [IsCommMonObj A.X]
  (e : A ≅ Grp.mk (picardIdentityComponent A.X.hom P R))

set_option hygiene false in
local notation "T₀" => (𝟙_ (FScheme k))

/-- Evaluating the original terminal character at the original first point gives the
original Weil pairing with the specified principal second point. -/
theorem originalTerminalPrincipalCharacterSection (n : ℕ) (hn : 0 < n)
    (x y : (T₀) ⟶ (MultiplicationKernel.kernelGroup A n).X) :
    let G := MultiplicationKernel.kernelGroup A n
    letI : IsFinite G.X.hom := Multiplication.kernelGroup_isFinite_of_pos A n hn
    letI : IsCommMonObj G.X :=
      Kernel.isCommMonObj_group (MultiplicationKernel.multiplicationHom A n)
    let t := y ≫ (principalIsoOnMultiplicationKernel A P R e n).hom.hom.hom
    let p := t ≫ (multiplicationKernelCartierHom A P R n hn).hom.hom
    let χ := _root_.AlgebraicGeometry.Scheme.Group.CartierDuality.characterRoots G (T₀) p n
      (Kernel.multiplication_kernel_pow_eq_one A n)
    x ≫ (groupSchemeBaseChangeId.inv.app G).hom.hom ≫ χ.hom.hom =
      lift x y ≫ weilPairingMorphismOfPrincipalIso A P R e n hn := by
  intro G t p χ
  let : IsFinite G.X.hom := Multiplication.kernelGroup_isFinite_of_pos A n hn
  let : IsCommMonObj G.X :=
    Kernel.isCommMonObj_group (MultiplicationKernel.multiplicationHom A n)
  let hkill := Kernel.multiplication_kernel_pow_eq_one A n
  have h₁ := originalTerminalCharacterSection G n hkill x p
  have h₂ : lift x p ≫ CartierDuality.evaluationRoots G n hkill =
      lift x y ≫ weilPairingMorphismOfPrincipalIso A P R e n hn := by
    let : Mono (rootsInclusion (Base k) n) :=
      inferInstanceAs (Mono (equalizer.ι (powerMap (Base k) n) (oneMap (Base k))))
    apply (cancel_mono (rootsInclusion (Base k) n)).mp
    rw [CartierDuality.comp_evaluationRoots_comp_inclusion,
      Category.assoc (lift x y), weilPairingMorphismOfPrincipalIso_comp_inclusion]
    unfold weilPairingEvaluationOfPrincipalIso
    rw [weilPairingEvaluation_eq]
    have ht : lift x y ≫
        (𝟙 G.X ⊗ₘ (principalIsoOnMultiplicationKernel A P R e n).hom.hom.hom) =
        lift x t := by
      rw [lift_map]
      exact congrArg (fun z => lift z t) (Category.comp_id x)
    have hp : lift x t ≫
        (𝟙 G.X ⊗ₘ (multiplicationKernelCartierHom A P R n hn).hom.hom) = lift x p := by
      rw [lift_map]
      exact congrArg (fun z => lift z p) (Category.comp_id x)
    rw [← Category.assoc (lift x y), ht, ← Category.assoc (lift x t), hp]
  exact h₁.trans h₂

end Principal

end AlgebraicGeometry.Scheme.RelativePicard
