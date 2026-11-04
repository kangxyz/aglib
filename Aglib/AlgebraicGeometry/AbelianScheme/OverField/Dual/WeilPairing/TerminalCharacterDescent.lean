/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.WeilPairing.RootCharacters
public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.WeilPairing.FrameClass.DirectRootCharacter
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RootCharacterDescent
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedMultiplicationBaseChange

/-! The positive Weil characters and the original represented coefficient maps. -/

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.Scheme.OverField AlgebraicGeometry.Scheme.Group
open AlgebraicGeometry.Scheme.Group.BaseChange
open AlgebraicGeometry.Scheme.EtaleCohomology
open GroupCohomology.Kummer.Coefficients

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.RelativePicard

universe u

attribute [local instance] Over.cartesianMonoidalCategory hasSheafifyLarge
  groupSchemeBaseChange_isCommMonObj

variable {k : Type u} [Field k] [IsSepClosed k] (A : Grp (FScheme k))
  (P : LocallyNoetherianOver (Base k)) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Base k)).op ⋙ (fppfPicardSheaf A.X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  [IsHProjective A.X.hom] [GeometricallyIntegral A.X.hom] [Smooth A.X.hom]
  [IsSeparated P.obj.hom] [IsCommMonObj A.X]
  (e : A ≅ Grp.mk (picardIdentityComponent A.X.hom P R))
  (n : ℕ) (hn : 0 < n)

set_option hygiene false in
local notation "K" => MultiplicationKernel.kernelGroup A n
set_option hygiene false in
local notation "T₀" => 𝟙_ (FScheme k)

local instance : IsCommMonObj (K).X :=
  Kernel.isCommMonObj_group (MultiplicationKernel.multiplicationHom A n)

variable [Etale (K).X.hom] {X : Scheme.{u}}
  [ConnectedSpace X] [CompactSpace X] [QuasiSeparatedSpace X] (p : X ⟶ Base k)
  (hi : IsUnit (n : Γ(Base k, ⊤)))

/-- Every coefficient map on the original kernel after pullback comes from the
positive Weil character of one original second kernel point. -/
def multiplicationTerminalRootCharacterSheafEquiv :
    ((T₀) ⟶ (K).X) ≃
      (representedSheaf (Group.BaseChange.baseChangedGroup p (K)) ⟶ mu X n) :=
  letI : IsFinite (K).X.hom := Multiplication.kernelGroup_isFinite_of_pos A n hn
  let i : Group.BaseChange.baseChangedGroup (𝟙 (Base k)) (K) ≅ (K) :=
    groupSchemeBaseChangeId.app (K)
  let e₀ := multiplicationKernelRootCharacterEquivOfPrincipalIso A P R e n hn (T₀)
  let e₁ := i.homCongr (Iso.refl (MultiplicativeGroup.rootsGroupScheme (Base k) n))
  let e₂ := Kummer.rootsCharacterPullbackEquiv k p (K) n hn hi
    (Kernel.multiplication_kernel_pow_eq_one A n)
  e₀.trans (e₁.trans e₂)

/-- The forward map is exactly the represented positive direct character. -/
theorem multiplicationTerminalRootCharacterSheafEquiv_apply (y : (T₀) ⟶ (K).X) :
    multiplicationTerminalRootCharacterSheafEquiv A P R e n hn p hi y =
      representedSheafMap (multiplicationTerminalRootCharacter A P R n hn
        (y ≫ (principalIsoOnMultiplicationKernel A P R e n).hom.hom.hom) p) := by
  let : IsFinite (K).X.hom := Multiplication.kernelGroup_isFinite_of_pos A n hn
  let i : Group.BaseChange.baseChangedGroup (𝟙 (Base k)) (K) ≅ (K) :=
    groupSchemeBaseChangeId.app (K)
  let e₀ := multiplicationKernelRootCharacterEquivOfPrincipalIso A P R e n hn (T₀)
  let e₂ := Kummer.rootsCharacterPullbackEquiv k p (K) n hn hi
    (Kernel.multiplication_kernel_pow_eq_one A n)
  let χ := multiplicationKernelRootCharacterOfPrincipalIso A P R e n hn (T₀) y
  have hχ : e₀ y = χ :=
    multiplicationKernelRootCharacterEquivOfPrincipalIso_apply A P R e n hn (T₀) y
  have h : i.inv ≫ e₀ y ≫ 𝟙 _ = i.inv ≫ χ :=
    congrArg (fun a => i.inv ≫ a) ((Category.comp_id _).trans hχ)
  change e₂ (i.inv ≫ e₀ y ≫ 𝟙 _) = _
  exact (congrArg e₂ h).trans (Kummer.rootsCharacterPullbackEquiv_apply k p (K) n hn hi
    (Kernel.multiplication_kernel_pow_eq_one A n) (i.inv ≫ χ))

end AlgebraicGeometry.Scheme.RelativePicard
