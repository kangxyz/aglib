/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.WeilPairing.Character
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RepresentedInclusion
public import Aglib.AlgebraicGeometry.Group.CartierDuality.CharacterRoots
public import Aglib.AlgebraicGeometry.Group.Kernel.MultiplicationAnnihilation
public import Aglib.AlgebraicGeometry.Group.MultiplicationSmoothEtale
public import Aglib.AlgebraicGeometry.Picard.Kernel.TorsorCharacter.FramePushout.Cohomology

/-! # The original Weil character and the original Poincaré frame class

On the original multiplication family, the root-valued Cartier character
extends the actual cover class to the Kummer class with the prescribed
Poincaré Picard image.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open Scheme.OverField Scheme.Group Scheme.EtaleCohomology Scheme.Modules.Invertible
open Scheme.Group.CartierDuality (characterRoots characterRoots_comp_inclusion)
open Scheme.Group.MultiplicativeGroup
  (rootsGroupScheme rootsInclusionHom rootsInclusionHom_baseChange)
open GroupCohomology.Kummer.Coefficients
open scoped CategoryTheory.MonObj

universe u w

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Scheme.RelativePicard

open KernelFramePushout

attribute [local instance] Over.cartesianMonoidalCategory hasSheafifyLarge
  familyCoefficient_isCommMonObj

variable {k : Type u} [Field k] (A : Grp (FScheme k))
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf A.X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  [IsHProjective A.X.hom] [GeometricallyIntegral A.X.hom] [Smooth A.X.hom]
  [IsSeparated P.obj.hom] [IsCommMonObj A.X]
  (n : ℕ) (hn : 0 < n) {T : FScheme k} (t : T ⟶ (dualMultiplicationKernel A P R n).X)

set_option hygiene false in
local notation "qₙ" => MultiplicationKernel.multiplicationHom A n
set_option hygiene false in
local notation "Aₜ" => Functor.obj (Functor.mapGrp (Over.pullback T.hom)) A
set_option hygiene false in
local notation "Yₜ" => (Aₜ).X.left
set_option hygiene false in
local notation "t₀" => t ≫ (dualMultiplicationKernelInclusion A P R n).hom.hom

set_option hygiene false in
local notation "Mₜ" => (poincarePullback A.X P R (t₀)).bundle
set_option hygiene false in
local notation "aₜ" => poincareKernelFrame A A P R P R (qₙ) (t₀)
  (by rw [Category.assoc, dualMultiplicationKernelInclusion_comp_pullback A P R n, MonObj.comp_one])

/-- The fixed-slot Cartier roots character on the actual target of the
original multiplication family. -/
def multiplicationFamilyRootCharacter :
    familyCoefficient (qₙ) T ⟶ rootsGroupScheme (Yₜ) n := by
  letI : IsFinite (Kernel.group (qₙ)).X.hom :=
    Multiplication.kernelGroup_isFinite_of_pos A n hn
  letI : IsCommMonObj (Kernel.group (qₙ)).X := Kernel.isCommMonObj_group (qₙ)
  exact (Over.pullback (Aₜ).X.hom).mapGrp.map
      (characterRoots (Kernel.group (qₙ)) T
        (t ≫ (multiplicationKernelCartierHom A P R n hn).hom.hom) n
        (Kernel.multiplication_kernel_pow_eq_one A n)) ≫
    (MultiplicativeBaseChange.rootsBaseChangeIso (Aₜ).X.hom n).hom

/-- The actual root inclusion recovers the positive Poincaré frame character. -/
theorem multiplicationFamilyRootCharacter_comp_inclusion :
    multiplicationFamilyRootCharacter A P R n hn t ≫ rootsInclusionHom (Yₜ) n =
      familyCharacter (qₙ) T (Mₜ) (aₜ) := by
  let : IsFinite (Kernel.group (qₙ)).X.hom :=
    Multiplication.kernelGroup_isFinite_of_pos A n hn
  let : IsCommMonObj (Kernel.group (qₙ)).X := Kernel.isCommMonObj_group (qₙ)
  unfold multiplicationFamilyRootCharacter
  rw [Category.assoc, rootsInclusionHom_baseChange, ← Category.assoc, ← Functor.map_comp,
    characterRoots_comp_inclusion, characterEquiv_comp_multiplicationKernelCartierHom A P R n hn t,
    familyCharacter_eq, poincareKernelCharacter]

/-- The represented comparison uses the literal Kummer coefficient inclusion. -/
theorem representedSheafMap_multiplicationFamilyRootCharacter_comp_inclusion :
    representedSheafMap (multiplicationFamilyRootCharacter A P R n hn t) ≫ inclusion (Yₜ) n =
      representedSheafMap (familyCharacter (qₙ) T (Mₜ) (aₜ)) := by
  calc
    _ = representedSheafMap (multiplicationFamilyRootCharacter A P R n hn t ≫
          rootsInclusionHom (Yₜ) n) := by
      rw [representedSheafMap_comp, representedSheafMap_rootsInclusionHom]
    _ = _ := congrArg (fun f => representedSheafMap f)
      (multiplicationFamilyRootCharacter_comp_inclusion A P R n hn t)

variable [HasExt.{w} (AbelianSheaf.{u, u + 1} (Yₜ))] (hu : IsUnit (n : k))

/-- The original multiplication cover class pushed along the fixed-slot
Cartier roots character. -/
def multiplicationFamilyKummerClass : H1Etale (Yₜ) (mu (Yₜ) n) := by
  let hf := Multiplication.multiplicationHom_finite_flat_surjective A n hn
  letI : IsFinite (qₙ).hom.hom.left := hf.1
  letI : Surjective (qₙ).hom.hom.left := hf.2.2
  letI : Etale (qₙ).hom.hom.left := by
    simpa only [MultiplicationKernel.multiplicationHom_hom, MultiplicationKernel.multiplication]
      using Multiplication.multiplication_etale_of_smooth_of_isUnit A n hu
  exact coefficientMap (M := mu (Yₜ) n)
    (representedSheafMap (multiplicationFamilyRootCharacter A P R n hn t))
    (torsorExtClass (familyCoverTorsor (qₙ) T))

/-- The pushed root class has the original normalized Poincaré Picard image. -/
theorem multiplicationFamilyKummerClass_inclusion :
    coefficientMap (inclusion (Yₜ) n) (multiplicationFamilyKummerClass A P R n hn t hu) =
      FrameTensor.picardH1Equiv.{u, w} (Yₜ) (classOf (Yₜ) (Mₜ)) := by
  let hf := Multiplication.multiplicationHom_finite_flat_surjective A n hn
  let : IsFinite (qₙ).hom.hom.left := hf.1
  let : Surjective (qₙ).hom.hom.left := hf.2.2
  let : Etale (qₙ).hom.hom.left := by
    simpa only [MultiplicationKernel.multiplicationHom_hom, MultiplicationKernel.multiplication]
      using Multiplication.multiplication_etale_of_smooth_of_isUnit A n hu
  let χ : representedSheaf (familyCoefficient (qₙ) T) ⟶ mu (Yₜ) n :=
    representedSheafMap (multiplicationFamilyRootCharacter A P R n hn t)
  let c := torsorExtClass (familyCoverTorsor (qₙ) T)
  have hχ : χ ≫ inclusion (Yₜ) n =
      representedSheafMap (familyCharacter (qₙ) T (Mₜ) (aₜ)) :=
    representedSheafMap_multiplicationFamilyRootCharacter_comp_inclusion A P R n hn t
  change Sheaf.H.map (inclusion (Yₜ) n) 1 (Sheaf.H.map χ 1 c) = _
  rw [← Sheaf.H.map_comp_apply, hχ]
  exact familyFrameClass_eq (qₙ) T (Mₜ) (aₜ)

/-- The inverse pushed root class has the original coframe Picard image. -/
theorem neg_multiplicationFamilyKummerClass_inclusion :
    coefficientMap (inclusion (Yₜ) n) (-multiplicationFamilyKummerClass A P R n hn t hu) =
      FrameTensor.picardH1Equiv.{u, w} (Yₜ) (-classOf (Yₜ) (Mₜ)) := by
  rw [map_neg, multiplicationFamilyKummerClass_inclusion, map_neg]

end AlgebraicGeometry.Scheme.RelativePicard
