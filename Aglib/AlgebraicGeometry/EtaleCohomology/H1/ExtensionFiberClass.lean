/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsor.Classification
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.TorsorPushout

/-! # The class of the original etale extension fibre

The free lift and the actual extension comparison specialize the generic proof.
The terminal-one predicate is retained literally at the Scheme boundary.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology
universe u
attribute [local instance] hasSheafifyLarge
variable {X : Scheme.{u}} {L E : AbelianSheaf.{u, u + 1} X}

/-- The same actual constant lifted-integer sheaf used by native cohomology. -/
abbrev constantIntegerSheaf (X : Scheme.{u}) : AbelianSheaf.{u, u + 1} X :=
  CategoryTheory.Sheaf.constantIntegerSheaf (Scheme.smallEtaleTopology X)

variable (P : Torsor L) (r : P.carrier ⟶ underlyingSetSheaf E)

/-- The additive presheaf map freely induced by an actual map of sets. -/
abbrev torsorFreeLiftPresheaf : torsorFreePresheaf P ⟶ E.obj :=
  CategoryTheory.Sheaf.torsorFreeLiftPresheaf P r

/-- The actual free-abelian sheaf map. -/
abbrev torsorFreeLiftSheaf : torsorFreeSheaf P ⟶ E :=
  CategoryTheory.Sheaf.torsorFreeLiftSheaf P r

/-- The free-sheaf map has the specified values on generators. -/
theorem torsorFreeLiftSheaf_unit :
    toSheafify (Scheme.smallEtaleTopology X) (torsorFreePresheaf P) ≫
      (torsorFreeLiftSheaf P r).hom = torsorFreeLiftPresheaf P r :=
  CategoryTheory.Sheaf.torsorFreeLiftSheaf_unit P r

variable (i : L ⟶ E)
variable (heq : ∀ U a t, r.hom.app U (P.action U a t) =
  i.hom.app U a + (show E.obj.obj U from r.hom.app U t))

include heq in
/-- Equivariance identifies the free-map restriction to the augmentation kernel
with inclusion of the canonical torsor difference. -/
theorem torsorFreeLiftPresheaf_kernel :
    torsorKernelInclusion P ≫ torsorFreeLiftPresheaf P r = torsorKernelDifference P ≫ i.hom :=
  CategoryTheory.Sheaf.torsorFreeLiftPresheaf_kernel P r i heq

include heq in
/-- The sheafified kernel square follows from the actual adjunction. -/
theorem torsorFreeLiftSheaf_kernel :
    torsorKernelSheafInclusion P ≫ torsorFreeLiftSheaf P r = torsorDifferenceSheafMap P ≫ i :=
  CategoryTheory.Sheaf.torsorFreeLiftSheaf_kernel P r i heq

variable (g : E ⟶ constantIntegerSheaf X)
variable (hover : ∀ U t, g.hom.app U (r.hom.app U t) =
  restrictSection (constantIntegerSheaf X) (constantIntegerOne X) U)

include hover in
/-- An actual lift into the augmentation-one fibre commutes with augmentation. -/
theorem torsorFreeLiftPresheaf_projection :
    torsorFreeLiftPresheaf P r ≫ g.hom = torsorAugmentationPresheaf P ≫
      toSheafify (Scheme.smallEtaleTopology X)
        ((Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))) :=
  CategoryTheory.Sheaf.torsorFreeLiftPresheaf_projection P r g
    (fun U t => (hover U t).trans (restrict_constantIntegerOne U))

include hover in
/-- The actual free-sheaf morphism lies over the identity of constant ℤ. -/
theorem torsorFreeLiftSheaf_projection :
    torsorFreeLiftSheaf P r ≫ g = torsorAugmentation P :=
  CategoryTheory.Sheaf.torsorFreeLiftSheaf_projection P r g
    (fun U t => (hover U t).trans (restrict_constantIntegerOne U))

variable (hig : i ≫ g = 0)

/-- The actual augmentation sequence maps to the given extension. -/
abbrev torsorAugmentationToExtension :
    torsorAugmentationComplex P ⟶ ShortComplex.mk i g hig :=
  CategoryTheory.Sheaf.torsorAugmentationToExtension P r i heq g
    (fun U t => (hover U t).trans (restrict_constantIntegerOne U)) hig

section ExtClass
universe w
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

include r heq hover in
/-- A coefficient-equivariant map into an augmentation-one extension fibre
identifies the canonical class with that actual short exact extension. -/
theorem torsorExtClass_of_extensionLift (hS : (ShortComplex.mk i g hig).ShortExact) :
    torsorExtClass P = hS.extClass :=
  CategoryTheory.Sheaf.torsorExtClass_of_extensionLift P r i heq g
    (fun U t => (hover U t).trans (restrict_constantIntegerOne U)) hig hS

end ExtClass

variable {P r heq hover}

/-- Actual inclusion of the extension fibre as sections of the middle sheaf. -/
abbrev extensionFiberInclusion
    (hS : (ShortComplex.mk i g hig).ShortExact) :
    (extensionFiberTorsor (ShortComplex.mk i g hig) (constantIntegerOne X) hS).carrier ⟶
      underlyingSetSheaf E :=
  CategoryTheory.Sheaf.extensionFiberInclusion (ShortComplex.mk i g hig)
    ((Topos.globalPointTerminalEquiv (etaleTerminalIsTerminal X)
      (underlyingSetSheaf (constantIntegerSheaf X))).symm (constantIntegerOne X))

section ExtClass
universe w
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- The augmentation-one fibre of an actual short exact extension has exactly
that extension's canonical Ext class, with no bijectivity assumption. -/
theorem torsorExtClass_extensionFiber (hS : (ShortComplex.mk i g hig).ShortExact) :
    torsorExtClass (extensionFiberTorsor (ShortComplex.mk i g hig) (constantIntegerOne X) hS) =
      hS.extClass :=
  torsorExtClass_of_extensionLift
    (extensionFiberTorsor (ShortComplex.mk i g hig) (constantIntegerOne X) hS)
    (extensionFiberInclusion i g hig hS) i (fun _ _ _ => rfl) g
    (fun _ t => t.property) hig hS

end ExtClass
end AlgebraicGeometry.Scheme.EtaleCohomology

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 bc2d2205730e5ef184ebae79c97c46949b2965c5ad4ffdc1b315e58b27678390.
Definitions, hypotheses and universes are retained modulo native names. -/
