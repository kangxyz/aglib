/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsor.Pushout
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.ExtensionTorsor
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.TorsorClass

/-! # The original etale coefficient pushout

The original terminal-one fibre and literal generator values are retained.
Generic proofs supply the extension, equivariance and class formula.
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
variable {X : Scheme.{u}} {L M : AbelianSheaf.{u, u + 1} X}

/-- The restriction of integer one is integer one on every étale test object. -/
theorem restrict_constantIntegerOne (U : X.Etaleᵒᵖ) :
    restrictSection
      ((constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))) (constantIntegerOne X) U =
    (toSheafify (Scheme.smallEtaleTopology X)
      ((Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app U
        (ULift.up 1) := by
  exact (ConcreteCategory.congr_hom
    ((toSheafify (Scheme.smallEtaleTopology X)
      ((Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).naturality
        ((etaleTerminalIsTerminal X).from U.unop).op) (ULift.up 1)).symm

variable (P : Torsor L) (q : L ⟶ M)

/-- The actual coefficient pushout of the augmentation sequence. -/
abbrev torsorCoefficientExtension : ShortComplex (AbelianSheaf.{u, u + 1} X) :=
  CategoryTheory.Sheaf.torsorCoefficientExtension P q

/-- This extension is short exact by the proved abelian pushout construction. -/
theorem torsorCoefficientExtension_shortExact : (torsorCoefficientExtension P q).ShortExact :=
  CategoryTheory.Sheaf.torsorCoefficientExtension_shortExact P q

/-- Coefficient pushout is constructed as a genuine sheaf torsor. -/
def torsorPushout : Torsor M :=
  extensionFiberTorsor (torsorCoefficientExtension P q) (constantIntegerOne X)
    (torsorCoefficientExtension_shortExact P q)

/-- The terminal-site fibre is exactly the intrinsic coefficient-pushout torsor. -/
theorem torsorPushout_eq_generic :
    torsorPushout P q = CategoryTheory.Sheaf.torsorPushout P q := by
  exact congrArg
    (fun z : Topos.GlobalPoint (underlyingSetSheaf (torsorCoefficientExtension P q).X₃) =>
      CategoryTheory.Sheaf.extensionFiberTorsor (torsorCoefficientExtension P q) z
        (torsorCoefficientExtension_shortExact P q))
    (constantIntegerOne_asGlobalPoint (X := X))

/-- The canonical generator section in the free abelian sheaf. -/
abbrev torsorGenerator (U : X.Etaleᵒᵖ) (t : P.carrier.obj.obj U) : (torsorFreeSheaf P).obj.obj U :=
  CategoryTheory.Sheaf.torsorGenerator P U t

/-- Generator sections respect restriction. -/
theorem torsorGenerator_naturality {U V : X.Etaleᵒᵖ} (f : U ⟶ V)
    (t : P.carrier.obj.obj U) :
    (torsorFreeSheaf P).obj.map f (torsorGenerator P U t) =
      torsorGenerator P V (P.carrier.obj.map f t) :=
  CategoryTheory.Sheaf.torsorGenerator_naturality P f t

/-- Every torsor generator lies over integer one. -/
theorem torsorGenerator_augmentation (U : X.Etaleᵒᵖ) (t : P.carrier.obj.obj U) :
    (torsorAugmentation P).hom.app U (torsorGenerator P U t) =
      restrictSection (torsorAugmentationComplex P).X₃ (constantIntegerOne X) U := by
  exact (CategoryTheory.Sheaf.torsorGenerator_augmentation P U t).trans
    (restrict_constantIntegerOne (X := X) U).symm

/-- The actual point map into the coefficient-pushout extension. -/
def torsorPushoutSection (U : X.Etaleᵒᵖ) (t : P.carrier.obj.obj U) :
    (torsorPushout P q).carrier.obj.obj U :=
  ⟨(pushout.inl (torsorKernelSheafInclusion P) (torsorDifferenceSheafMap P ≫ q)).hom.app U
    (torsorGenerator P U t), by
    have h := congrArg (fun r => r.hom.app U (torsorGenerator P U t))
      (CategoryTheory.Abelian.ExtensionPushout.inl_projection (torsorAugmentationComplex P)
        (torsorDifferenceSheafMap P ≫ q))
    exact h.trans (torsorGenerator_augmentation P U t)⟩

/-- The canonical difference map is the adjoint extension of its explicit
presheaf formula. -/
theorem torsorDifferenceSheafMap_unit :
    toSheafify (Scheme.smallEtaleTopology X) (torsorKernelPresheaf P) ≫
      (torsorDifferenceSheafMap P).hom = torsorKernelDifference P :=
  CategoryTheory.Sheaf.torsorDifferenceSheafMap_unit P

/-- Positive transport gives the relation `[a+t]-[t] ↦ a` after sheafification. -/
theorem torsorPushoutSection_equivariant (U : X.Etaleᵒᵖ)
    (a : L.obj.obj U) (t : P.carrier.obj.obj U) :
    torsorPushoutSection P q U (P.action U a t) =
      (torsorPushout P q).action U (q.hom.app U a) (torsorPushoutSection P q U t) := by
  apply Subtype.ext
  change (_ : (torsorCoefficientExtension P q).X₂.obj.obj U) = _
  have h := congrArg
    (fun x : (CategoryTheory.Sheaf.torsorPushout P q).carrier.obj.obj U =>
      (show (torsorCoefficientExtension P q).X₂.obj.obj U from x.val))
    (CategoryTheory.Sheaf.torsorPushoutSection_equivariant P q U a t)
  exact h

/-- The original generator map, with generic naturality and equivariance proofs. -/
def torsorPushoutMap : Torsor.Hom q P (torsorPushout P q) where
  map := ⟨{
    app U := TypeCat.ofHom (fun t => torsorPushoutSection P q U t)
    naturality {U V} f := by
      ext t
      apply Subtype.ext
      change (_ : (torsorCoefficientExtension P q).X₂.obj.obj V) = _
      have h := congrArg
        (fun x : (CategoryTheory.Sheaf.torsorPushout P q).carrier.obj.obj V =>
          (show (torsorCoefficientExtension P q).X₂.obj.obj V from x.val))
        (ConcreteCategory.congr_hom
          ((CategoryTheory.Sheaf.torsorPushoutMap P q).map.hom.naturality f) t)
      exact h }⟩
  equivariant := torsorPushoutSection_equivariant P q

section ExtClass
universe w
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- Coefficient pushout has exactly the coefficient-change Ext class. -/
theorem torsorExtClass_pushout :
    torsorExtClass (torsorPushout P q) = coefficientMap q (torsorExtClass P) :=
  (torsorExtClass_naturality (torsorPushoutMap P q)).symm

end ExtClass
end AlgebraicGeometry.Scheme.EtaleCohomology

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 eb3becf21deea0b70ccccc64d94dcafe14dab0cecf72c10ca6e95c277eb17eb5.
Definitions, hypotheses and universes are retained modulo native names. -/
