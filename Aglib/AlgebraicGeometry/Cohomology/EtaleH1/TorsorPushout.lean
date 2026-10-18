/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Current interface basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original construction and mathematical provenance are retained below. -/
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.ExtensionTorsor
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.TorsorClass

/-!
# Genuine coefficient pushouts of abelian sheaf torsors

Construction for `K2-018#eq:k2018-pointed-character`, frozen basis
`7f86e4a1763cc4ec35e9b0a8acd659750355a0de`. The new torsor is the actual
augmentation-one fibre in the pushout of the free-abelian torsor extension.
Its canonical equivariant map proves the cohomological coefficient formula.
No class bijection or transported group structure is used in this construction.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace AlgebraicGeometry.Scheme.EtaleH1
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
def torsorCoefficientExtension : ShortComplex (AbelianSheaf.{u, u + 1} X) :=
  CategoryTheory.Abelian.ExtensionPushout.complex (torsorAugmentationComplex P)
    (torsorDifferenceSheafMap P ≫ q)

/-- This extension is short exact by the proved abelian pushout construction. -/
theorem torsorCoefficientExtension_shortExact : (torsorCoefficientExtension P q).ShortExact :=
  CategoryTheory.Abelian.ExtensionPushout.shortExact _ _ (torsorAugmentation_shortExact P)

/-- Coefficient pushout is constructed as a genuine sheaf torsor. -/
def torsorPushout : Torsor M :=
  extensionFiberTorsor (torsorCoefficientExtension P q) (constantIntegerOne X)
    (torsorCoefficientExtension_shortExact P q)

/-- The canonical generator section in the free abelian sheaf. -/
def torsorGenerator (U : X.Etaleᵒᵖ) (t : P.carrier.obj.obj U) : (torsorFreeSheaf P).obj.obj U :=
  (toSheafify (Scheme.smallEtaleTopology X) (torsorFreePresheaf P)).app U
    (FreeAbelianGroup.of t)

/-- Generator sections respect restriction. -/
theorem torsorGenerator_naturality {U V : X.Etaleᵒᵖ} (f : U ⟶ V)
    (t : P.carrier.obj.obj U) :
    (torsorFreeSheaf P).obj.map f (torsorGenerator P U t) =
      torsorGenerator P V (P.carrier.obj.map f t) := by
  have h := ConcreteCategory.congr_hom
    ((toSheafify (Scheme.smallEtaleTopology X) (torsorFreePresheaf P)).naturality f)
    (FreeAbelianGroup.of t)
  change (toSheafify (Scheme.smallEtaleTopology X) (torsorFreePresheaf P)).app V
      (FreeAbelianGroup.map (P.carrier.obj.map f) (FreeAbelianGroup.of t)) = _ at h
  rw [FreeAbelianGroup.map_of_apply] at h
  exact h.symm

/-- Every torsor generator lies over integer one. -/
theorem torsorGenerator_augmentation (U : X.Etaleᵒᵖ) (t : P.carrier.obj.obj U) :
    (torsorAugmentation P).hom.app U (torsorGenerator P U t) =
      restrictSection (torsorAugmentationComplex P).X₃ (constantIntegerOne X) U := by
  have h := congrArg (fun r => r.app U (FreeAbelianGroup.of t))
    (toSheafify_naturality (Scheme.smallEtaleTopology X) (torsorAugmentationPresheaf P))
  change _ = restrictSection
    ((constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))) (constantIntegerOne X) U
  rw [restrict_constantIntegerOne]
  change (toSheafify (Scheme.smallEtaleTopology X)
      ((Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app U
        (FreeAbelianGroup.lift (fun _ : P.carrier.obj.obj U => (1 : ULift.{u + 1} ℤ))
          (FreeAbelianGroup.of t)) = _ at h
  rw [FreeAbelianGroup.lift_apply_of] at h
  exact h.symm

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
      (torsorDifferenceSheafMap P).hom = torsorKernelDifference P := by
  let adj := sheafificationAdjunction (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}
  change adj.homEquiv _ _ ((adj.homEquiv _ _).symm (torsorKernelDifference P)) = _
  exact (adj.homEquiv _ _).apply_symm_apply _

/-- Positive transport gives the relation `[a+t]-[t] ↦ a` after sheafification. -/
theorem torsorPushoutSection_equivariant (U : X.Etaleᵒᵖ)
    (a : L.obj.obj U) (t : P.carrier.obj.obj U) :
    torsorPushoutSection P q U (P.action U a t) =
      (torsorPushout P q).action U (q.hom.app U a) (torsorPushoutSection P q U t) := by
  let := P.sectionAction U
  let x := AddAction.TorsorAugmentation.generatorDifference (P.action U a t) t
  let k := (toSheafify (Scheme.smallEtaleTopology X) (torsorKernelPresheaf P)).app U x
  have hd : (torsorDifferenceSheafMap P).hom.app U k = a := by
    have h := congrArg (fun r => r.app U x) (torsorDifferenceSheafMap_unit P)
    change (torsorDifferenceSheafMap P).hom.app U k =
      AddAction.TorsorAugmentation.kernelDifference (P.unique_transport U) x at h
    rw [h]
    exact (AddAction.TorsorAugmentation.kernelDifference_generatorDifference _ _ _).trans
      (AddAction.TorsorAugmentation.difference_action _ a t)
  have hi : (torsorKernelSheafInclusion P).hom.app U k =
      torsorGenerator P U (P.action U a t) - torsorGenerator P U t := by
    have h := congrArg (fun r => r.app U x)
      (toSheafify_naturality (Scheme.smallEtaleTopology X) (torsorKernelInclusion P))
    change (toSheafify (Scheme.smallEtaleTopology X) (torsorFreePresheaf P)).app U
      (FreeAbelianGroup.of (P.action U a t) - FreeAbelianGroup.of t) =
        (torsorKernelSheafInclusion P).hom.app U k at h
    exact h.symm.trans (map_sub _ _ _)
  have hc := congrArg (fun r => r.hom.app U k)
    (pushout.condition (f := torsorKernelSheafInclusion P) (g := torsorDifferenceSheafMap P ≫ q))
  change (pushout.inl (torsorKernelSheafInclusion P) (torsorDifferenceSheafMap P ≫ q)).hom.app U
      ((torsorKernelSheafInclusion P).hom.app U k) =
    (pushout.inr (torsorKernelSheafInclusion P) (torsorDifferenceSheafMap P ≫ q)).hom.app U
      (q.hom.app U ((torsorDifferenceSheafMap P).hom.app U k)) at hc
  rw [hd, hi, map_sub] at hc
  apply Subtype.ext
  exact sub_eq_iff_eq_add.mp hc

/-- The canonical coefficient-relative map into the actual pushout torsor. -/
def torsorPushoutMap : Torsor.Hom q P (torsorPushout P q) where
  map := ⟨{
    app U := TypeCat.ofHom (fun t => torsorPushoutSection P q U t)
    naturality {U V} f := by
      ext t
      apply Subtype.ext
      change (pushout.inl (torsorKernelSheafInclusion P) (torsorDifferenceSheafMap P ≫ q)).hom.app V
          (torsorGenerator P V (P.carrier.obj.map f t)) =
        (torsorCoefficientExtension P q).X₂.obj.map f
          ((pushout.inl (torsorKernelSheafInclusion P) (torsorDifferenceSheafMap P ≫ q)).hom.app U
            (torsorGenerator P U t))
      rw [← torsorGenerator_naturality]
      exact ConcreteCategory.congr_hom
        ((pushout.inl (torsorKernelSheafInclusion P) (torsorDifferenceSheafMap P ≫
          q)).hom.naturality f)
        (torsorGenerator P U t) }⟩
  equivariant := torsorPushoutSection_equivariant P q

section ExtClass
universe w
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- Coefficient pushout has exactly the coefficient-change Ext class. -/
theorem torsorExtClass_pushout :
    torsorExtClass (torsorPushout P q) = coefficientMap q (torsorExtClass P) :=
  (torsorExtClass_naturality (torsorPushoutMap P q)).symm

end ExtClass
end AlgebraicGeometry.Scheme.EtaleH1

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 eb3becf21deea0b70ccccc64d94dcafe14dab0cecf72c10ca6e95c277eb17eb5.
Definitions, hypotheses and universes are retained modulo native names. -/
