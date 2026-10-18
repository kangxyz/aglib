/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Current interface basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original construction and mathematical provenance are retained below. -/
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.TorsorPushout

/-!
# The canonical class of an actual extension fibre

Construction for `K2-018#eq:k2018-pointed-character`, frozen basis
`7f86e4a1763cc4ec35e9b0a8acd659750355a0de`. The augmentation-one fibre of an
actual short exact sequence represents its Ext class. The comparison is
proved through the free-abelian augmentation map, with positive transport.
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
variable {X : Scheme.{u}} {L E : AbelianSheaf.{u, u + 1} X}

/-- The actual constant lifted-integer sheaf used in Ext-based cohomology. -/
abbrev constantIntegerSheaf (X : Scheme.{u}) : AbelianSheaf.{u, u + 1} X :=
  (constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))

variable (P : Torsor L) (r : P.carrier ⟶ underlyingSetSheaf E)

/-- The additive presheaf map freely induced by an actual map of sets. -/
def torsorFreeLiftPresheaf : torsorFreePresheaf P ⟶ E.obj where
  app U := AddCommGrpCat.ofHom (FreeAbelianGroup.lift (fun t => r.hom.app U t))
  naturality {U V} f := by
    apply AddCommGrpCat.ext
    intro x
    change FreeAbelianGroup.lift (fun t => r.hom.app V t)
        (FreeAbelianGroup.map (P.carrier.obj.map f) x) =
      E.obj.map f (FreeAbelianGroup.lift (fun t => r.hom.app U t) x)
    rw [← FreeAbelianGroup.lift_comp]
    have hn : (fun t => r.hom.app V (P.carrier.obj.map f t)) =
        (fun t => E.obj.map f (r.hom.app U t)) :=
      funext (fun t => ConcreteCategory.congr_hom (r.hom.naturality f) t)
    rw [show (fun t => r.hom.app V t) ∘ P.carrier.obj.map f =
      (E.obj.map f).hom ∘ (fun t => r.hom.app U t) from hn]
    exact FreeAbelianGroup.lift_comp_apply _ _ _

/-- The actual free-abelian sheaf map. -/
def torsorFreeLiftSheaf : torsorFreeSheaf P ⟶ E :=
  ((sheafificationAdjunction (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).homEquiv
    (torsorFreePresheaf P) E).symm (torsorFreeLiftPresheaf P r)

/-- The free-sheaf map has the specified values on generators. -/
theorem torsorFreeLiftSheaf_unit :
    toSheafify (Scheme.smallEtaleTopology X) (torsorFreePresheaf P) ≫
      (torsorFreeLiftSheaf P r).hom = torsorFreeLiftPresheaf P r := by
  let adj := sheafificationAdjunction (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}
  change adj.homEquiv _ _ ((adj.homEquiv _ _).symm (torsorFreeLiftPresheaf P r)) = _
  exact (adj.homEquiv _ _).apply_symm_apply _

variable (i : L ⟶ E)
variable (heq : ∀ U a t, r.hom.app U (P.action U a t) =
  i.hom.app U a + (show E.obj.obj U from r.hom.app U t))

include heq in
/-- Equivariance identifies the free-map restriction to the augmentation kernel
with inclusion of the canonical torsor difference. -/
theorem torsorFreeLiftPresheaf_kernel :
    torsorKernelInclusion P ≫ torsorFreeLiftPresheaf P r = torsorKernelDifference P ≫ i.hom := by
  ext U x
  let := P.sectionAction U
  let := (trivialTorsor E).sectionAction U
  have h := AddAction.TorsorAugmentation.kernelDifference_naturality (P.unique_transport U)
    ((trivialTorsor E).unique_transport U) (i.hom.app U).hom (r.hom.app U) (heq U) x
  rw [AddAction.TorsorAugmentation.kernelDifference_eq_based
    ((trivialTorsor E).unique_transport U) (0 : E.obj.obj U)] at h
  have hb : AddAction.TorsorAugmentation.basedDifference ((trivialTorsor E).unique_transport U)
      (0 : E.obj.obj U) = FreeAbelianGroup.lift (fun t : E.obj.obj U => t) := by
    apply FreeAbelianGroup.lift_ext
    intro t
    rw [AddAction.TorsorAugmentation.basedDifference_of]
    change AddAction.TorsorAugmentation.difference ((trivialTorsor E).unique_transport U) t 0 =
      FreeAbelianGroup.lift (fun t : E.obj.obj U => t) (FreeAbelianGroup.of t)
    rw [FreeAbelianGroup.lift_apply_of]
    exact AddAction.TorsorAugmentation.difference_eq _ t 0 (show E.obj.obj U from t)
      (add_zero (show E.obj.obj U from t))
  rw [hb] at h
  change FreeAbelianGroup.lift (fun t => r.hom.app U t) x.val = _
  exact (FreeAbelianGroup.lift_comp (r.hom.app U) (fun t : E.obj.obj U => t) x.val).trans h

include heq in
/-- The sheafified kernel square follows from the actual adjunction. -/
theorem torsorFreeLiftSheaf_kernel :
    torsorKernelSheafInclusion P ≫ torsorFreeLiftSheaf P r = torsorDifferenceSheafMap P ≫ i := by
  let adj := sheafificationAdjunction (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}
  apply (adj.homEquiv (torsorKernelPresheaf P) E).injective
  change adj.homEquiv _ _
      ((presheafToSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).map
        (torsorKernelInclusion P) ≫ (adj.homEquiv _ _).symm (torsorFreeLiftPresheaf P r)) =
    adj.homEquiv _ _ ((adj.homEquiv _ _).symm (torsorKernelDifference P) ≫ i)
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact torsorFreeLiftPresheaf_kernel P r i heq

variable (g : E ⟶ constantIntegerSheaf X)
variable (hover : ∀ U t, g.hom.app U (r.hom.app U t) =
  restrictSection (constantIntegerSheaf X) (constantIntegerOne X) U)

include hover in
/-- An actual lift into the augmentation-one fibre commutes with augmentation. -/
theorem torsorFreeLiftPresheaf_projection :
    torsorFreeLiftPresheaf P r ≫ g.hom = torsorAugmentationPresheaf P ≫
      toSheafify (Scheme.smallEtaleTopology X)
        ((Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))) := by
  ext U x
  change g.hom.app U (FreeAbelianGroup.lift (fun t => r.hom.app U t) x) =
    (toSheafify (Scheme.smallEtaleTopology X)
      ((Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app U
        (FreeAbelianGroup.lift (fun _ : P.carrier.obj.obj U => (1 : ULift.{u + 1} ℤ)) x)
  induction x using FreeAbelianGroup.induction_on with
  | zero => simp only [map_zero]
  | of t =>
    rw [FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of,
      hover, restrict_constantIntegerOne]
    rfl
  | neg t ht => simp only [map_neg, ht]
  | add x y hx hy => simp only [map_add, hx, hy]

include hover in
/-- The actual free-sheaf morphism lies over the identity of constant ℤ. -/
theorem torsorFreeLiftSheaf_projection :
    torsorFreeLiftSheaf P r ≫ g = torsorAugmentation P := by
  let adj := sheafificationAdjunction (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}
  apply (adj.homEquiv (torsorFreePresheaf P) (constantIntegerSheaf X)).injective
  rw [Adjunction.homEquiv_naturality_right]
  change adj.homEquiv _ _ ((adj.homEquiv _ _).symm (torsorFreeLiftPresheaf P r)) ≫ g.hom = _
  rw [Equiv.apply_symm_apply]
  change torsorFreeLiftPresheaf P r ≫ g.hom =
    toSheafify (Scheme.smallEtaleTopology X) (torsorFreePresheaf P) ≫
      (torsorAugmentation P).hom
  exact (torsorFreeLiftPresheaf_projection P r g hover).trans
    (toSheafify_naturality (Scheme.smallEtaleTopology X) (torsorAugmentationPresheaf P))

variable (hig : i ≫ g = 0)

/-- The actual augmentation sequence maps to the given extension. -/
def torsorAugmentationToExtension :
    torsorAugmentationComplex P ⟶ ShortComplex.mk i g hig where
  τ₁ := torsorDifferenceSheafMap P
  τ₂ := torsorFreeLiftSheaf P r
  τ₃ := 𝟙 _
  comm₁₂ := (torsorFreeLiftSheaf_kernel P r i heq).symm
  comm₂₃ := by
    change torsorFreeLiftSheaf P r ≫ g = torsorAugmentation P ≫ 𝟙 _
    rw [Category.comp_id]
    exact torsorFreeLiftSheaf_projection P r g hover

section ExtClass
universe w
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

include r heq hover in
/-- A coefficient-equivariant map into an augmentation-one extension fibre
identifies the canonical class with that actual short exact extension. -/
theorem torsorExtClass_of_extensionLift (hS : (ShortComplex.mk i g hig).ShortExact) :
    torsorExtClass P = hS.extClass := by
  have hn := ShortComplex.ShortExact.extClass_naturality
    (torsorAugmentation_shortExact P) hS
    (torsorAugmentationToExtension P r i heq g hover hig)
  change (torsorAugmentation_shortExact P).extClass.comp
      (Abelian.Ext.mk₀ (torsorDifferenceSheafMap P)) (add_zero 1) =
    (Abelian.Ext.mk₀ (𝟙 _)).comp hS.extClass (zero_add 1) at hn
  rw [Abelian.Ext.mk₀_id_comp] at hn
  exact (torsorExtClass_eq P).trans hn

end ExtClass

variable {P r heq hover}

/-- Actual inclusion of the extension fibre as sections of the middle sheaf. -/
noncomputable def extensionFiberInclusion
    (hS : (ShortComplex.mk i g hig).ShortExact) :
    (extensionFiberTorsor (ShortComplex.mk i g hig) (constantIntegerOne X) hS).carrier ⟶
      underlyingSetSheaf E :=
  ⟨{ app _ := TypeCat.ofHom Subtype.val
     naturality {_ _} _ := rfl }⟩

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
end AlgebraicGeometry.Scheme.EtaleH1

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 bc2d2205730e5ef184ebae79c97c46949b2965c5ad4ffdc1b315e58b27678390.
Definitions, hypotheses and universes are retained modulo native names. -/
