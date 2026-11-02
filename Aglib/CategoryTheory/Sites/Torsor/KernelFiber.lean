/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsor.ExtensionFiber
public import Aglib.CategoryTheory.Sites.Torsor.Adjunction

/-!
# Actual fibres of coefficient-equivariant torsor maps

The zero fibre retains the original section subtype and the action of the actual
kernel inclusion. The actual kernel universal property lifts the unique transporter;
local surjectivity of the coefficient map supplies local fibre sections. No global
torsor section, terminal object or choice of another kernel is required.

Maps between extension fibres use the same literal subtype construction and their
actual coefficient squares, in the existing site-adjoint torsor presentation.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf

universe u v w u' v'
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {A B : Sheaf J AddCommGrpCat.{w}}
variable (P : Torsor A) (φ : P.carrier ⟶ underlyingSetSheaf B)

/-- The actual torsor-map value in the original additive target component. -/
def kernelFiberValue (U : Cᵒᵖ) (s : P.carrier.obj.obj U) : B.obj.obj U := φ.hom.app U s

/-- The original map commutes with restriction of torsor sections. -/
theorem kernelFiber_value_naturality {U V : Cᵒᵖ} (f : U ⟶ V)
    (s : P.carrier.obj.obj U) :
    kernelFiberValue P φ V (P.carrier.obj.map f s) = B.obj.map f (kernelFiberValue P φ U s) :=
  ConcreteCategory.congr_hom (φ.hom.naturality f) s

/-- The literal zero-fibre subfunctor of the original torsor carrier. -/
def kernelFiberSubfunctor : Subfunctor P.carrier.obj where
  obj U := {s | kernelFiberValue P φ U s = 0}
  map {U V} f s hs := by
    change kernelFiberValue P φ V (P.carrier.obj.map f s) = 0
    rw [kernelFiber_value_naturality, hs, map_zero]

/-- The zero-fibre predicate is local because its target is a sheaf. -/
theorem kernelFiber_isSheaf : Presheaf.IsSheaf J (kernelFiberSubfunctor P φ).toFunctor := by
  rw [isSheaf_iff_isSheaf_of_type]
  apply (Subfunctor.isSheaf_iff (J := J) (kernelFiberSubfunctor P φ)
    ((isSheaf_iff_isSheaf_of_type _ _).mp P.carrier.property)).2
  intro U s hs
  apply (((isSheaf_iff_isSheaf_of_type _ _).mp
    (underlyingSetSheaf B).property).isSeparated _ hs).ext
  intro V f hf
  change B.obj.map f.op (kernelFiberValue P φ U s) = B.obj.map f.op 0
  rw [map_zero, ← kernelFiber_value_naturality]
  exact hf

/-- The zero fibre, with precisely its original section subtype. -/
def kernelFiberSheaf : Sheaf J (Type w) :=
  ⟨(kernelFiberSubfunctor P φ).toFunctor, kernelFiber_isSheaf P φ⟩

variable {L : Sheaf J AddCommGrpCat.{w}}
variable (i : L ⟶ A) (p : A ⟶ B) (h : i ≫ p = 0)
variable (hk : IsLimit (KernelFork.ofι i h))

/-- Evaluation preserves the supplied actual kernel fork. -/
def kernelFiberSectionKernel (U : Cᵒᵖ) :
    IsLimit (KernelFork.ofι (i.hom.app U)
      (show i.hom.app U ≫ p.hom.app U = 0 from
        congrArg (fun q => q.hom.app U) h)) :=
  KernelFork.mapIsLimit _ hk (sheafToPresheaf J AddCommGrpCat.{w} ⋙
    (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{w}).obj U)

/-- A coefficient-equivariant torsor map has an actual torsor as its zero fibre.
The kernel is the supplied one, and local nonemptiness uses only local surjectivity. -/
def kernelFiberTorsor [Sheaf.IsLocallySurjective p]
    (hφ : ∀ U a s, kernelFiberValue P φ U (P.action U a s) =
      p.hom.app U a + kernelFiberValue P φ U s) : Torsor L where
  carrier := kernelFiberSheaf P φ
  action U a s := ⟨P.action U (i.hom.app U a) s.val, by
    change kernelFiberValue P φ U (P.action U (i.hom.app U a) s.val) = 0
    rw [hφ, s.property]
    have hz : p.hom.app U (i.hom.app U a) = 0 :=
      ConcreteCategory.congr_hom (congrArg (fun q => q.hom.app U) h) a
    rw [hz, add_zero]⟩
  zero_action U s := by
    change {x : P.carrier.obj.obj U // kernelFiberValue P φ U x = 0} at s
    apply Subtype.ext
    change P.action U (i.hom.app U (0 : L.obj.obj U)) s.val = s.val
    exact (congrArg (fun a : A.obj.obj U => P.action U a s.val)
      (i.hom.app U).hom.map_zero).trans (P.zero_action U s.val)
  add_action U a b s := by
    change {x : P.carrier.obj.obj U // kernelFiberValue P φ U x = 0} at s
    apply Subtype.ext
    change P.action U (i.hom.app U (a + b)) s.val =
      P.action U (i.hom.app U a) (P.action U (i.hom.app U b) s.val)
    exact (congrArg (fun c : A.obj.obj U => P.action U c s.val)
      ((i.hom.app U).hom.map_add a b)).trans
        (P.add_action U (i.hom.app U a) (i.hom.app U b) s.val)
  naturality {U V} f a s := by
    apply Subtype.ext
    change P.carrier.obj.map f (P.action U (i.hom.app U a) s.val) =
      P.action V (i.hom.app V (L.obj.map f a)) (P.carrier.obj.map f s.val)
    rw [P.naturality]
    exact congrArg (fun b => P.action V b (P.carrier.obj.map f s.val))
      (ConcreteCategory.congr_hom (i.hom.naturality f) a).symm
  unique_transport U s t := by
    change {x : P.carrier.obj.obj U // kernelFiberValue P φ U x = 0} at s t
    obtain ⟨a, ha, hu⟩ := P.unique_transport U s.val t.val
    have hp : p.hom.app U a = 0 := by
      have ht := congrArg (kernelFiberValue P φ U) ha
      rw [hφ, s.property, t.property, add_zero] at ht
      exact ht
    let SU : ShortComplex AddCommGrpCat.{w} := ShortComplex.mk
      (i.hom.app U) (p.hom.app U) (congrArg (fun q => q.hom.app U) h)
    have hex : SU.Exact := SU.exact_of_f_is_kernel (kernelFiberSectionKernel i p h hk U)
    obtain ⟨b, hb⟩ := (ShortComplex.ab_exact_iff SU).mp hex a hp
    have hi : Function.Injective (i.hom.app U) := by
      let : Mono (i.hom.app U) := mono_of_isLimit_fork (kernelFiberSectionKernel i p h hk U)
      exact (AddCommGrpCat.mono_iff_injective _).mp inferInstance
    refine ⟨b, ?_, ?_⟩
    · apply Subtype.ext
      change P.action U (i.hom.app U b) s.val = t.val
      exact (congrArg (fun c : A.obj.obj U => P.action U c s.val) hb).trans ha
    · intro c hc
      apply hi
      exact (hu _ (congrArg Subtype.val hc)).trans hb.symm
  locally_nonempty U := by
    apply J.transitive (P.locally_nonempty U)
    intro V f hf
    obtain ⟨s⟩ := hf
    refine J.superset_covering ?_
      (Presheaf.imageSieve_mem J p.hom (-kernelFiberValue P φ (op V) s))
    rintro W g ⟨a, ha⟩
    refine ⟨⟨P.action (op W) a (P.carrier.obj.map g.op s), ?_⟩⟩
    change kernelFiberValue P φ (op W) (P.action (op W) a (P.carrier.obj.map g.op s)) = 0
    rw [hφ, ha, map_neg, kernelFiber_value_naturality, neg_add_cancel]

section AdjointFibres

variable {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
variable (F : C ⥤ D) [F.IsContinuous J K]
variable (E : ShortComplex (Sheaf J AddCommGrpCat.{w}))
variable (E' : ShortComplex (Sheaf K AddCommGrpCat.{w}))
variable (z : Topos.GlobalPoint (underlyingSetSheaf E.X₃))
variable (z' : Topos.GlobalPoint (underlyingSetSheaf E'.X₃))
variable (q : E.X₂ ⟶ (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj E'.X₂)
variable (hq : ∀ (U : Cᵒᵖ) (t : E.X₂.obj.obj U),
  E.g.hom.app U t = z.hom.app U PUnit.unit →
    E'.g.hom.app (F.op.obj U) (q.hom.app U t) = z'.hom.app (F.op.obj U) PUnit.unit)

/-- The literal middle-sheaf map restricted to the existing extension fibre subtypes. -/
def extensionFiberCarrierMap : extensionFiberSheaf E z ⟶
    (F.sheafPushforwardContinuous (Type w) J K).obj (extensionFiberSheaf E' z') where
  hom := {
    app U := TypeCat.ofHom fun t => ⟨q.hom.app U t.val, hq U t.val t.property⟩
    naturality {U V} g := by
      apply ConcreteCategory.hom_ext
      intro t
      apply Subtype.ext
      exact ConcreteCategory.congr_hom (q.hom.naturality g) t.val }

/-- Restricting to fibres retains the original middle map on each underlying section. -/
@[simp] theorem extensionFiberCarrierMap_apply (U : Cᵒᵖ)
    (t : (extensionFiberSheaf E z).obj.obj U) :
    ((extensionFiberCarrierMap F E E' z z' q hq).hom.app U t).val = q.hom.app U t.val := rfl

variable [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable (hE : E.ShortExact) (hE' : E'.ShortExact)
variable (r : E.X₁ ⟶ (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj E'.X₁)
variable (hi : ∀ (U : Cᵒᵖ) (a : E.X₁.obj.obj U),
  q.hom.app U (E.f.hom.app U a) = E'.f.hom.app (F.op.obj U) (r.hom.app U a))

/-- The actual middle and coefficient squares give the existing adjoint torsor map
on the original extension fibres. Its carrier is the same literal subtype map. -/
def extensionFiberAdjointHom :
    Torsor.AdjointHom F r (extensionFiberTorsor E z hE) (extensionFiberTorsor E' z' hE') where
  map := extensionFiberCarrierMap F E E' z z' q hq
  equivariant U a t := by
    apply Subtype.ext
    change q.hom.app U (E.f.hom.app U a + (show E.X₂.obj.obj U from t.val)) =
      E'.f.hom.app (F.op.obj U) (r.hom.app U a) +
        (show E'.X₂.obj.obj (F.op.obj U) from q.hom.app U t.val)
    rw [map_add]
    exact congrArg (fun b : E'.X₂.obj.obj (F.op.obj U) =>
      b + (show E'.X₂.obj.obj (F.op.obj U) from q.hom.app U t.val)) (hi U a)

end AdjointFibres

end CategoryTheory.Sheaf
