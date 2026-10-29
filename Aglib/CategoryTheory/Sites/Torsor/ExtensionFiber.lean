/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsor.Basic
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone

/-! # Actual fibres of abelian sheaf extensions over intrinsic global elements

The original fibre subtype is the carrier throughout. Its pullback universal
property is proved on that carrier. Short exactness gives the original additive
kernel action and local nonemptiness, without a terminal site object or points.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf

universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

private theorem terminalSheaf_component_ext (U : Cᵒᵖ)
    (x y : (Topos.terminalSheaf J : Sheaf J (Type w)).obj.obj U) : x = y := by
  change (PUnit : Type w) at x y
  exact Subsingleton.elim x y

private theorem globalPoint_naturality {F : Sheaf J AddCommGrpCat.{w}}
    (z : Topos.GlobalPoint (underlyingSetSheaf F)) {U V : Cᵒᵖ} (f : U ⟶ V) :
    F.obj.map f (z.hom.app U PUnit.unit) = z.hom.app V PUnit.unit := by
  exact (ConcreteCategory.congr_hom (z.hom.naturality f) PUnit.unit).symm

variable (S : ShortComplex (Sheaf J AddCommGrpCat.{w}))
variable (z : Topos.GlobalPoint (underlyingSetSheaf S.X₃))

/-- Sections of the middle sheaf lying over the specified quotient section. -/
def extensionFiberSubfunctor : Subfunctor (underlyingSetSheaf S.X₂).obj where
  obj U := {s | S.g.hom.app U s = z.hom.app U PUnit.unit}
  map {U V} f s hs := by
    change S.g.hom.app V (S.X₂.obj.map f s) = z.hom.app V PUnit.unit
    have hn := ConcreteCategory.congr_hom (S.g.hom.naturality f) s
    change S.g.hom.app V (S.X₂.obj.map f s) = S.X₃.obj.map f (S.g.hom.app U s) at hn
    rw [hn, hs, globalPoint_naturality]

/-- A fibre condition is local because the quotient is a sheaf. -/
theorem extensionFiber_isSheaf :
    Presheaf.IsSheaf J (extensionFiberSubfunctor S z).toFunctor := by
  rw [isSheaf_iff_isSheaf_of_type]
  apply (Subfunctor.isSheaf_iff (J := J) (extensionFiberSubfunctor S z)
    ((isSheaf_iff_isSheaf_of_type _ _).mp (underlyingSetSheaf S.X₂).property)).2
  intro U s hs
  change S.g.hom.app U s = z.hom.app U PUnit.unit
  apply (((isSheaf_iff_isSheaf_of_type _ _).mp
    (underlyingSetSheaf S.X₃).property).isSeparated _ hs).ext
  intro V f hf
  change S.X₃.obj.map f.op (S.g.hom.app U s) = S.X₃.obj.map f.op (z.hom.app U PUnit.unit)
  rw [globalPoint_naturality]
  have hn := ConcreteCategory.congr_hom (S.g.hom.naturality f.op) s
  change S.g.hom.app (op V) (S.X₂.obj.map f.op s) =
    S.X₃.obj.map f.op (S.g.hom.app U s) at hn
  rw [← hn]
  exact hf

/-- The actual sheaf-theoretic fibre. -/
def extensionFiberSheaf : Sheaf J (Type w) :=
  ⟨(extensionFiberSubfunctor S z).toFunctor, extensionFiber_isSheaf S z⟩

/-- The literal subtype inclusion into the original middle sheaf. -/
def extensionFiberInclusion : extensionFiberSheaf S z ⟶ underlyingSetSheaf S.X₂ :=
  ⟨{ app _ := TypeCat.ofHom Subtype.val
     naturality {_ _} _ := rfl }⟩

/-- The square of the original fibre carrier over the intrinsic global element. -/
def extensionFiberPullbackCone :
    PullbackCone ((sheafCompose J (forget AddCommGrpCat.{w})).map S.g) z :=
  PullbackCone.mk (extensionFiberInclusion S z)
    ((Topos.terminalSheafIsTerminal J).from (extensionFiberSheaf S z)) (by
      ext U t
      exact t.property.trans (congrArg (fun x => z.hom.app U x)
        (terminalSheaf_component_ext U PUnit.unit
          (((Topos.terminalSheafIsTerminal J).from (extensionFiberSheaf S z)).hom.app U t))))

/-- The actual fibre subtype satisfies the pullback universal property. -/
def extensionFiberPullbackIsLimit : IsLimit (extensionFiberPullbackCone S z) := by
  let lift (s : PullbackCone ((sheafCompose J (forget AddCommGrpCat.{w})).map S.g) z) :
      s.pt ⟶ extensionFiberSheaf S z :=
    ⟨{ app U := TypeCat.ofHom (fun x => ⟨s.fst.hom.app U x, by
         have h := congrArg
           (fun q : s.pt ⟶ underlyingSetSheaf S.X₃ => q.hom.app U x) s.condition
         exact h.trans (congrArg (fun t => z.hom.app U t)
           (terminalSheaf_component_ext U (s.snd.hom.app U x) PUnit.unit))⟩)
       naturality {U V} f := by
         ext x
         apply Subtype.ext
         exact ConcreteCategory.congr_hom (s.fst.hom.naturality f) x }⟩
  refine PullbackCone.IsLimit.mk _ lift ?_ ?_ ?_
  · intro s
    ext U x
    rfl
  · intro s
    exact (Topos.terminalSheafIsTerminal J).hom_ext _ _
  · intro s m hm _
    ext U x
    apply Subtype.ext
    exact congrArg (fun q : s.pt ⟶ underlyingSetSheaf S.X₂ => q.hom.app U x) hm

variable [HasSheafify J AddCommGrpCat.{w}]

/-- Evaluation preserves the actual kernel in a short exact sheaf sequence. -/
def extensionSectionKernel (hS : S.ShortExact) (U : Cᵒᵖ) :
    IsLimit (KernelFork.ofι (S.f.hom.app U)
      (show S.f.hom.app U ≫ S.g.hom.app U = 0 from
        congrArg (fun q => q.hom.app U) S.zero)) := by
  exact KernelFork.mapIsLimit _ hS.fIsKernel
    (sheafToPresheaf J AddCommGrpCat.{w} ⋙
      (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{w}).obj U)

variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The fibre of a short exact abelian sheaf sequence over a global section
is a genuine torsor, with action by addition of the kernel inclusion. -/
def extensionFiberTorsor (hS : S.ShortExact) : Torsor S.X₁ where
  carrier := extensionFiberSheaf S z
  action U a t := ⟨S.f.hom.app U a + (show S.X₂.obj.obj U from t.val), by
    change S.g.hom.app U (S.f.hom.app U a + (show S.X₂.obj.obj U from t.val)) = _
    rw [map_add]
    have hz : S.g.hom.app U (S.f.hom.app U a) = 0 :=
      congrArg (fun q => q.hom.app U a) S.zero
    rw [hz, zero_add]
    exact t.property⟩
  zero_action U t := by apply Subtype.ext; simp
  add_action U a b t := by apply Subtype.ext; simp [add_assoc]
  naturality {U V} f a t := by
    apply Subtype.ext
    change S.X₂.obj.map f (S.f.hom.app U a + (show S.X₂.obj.obj U from t.val)) =
      S.f.hom.app V (S.X₁.obj.map f a) + S.X₂.obj.map f (show S.X₂.obj.obj U from t.val)
    rw [map_add]
    exact congrArg (· + S.X₂.obj.map f (show S.X₂.obj.obj U from t.val))
      (ConcreteCategory.congr_hom (S.f.hom.naturality f) a).symm
  unique_transport U s t := by
    let SU : ShortComplex AddCommGrpCat.{w} := ShortComplex.mk
      (S.f.hom.app U) (S.g.hom.app U)
      (congrArg (fun q => q.hom.app U) S.zero)
    have hex : SU.Exact := SU.exact_of_f_is_kernel (extensionSectionKernel S hS U)
    obtain ⟨a, ha⟩ := (ShortComplex.ab_exact_iff SU).mp hex ((show S.X₂.obj.obj U from t.val) -
      (show S.X₂.obj.obj U from s.val)) (by
      change S.g.hom.app U ((show S.X₂.obj.obj U from t.val) - (show S.X₂.obj.obj U from s.val)) = 0
      rw [map_sub, s.property, t.property, sub_self])
    have hi : Function.Injective (S.f.hom.app U) := by
      let : Mono (S.f.hom.app U) := mono_of_isLimit_fork (extensionSectionKernel S hS U)
      exact (AddCommGrpCat.mono_iff_injective _).mp inferInstance
    refine ⟨a, ?_, ?_⟩
    · apply Subtype.ext
      change S.f.hom.app U a + (show S.X₂.obj.obj U from s.val) = t.val
      change S.f.hom.app U a = (show S.X₂.obj.obj U from t.val) - (show S.X₂.obj.obj U from
        s.val) at ha
      exact eq_sub_iff_add_eq.mp ha
    · intro b hb
      apply hi
      have hb' := congrArg Subtype.val hb
      change S.f.hom.app U b + (show S.X₂.obj.obj U from s.val) = t.val at hb'
      exact (eq_sub_iff_add_eq.mpr hb').trans ha.symm
  locally_nonempty U := by
    let : Sheaf.IsLocallySurjective S.g :=
      (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{w} S.g).mpr hS.epi_g
    refine J.superset_covering ?_
      (Presheaf.imageSieve_mem J S.g.hom
        (z.hom.app (op U) PUnit.unit))
    rintro V f ⟨t, ht⟩
    exact ⟨⟨t, ht.trans (globalPoint_naturality z f.op)⟩⟩

end CategoryTheory.Sheaf
