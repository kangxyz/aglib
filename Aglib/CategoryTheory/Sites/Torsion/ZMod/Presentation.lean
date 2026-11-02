/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsion.FinitePresentation.FiniteCover
public import Aglib.CategoryTheory.Sites.Torsion.ZMod.Sheaf
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Presentable.Finite
public import Mathlib.CategoryTheory.Presentable.StrongGenerator
public import Mathlib.CategoryTheory.Sites.Continuous

/-! # Original bounded coefficients and their site presentations

The native full subcategory of sheaves killed by a fixed scalar retains its
original colimits and free scalar-quotient generators. Their maps represent
unchanged sections. The original binary-cover gluing proves a pushout of
these generators, and restriction to a detecting subsite proves that its
original generators form a strong generator. Compactness and density remain
the native presentability and cardinal-closure constructions.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory.Limits Opposite
open CategoryTheory.Sheaf.TorsionFinitePresentation

namespace CategoryTheory.TorsionZMod.Presentation

universe u v a b w w'

attribute [local instance] Cardinal.fact_isRegular_aleph0

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (n : ℕ)

/-- The native full category defined by the literal common scalar equation. -/
abbrev Coefficient :=
  (killedSheaves.{u, v, max u v} J n :
    ObjectProperty (Sheaf J AddCommGrpCat.{max u v})).FullSubcategory

/-- The original sheaf and every original coefficient map are retained. -/
abbrev inclusion : Coefficient J n ⥤ Sheaf J AddCommGrpCat.{max u v} :=
  (killedSheaves J n).ι

/-- Scalar naturality closes the actual killed-sheaf category under original colimits. -/
instance killedSheaves_closedColimits (I : Type a) [Category.{b} I] :
    (killedSheaves.{u, v, w} J n :
      ObjectProperty (Sheaf J AddCommGrpCat.{w})).IsClosedUnderColimitsOfShape I where
  colimitsOfShape_le F hF := by
    obtain ⟨p⟩ := hF
    change n • 𝟙 F = 0
    apply p.isColimit.hom_ext
    intro i
    calc
      p.ι.app i ≫ (n • 𝟙 F) = (n • 𝟙 (p.diag.obj i)) ≫ p.ι.app i := by simp
      _ = 0 := by rw [p.prop_diag_obj i, zero_comp]
      _ = p.ι.app i ≫ 0 := by simp

variable [HasSheafify J AddCommGrpCat.{max u v}]

/-- Bounded coefficients have colimits at the original standard value/index size. -/
instance coefficient_hasColimits :
    HasColimitsOfSize.{max u v, max u v} (Coefficient J n) where
  has_colimits_of_shape _I _ := inferInstance

/-- Inclusion preserves these original colimits without replacing their cocones. -/
instance inclusion_preservesColimits :
    PreservesColimitsOfSize.{max u v, max u v} (inclusion J n) where
  preservesColimitsOfShape {_I} := inferInstance

/-- The original free scalar quotient, with its actual annihilation proof. -/
def free (U : C) : Coefficient J n :=
  ⟨freeZModRepresentable.{u} J n U, nsmul_id_freeZModRepresentable J n U⟩

/-- Maps from the original free scalar quotient are the original sheaf sections. -/
def sectionsEquiv (U : C) (F : Coefficient J n) :
    (free J n U ⟶ F) ≃ F.obj.obj.obj (op U) where
  toFun a := (freeZModSectionsEquiv J n U F.obj a.hom).val
  invFun s := ObjectProperty.homMk
    ((freeZModSectionsEquiv J n U F.obj).symm
      ⟨s, sheafSectionsKilled J n F.obj F.property (op U) s⟩)
  left_inv a := by
    apply ObjectProperty.hom_ext
    exact (freeZModSectionsEquiv J n U F.obj).symm_apply_apply a.hom
  right_inv s := congrArg Subtype.val
    ((freeZModSectionsEquiv J n U F.obj).apply_symm_apply
      ⟨s, sheafSectionsKilled J n F.obj F.property (op U) s⟩)

/-- The representing equivalence retains every original coefficient map. -/
theorem sectionsEquiv_naturality (U : C) {F G : Coefficient J n}
    (a : free J n U ⟶ F) (q : F ⟶ G) :
    sectionsEquiv J n U G (a ≫ q) = q.hom.hom.app (op U) (sectionsEquiv J n U F a) :=
  freeZModSectionsEquiv_naturality J n U a.hom q.hom

/-- The inverse equivalence retains the action on the same original section. -/
theorem sectionsEquiv_symm_naturality (U : C) {F G : Coefficient J n}
    (s : F.obj.obj.obj (op U)) (q : F ⟶ G) :
    sectionsEquiv J n U G ((sectionsEquiv J n U F).symm s ≫ q) =
      q.hom.hom.app (op U) s :=
  (sectionsEquiv_naturality J n U _ q).trans
    (congrArg (fun z => q.hom.hom.app (op U) z)
      ((sectionsEquiv J n U F).apply_symm_apply s))

/-- Full inclusion identifies the unchanged native Hom functors. -/
def homInclusionIso (U : C) :
    coyoneda.obj (op (free J n U)) ≅
      inclusion J n ⋙ coyoneda.obj (op (freeZModRepresentable.{u} J n U)) :=
  NatIso.ofComponents (fun F => ((killedSheaves J n).fullyFaithfulι.homEquiv).toIso)
    (fun q => by ext a; rfl)

/-- Ambient compactness transfers along the unchanged full coefficient inclusion. -/
theorem free_isFinitelyPresentable (U : C)
    (hU : IsFinitelyPresentable.{max u v} (freeZModRepresentable.{u} J n U)) :
    IsFinitelyPresentable.{max u v} (free J n U) := by
  have := hU
  exact Functor.isCardinalAccessible_of_natIso (homInclusionIso J n U).symm
    Cardinal.aleph0.{max u v}

/-- Original free quotient maps, inside the native killed coefficient category. -/
def coefficientFreeFunctor : C ⥤ Coefficient J n where
  obj U := free J n U
  map f := ObjectProperty.homMk (FiniteCover.freeMap J n f)
  map_id U := by
    apply ObjectProperty.hom_ext
    exact FiniteCover.freeMap_id J n U
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact FiniteCover.freeMap_comp J n f g

/-- The inclusion retains the original generator functor literally. -/
theorem coefficientFreeFunctor_inclusion :
    coefficientFreeFunctor J n ⋙ inclusion J n = FiniteCover.freeFunctor.{u} J n := rfl

/-- Original bounded free maps evaluate to original restriction of sections. -/
theorem sections_restriction {U V : C} (f : U ⟶ V) (F : Coefficient J n)
    (b : free J n V ⟶ F) :
    sectionsEquiv J n U F ((coefficientFreeFunctor J n).map f ≫ b) =
      F.obj.obj.map f.op (sectionsEquiv J n V F b) :=
  FiniteCover.sections_naturality_left J n f F.obj b.hom

variable (sq : Square C) [Mono sq.f₂₄] [Mono sq.f₃₄]
  (hp : sq.IsPullback) (hcover : Sieve.ofTwoArrows sq.f₂₄ sq.f₃₄ ∈ J sq.X₄)

/-- The original free mod-n square as an actual square of native bounded coefficients. -/
def coefficientSquare : Square (Coefficient J n) :=
  sq.map (coefficientFreeFunctor J n)

include hp hcover in
/-- Original binary-cover section amalgamation proves the actual bounded-generator pushout. -/
theorem coefficientSquare_isPushout : (coefficientSquare J n sq).IsPushout := by
  let F := coefficientFreeFunctor J n
  let E₀ (s : PushoutCocone (F.map sq.f₁₂) (F.map sq.f₁₃)) :=
    sectionsEquiv J n sq.X₂ s.pt s.inl
  let E₁ (s : PushoutCocone (F.map sq.f₁₂) (F.map sq.f₁₃)) :=
    sectionsEquiv J n sq.X₃ s.pt s.inr
  have he (s : PushoutCocone (F.map sq.f₁₂) (F.map sq.f₁₃)) :
      s.pt.obj.obj.map sq.f₁₂.op (E₀ s) = s.pt.obj.obj.map sq.f₁₃.op (E₁ s) :=
    (sections_restriction J n sq.f₁₂ s.pt s.inl).symm.trans
      ((congrArg (sectionsEquiv J n sq.X₁ s.pt) s.condition).trans
        (sections_restriction J n sq.f₁₃ s.pt s.inr))
  let t (s : PushoutCocone (F.map sq.f₁₂) (F.map sq.f₁₃)) :=
    FiniteCover.glue.{u} J sq hp hcover s.pt.obj (E₀ s) (E₁ s) (he s)
  let d (s : PushoutCocone (F.map sq.f₁₂) (F.map sq.f₁₃)) : F.obj sq.X₄ ⟶ s.pt :=
    (sectionsEquiv J n sq.X₄ s.pt).symm (t s)
  have hd (s : PushoutCocone (F.map sq.f₁₂) (F.map sq.f₁₃)) :
      sectionsEquiv J n sq.X₄ s.pt (d s) = t s :=
    (sectionsEquiv J n sq.X₄ s.pt).apply_symm_apply (t s)
  have h₀ (s : PushoutCocone (F.map sq.f₁₂) (F.map sq.f₁₃)) : F.map sq.f₂₄ ≫ d s = s.inl := by
    apply (sectionsEquiv J n sq.X₂ s.pt).injective
    rw [sections_restriction, hd]
    exact FiniteCover.glue_left.{u} J sq hp hcover s.pt.obj (E₀ s) (E₁ s) (he s)
  have h₁ (s : PushoutCocone (F.map sq.f₁₂) (F.map sq.f₁₃)) : F.map sq.f₃₄ ≫ d s = s.inr := by
    apply (sectionsEquiv J n sq.X₃ s.pt).injective
    rw [sections_restriction, hd]
    exact FiniteCover.glue_right.{u} J sq hp hcover s.pt.obj (E₀ s) (E₁ s) (he s)
  apply Square.IsPushout.mk
  refine PushoutCocone.IsColimit.mk _ d h₀ h₁ ?_
  intro s m hm₀ hm₁
  apply (sectionsEquiv J n sq.X₄ s.pt).injective
  apply FiniteCover.sections_ext.{u} J sq hp hcover s.pt.obj
  · exact (sections_restriction J n sq.f₂₄ s.pt m).symm.trans
      ((congrArg (sectionsEquiv J n sq.X₂ s.pt) hm₀).trans
        ((congrArg (sectionsEquiv J n sq.X₂ s.pt) (h₀ s)).symm.trans
          (sections_restriction J n sq.f₂₄ s.pt (d s))))
  · exact (sections_restriction J n sq.f₃₄ s.pt m).symm.trans
      ((congrArg (sectionsEquiv J n sq.X₃ s.pt) hm₁).trans
        ((congrArg (sectionsEquiv J n sq.X₃ s.pt) (h₁ s)).symm.trans
          (sections_restriction J n sq.f₃₄ s.pt (d s))))


/-- Native density and cardinal closure present the actual finite-colimit stages.
The diagram is the original costructured-arrow diagram, reindexed once by its
native SmallModel; no isomorphic copies of its objects are selected. -/
theorem finiteColimitClosure_filteredGenerator
    (P : ObjectProperty (Coefficient J n)) [ObjectProperty.Small.{max u v} P]
    (hstrong : P.IsStrongGenerator)
    (hpresentable : P ≤ isCardinalPresentable (Coefficient J n) Cardinal.aleph0.{max u v}) :
    (P.colimitsCardinalClosure Cardinal.aleph0.{max u v}).IsCardinalFilteredGenerator
      Cardinal.aleph0.{max u v} := by
  have := hstrong.isDense_colimitsCardinalClosure_ι hpresentable
  have (F : Coefficient J n) : IsCardinalFiltered
      (CostructuredArrow (P.colimitsCardinalClosure Cardinal.aleph0.{max u v}).ι F)
        Cardinal.aleph0.{max u v} := by
    infer_instance
  have hp : P.colimitsCardinalClosure Cardinal.aleph0.{max u v} ≤
      isCardinalPresentable (Coefficient J n) Cardinal.aleph0.{max u v} :=
    ObjectProperty.colimitsCardinalClosure_le_isCardinalPresentable.{max u v,
      max u v, max (u + 1) (v + 1)} P hpresentable
  refine ⟨hp, fun F => ?_⟩
  have : LocallySmall.{max u v} (Coefficient J n) := inferInstance
  have : ObjectProperty.EssentiallySmall.{max u v}
      (P.colimitsCardinalClosure Cardinal.aleph0.{max u v}) := inferInstance
  have : EssentiallySmall.{max u v}
      (P.colimitsCardinalClosure Cardinal.aleph0.{max u v}).FullSubcategory := inferInstance
  let I := CostructuredArrow (P.colimitsCardinalClosure Cardinal.aleph0.{max u v}).ι F
  have : EssentiallySmall.{max u v} I := by
    dsimp only [I]
    infer_instance
  let e : I ≌ SmallModel.{max u v} I := equivSmallModel.{max u v} I
  refine ⟨SmallModel.{max u v} I, inferInstance,
    IsCardinalFiltered.of_equivalence Cardinal.aleph0.{max u v} e, ⟨{
      diag := _
      ι := _
      isColimit :=
        ((P.colimitsCardinalClosure Cardinal.aleph0.{max u v}).ι.denseAt F).whiskerEquivalence
          e.symm
      prop_diag_obj := ?_ }⟩⟩
  intro i
  exact (e.inverse.obj i).left.property

section DetectingSubsite

variable {B : Type a} [Category.{b} B] (K : GrothendieckTopology B) (r : B ⥤ C)
  [r.IsContinuous K J]

/-- The same free generators on the objects of the actual subsite. -/
def generators : ObjectProperty (Coefficient J n) :=
  .ofObj (fun U : B => free J n (r.obj U))

variable [(r.sheafPushforwardContinuous AddCommGrpCat.{max u v} K J).Faithful]

include K in
/-- Sections after faithful native subsite restriction separate original coefficient maps. -/
theorem generators_isSeparating : (generators J n r).IsSeparating := by
  intro F G a b h
  apply ObjectProperty.hom_ext
  apply (r.sheafPushforwardContinuous AddCommGrpCat.{max u v} K J).map_injective
  apply ObjectProperty.hom_ext
  ext U s
  let V := r.obj U.unop
  let z : free J n V ⟶ F := (sectionsEquiv J n V F).symm s
  have hz := h (free J n V) ⟨U.unop⟩ z
  change a.hom.hom.app (op V) s = b.hom.hom.app (op V) s
  exact (sectionsEquiv_symm_naturality J n V s a).symm.trans
    ((congrArg (sectionsEquiv J n V G) hz).trans
      (sectionsEquiv_symm_naturality J n V s b))

variable [(r.sheafPushforwardContinuous AddCommGrpCat.{max u v} K J).ReflectsIsomorphisms]

include K in
/-- Maps from original subsite generators detect every proper original subobject. -/
theorem generators_isStrongGenerator : (generators J n r).IsStrongGenerator := by
  rw [ObjectProperty.isStrongGenerator_iff]
  refine ⟨generators_isSeparating J n K r, ?_⟩
  intro F G a ha h
  have he : IsIso ((r.sheafPushforwardContinuous AddCommGrpCat.{max u v} K J).map a.hom).hom := by
    apply (NatTrans.isIso_iff_isIso_app _).mpr
    intro U
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    refine ⟨?_, ?_⟩
    · intro s t hst
      let V := r.obj U.unop
      apply (sectionsEquiv J n V F).symm.injective
      apply (cancel_mono a).mp
      apply (sectionsEquiv J n V G).injective
      exact (sectionsEquiv_symm_naturality J n V s a).trans
        (hst.trans (sectionsEquiv_symm_naturality J n V t a).symm)
    · intro s
      let V := r.obj U.unop
      obtain ⟨b, hb⟩ := h (free J n V) ⟨U.unop⟩ ((sectionsEquiv J n V G).symm s)
      refine ⟨sectionsEquiv J n V F b, ?_⟩
      exact (sectionsEquiv_naturality J n V b a).symm.trans
        ((congrArg (sectionsEquiv J n V G) hb).trans
          ((sectionsEquiv J n V G).apply_symm_apply s))
  have : IsIso ((sheafToPresheaf K AddCommGrpCat.{max u v}).map
      ((r.sheafPushforwardContinuous AddCommGrpCat.{max u v} K J).map a.hom)) := he
  have : IsIso ((r.sheafPushforwardContinuous AddCommGrpCat.{max u v} K J).map a.hom) :=
    isIso_of_reflects_iso _ (sheafToPresheaf K AddCommGrpCat.{max u v})
  have hi : IsIso a.hom :=
    isIso_of_reflects_iso a.hom (r.sheafPushforwardContinuous AddCommGrpCat.{max u v} K J)
  have : IsIso ((inclusion J n).map a) := hi
  exact isIso_of_reflects_iso a (inclusion J n)

end DetectingSubsite

end CategoryTheory.TorsionZMod.Presentation
