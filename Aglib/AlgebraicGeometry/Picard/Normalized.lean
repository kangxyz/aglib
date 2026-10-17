/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Presheaf

/-!
# The normalized Picard presheaf of a morphism with a section

Let `p : X ⟶ S` be a morphism of schemes and `o : S ⟶ X` a section, `o ≫ p = 𝟙 S`.
For every `S`-scheme `T`, the section induces `originSection p o ho T : T ⟶ X ×_S T`,
the graph of `T ⟶ S ⟶ X`. Pullback along these sections is the natural
transformation `originRestriction p o ho : Pic(X ×_S T) ⟶ Pic(T)`, and it is a
retraction of the base pullback (`basePullback_originRestriction`).

`normalizedPicardFunctor p o ho` is the kernel presheaf
`T ↦ ker(o_T^* : Pic(X ×_S T) → Pic(T))`. The projection `L ↦ L - pr₂^*(o_T^* L)`
identifies the relative Picard functor `P_{X/S}` with it:
`quotientNormalizedIso p o ho : relativePicardFunctor p ≅ normalizedPicardFunctor p o ho`,
whose inverse is the inclusion of the kernel followed by the quotient map
(`quotientNormalizedIso_inv`). This is the elementary split of
`Pic(T) → Pic(X ×_S T) → P_{X/S}(T) → 0` by `o_T^*`; no hypothesis on `p` and no
rigidification are used, and all test schemes are allowed.

The additive splitting lemma `Split.quotientEquiv` is the source construction
`R5Lab.AlgebraicGeometry.Curves.RelativePicard.Split`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.RelativePicard

open Scheme.Modules.Invertible Scheme.Modules.Invertible.PullbackTensor.Local

universe u

namespace Split

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]
variable (i : B →+ A) (r : A →+ B) (h : r.comp i = AddMonoidHom.id B)

include h in
theorem retraction (b : B) : r (i b) = b := DFunLike.congr_fun h b

/-- The projection `a ↦ a - i (r a)` onto the kernel of the retraction `r`. -/
def normalize : A →+ r.ker where
  toFun a := ⟨a - i (r a), by
    simp only [AddMonoidHom.mem_ker, map_sub, retraction i r h, sub_self]⟩
  map_zero' := by
    apply Subtype.ext
    simp
  map_add' a b := by
    apply Subtype.ext
    change a + b - i (r (a + b)) = (a - i (r a)) + (b - i (r b))
    simp only [map_add]
    abel

@[simp]
theorem normalize_val (a : A) : (normalize i r h a).val = a - i (r a) := rfl

@[simp]
theorem normalize_on_ker (a : r.ker) : normalize i r h a.val = a := by
  apply Subtype.ext
  change a.val - i (r a.val) = a.val
  rw [show r a.val = 0 from a.property, map_zero, sub_zero]

theorem normalize_ker : (normalize i r h).ker = i.range := by
  ext a
  constructor
  · intro ha
    have hz : a - i (r a) = 0 := congrArg Subtype.val ha
    exact ⟨r a, (sub_eq_zero.mp hz).symm⟩
  · rintro ⟨b, rfl⟩
    apply Subtype.ext
    change i b - i (r (i b)) = 0
    rw [retraction i r h, sub_self]

/-- For a split injection `i` with retraction `r`, the cokernel of `i` is the kernel of
`r`, through `a ↦ a - i (r a)`. -/
def quotientEquiv : A ⧸ i.range ≃+ r.ker :=
  (QuotientAddGroup.quotientAddEquivOfEq (normalize_ker i r h).symm).trans
    (QuotientAddGroup.quotientKerEquivOfRightInverse (normalize i r h) Subtype.val
      (normalize_on_ker i r h))

@[simp]
theorem quotientEquiv_mk (a : A) :
    quotientEquiv i r h (QuotientAddGroup.mk a) = normalize i r h a := rfl

end Split

variable {S X : Scheme.{u}} (p : X ⟶ S) (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)

/-- The section `T ⟶ X ×_S T` induced by the section `o` of `p`: the graph of
`T ⟶ S ⟶ X`. -/
def originSection (T : Over S) : T.left ⟶ pullback p T.hom :=
  pullback.lift (T.hom ≫ o) (𝟙 T.left) (by simp [ho])

@[reassoc (attr := simp)]
theorem originSection_fst (T : Over S) :
    originSection p o ho T ≫ pullback.fst p T.hom = T.hom ≫ o :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem originSection_snd (T : Over S) :
    originSection p o ho T ≫ pullback.snd p T.hom = 𝟙 _ :=
  pullback.lift_snd _ _ _

-- `pullback.map` is a `pullback.lift` carrying its own `HasPullback` instances; relaxing
-- instance transparency lets `pullback.lift_fst`/`pullback.lift_snd` match them, as in
-- Mathlib's `pullback.map_comp` and `pullback.map_id`.
set_option backward.isDefEq.respectTransparency false in
/-- The origin sections, natural in the `S`-scheme `T`. -/
@[simps]
def originSectionNatTrans : Over.forget S ⟶ familyScheme p where
  app T := originSection p o ho T
  naturality T T' f := by
    apply pullback.hom_ext <;> simp

-- `pullback.map` is a `pullback.lift` carrying its own `HasPullback` instances; relaxing
-- instance transparency lets `pullback.lift_fst`/`pullback.lift_snd` match them, as in
-- Mathlib's `pullback.map_comp` and `pullback.map_id`.
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem originSectionNatTrans_familyProjection :
    originSectionNatTrans p o ho ≫ familyProjection p = 𝟙 (Over.forget S) := by
  ext T
  simp

/-- Restriction of line-bundle classes along the origin sections,
`o_T^* : Pic(X ×_S T) ⟶ Pic(T)`. -/
def originRestriction : familyPicardFunctor p ⟶ basePicardFunctor S :=
  Functor.whiskerRight (NatTrans.op (originSectionNatTrans p o ho)) picardFunctor

theorem originRestriction_app_apply (T : (Over S)ᵒᵖ) (a : PicardGroup (pullback p T.unop.hom)) :
    ((originRestriction p o ho).app T).hom a = pullbackClass (originSection p o ho T.unop) a :=
  rfl

-- `rw` with `pullbackClass_comp` must identify `(familyScheme p).obj T` with
-- `pullback p T.hom`, which needs relaxed instance transparency.
set_option backward.isDefEq.respectTransparency false in
/-- Origin restriction is a retraction of the base pullback. -/
@[reassoc (attr := simp)]
theorem basePullback_originRestriction :
    basePullback p ≫ originRestriction p o ho = 𝟙 (basePicardFunctor S) := by
  ext T a
  change pullbackClass (originSection p o ho T.unop)
    (pullbackClass (pullback.snd p T.unop.hom) a) = a
  rw [← pullbackClass_comp, originSection_snd, pullbackClass_id]

theorem originRestriction_comp_basePullback (T : (Over S)ᵒᵖ) :
    ((originRestriction p o ho).app T).hom.comp ((basePullback p).app T).hom =
      AddMonoidHom.id _ := by
  ext a
  exact congrArg (fun φ => (φ.app T).hom a) (basePullback_originRestriction p o ho)

include o ho in
/-- With a section, `Pic(T) ⟶ Pic(X ×_S T)` is injective. -/
theorem basePullback_app_injective (T : (Over S)ᵒᵖ) :
    Function.Injective ((basePullback p).app T).hom :=
  Function.LeftInverse.injective (g := ((originRestriction p o ho).app T).hom)
    (DFunLike.congr_fun (originRestriction_comp_basePullback p o ho T))

/-- The classes on `X ×_S T` whose restriction along the origin section is trivial. -/
abbrev normalizedSubgroup (T : (Over S)ᵒᵖ) : AddSubgroup ((familyPicardFunctor p).obj T) :=
  ((originRestriction p o ho).app T).hom.ker

theorem map_mem_normalizedSubgroup {T T' : (Over S)ᵒᵖ} (f : T ⟶ T')
    {a : (familyPicardFunctor p).obj T} (ha : a ∈ normalizedSubgroup p o ho T) :
    ((familyPicardFunctor p).map f).hom a ∈ normalizedSubgroup p o ho T' := by
  rw [AddMonoidHom.mem_ker] at ha ⊢
  have h := congrArg (fun φ => φ.hom a) ((originRestriction p o ho).naturality f)
  refine h.trans ?_
  change ((basePicardFunctor S).map f).hom (((originRestriction p o ho).app T).hom a) = 0
  exact (congrArg ((basePicardFunctor S).map f).hom ha).trans (map_zero _)

/-- The normalized Picard presheaf `T ↦ ker(o_T^* : Pic(X ×_S T) → Pic(T))`. -/
def normalizedPicardFunctor : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj T := AddCommGrpCat.of (normalizedSubgroup p o ho T)
  map f := AddCommGrpCat.ofHom
    ((((familyPicardFunctor p).map f).hom.comp (normalizedSubgroup p o ho _).subtype).codRestrict
      _ fun a => map_mem_normalizedSubgroup p o ho f a.2)
  map_id T := by
    ext a
    exact congrArg (fun φ => φ.hom a.1) ((familyPicardFunctor p).map_id T)
  map_comp f g := by
    ext a
    exact congrArg (fun φ => φ.hom a.1) ((familyPicardFunctor p).map_comp f g)

theorem normalizedPicardFunctor_map_apply_val {T T' : (Over S)ᵒᵖ} (f : T ⟶ T')
    (a : normalizedSubgroup p o ho T) :
    (((normalizedPicardFunctor p o ho).map f).hom a).val =
      ((familyPicardFunctor p).map f).hom a.val := rfl

/-- The inclusion of the normalized presheaf into the family Picard presheaf. -/
def normalizedInclusion : normalizedPicardFunctor p o ho ⟶ familyPicardFunctor p where
  app T := AddCommGrpCat.ofHom (normalizedSubgroup p o ho T).subtype
  naturality T T' f := by
    ext a
    rfl

theorem normalizedInclusion_app_injective (T : (Over S)ᵒᵖ) :
    Function.Injective ((normalizedInclusion p o ho).app T).hom :=
  Subtype.val_injective

/-- The pointwise identification `P_{X/S}(T) ≃+ ker(o_T^*)`, `[L] ↦ L - pr₂^*(o_T^* L)`. -/
def quotientNormalizedEquiv (T : (Over S)ᵒᵖ) :
    (familyPicardFunctor p).obj T ⧸ baseImage p T ≃+ normalizedSubgroup p o ho T :=
  Split.quotientEquiv ((basePullback p).app T).hom ((originRestriction p o ho).app T).hom
    (originRestriction_comp_basePullback p o ho T)

theorem quotientNormalizedEquiv_mk_val (T : (Over S)ᵒᵖ) (a : (familyPicardFunctor p).obj T) :
    (quotientNormalizedEquiv p o ho T (QuotientAddGroup.mk a)).val =
      a - ((basePullback p).app T).hom (((originRestriction p o ho).app T).hom a) := rfl

theorem quotientNormalizedEquiv_symm_apply (T : (Over S)ᵒᵖ) (a : normalizedSubgroup p o ho T) :
    (quotientNormalizedEquiv p o ho T).symm a = QuotientAddGroup.mk a.val := by
  apply (quotientNormalizedEquiv p o ho T).injective
  rw [AddEquiv.apply_symm_apply]
  exact (Split.normalize_on_ker _ _ (originRestriction_comp_basePullback p o ho T) a).symm

/-- The relative Picard functor is isomorphic to the normalized Picard presheaf. -/
def quotientNormalizedIso : relativePicardFunctor p ≅ normalizedPicardFunctor p o ho :=
  NatIso.ofComponents (fun T => (quotientNormalizedEquiv p o ho T).toAddCommGrpIso) (by
    intro T T' f
    ext x
    induction x using QuotientAddGroup.induction_on with
    | H a =>
      change ↑((familyPicardFunctor p).obj T) at a
      apply Subtype.ext
      change ((familyPicardFunctor p).map f).hom a -
          ((basePullback p).app T').hom (((originRestriction p o ho).app T').hom
            (((familyPicardFunctor p).map f).hom a)) =
        ((familyPicardFunctor p).map f).hom
          (a - ((basePullback p).app T).hom (((originRestriction p o ho).app T).hom a))
      rw [map_sub]
      congr 1
      have hr := congrArg (fun φ => φ.hom a) ((originRestriction p o ho).naturality f)
      have hb := congrArg (fun φ => φ.hom (((originRestriction p o ho).app T).hom a))
        ((basePullback p).naturality f)
      exact (congrArg ((basePullback p).app T').hom hr).trans hb)

/-- The inverse of `quotientNormalizedIso` is the inclusion of the kernel followed by the
quotient map. -/
theorem quotientNormalizedIso_inv :
    (quotientNormalizedIso p o ho).inv = normalizedInclusion p o ho ≫ quotientProjection p := by
  ext T a
  exact quotientNormalizedEquiv_symm_apply p o ho T a

theorem quotientNormalizedIso_hom_app_mk_val (T : (Over S)ᵒᵖ) (a : (familyPicardFunctor p).obj T) :
    (((quotientNormalizedIso p o ho).hom.app T).hom (QuotientAddGroup.mk a)).val =
      a - ((basePullback p).app T).hom (((originRestriction p o ho).app T).hom a) := rfl

end AlgebraicGeometry.Scheme.RelativePicard
