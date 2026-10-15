/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Composition
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
/-!
# Extension-closed full exact subcategories

The exact structure is inherited by testing ambient conflations. Its kernel and
cokernel fields are genuine universal properties. Closure under extensions is
used to keep the required admissible pushouts, pullbacks, and composition
kernels/cokernels inside the subcategory; arbitrary kernels and cokernels are
not assumed to exist.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

namespace CategoryTheory.ExactCategory.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- Closure under the extensions specified by this exact structure. -/
class IsExtensionClosed (P : ObjectProperty C) : Prop where
  prop_middle : ∀ {S : ShortComplex C}, E.conflation S → P S.X₁ → P S.X₃ → P S.X₂

variable (P : ObjectProperty C) [E.IsExtensionClosed P]
include E

lemma prop_biprod {X Y : C} (hX : P X) (hY : P Y) : P (X ⊞ Y) :=
  IsExtensionClosed.prop_middle (E.conflation_biprod_inl_snd X Y) hX hY

lemma extensionClosed_binaryProducts [P.IsClosedUnderIsomorphisms] :
    P.IsClosedUnderBinaryProducts where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    refine P.prop_of_iso ?_ (E.prop_biprod P
      (p.prop_diag_obj (.mk .left)) (p.prop_diag_obj (.mk .right)))
    exact IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit _ _)
      ((IsLimit.postcomposeHomEquiv (diagramIsoPair p.diag) _).2 p.isLimit)

lemma extensionClosed_finiteProducts [P.IsClosedUnderIsomorphisms] [P.ContainsZero] :
    P.IsClosedUnderFiniteProducts := by
  let := E.extensionClosed_binaryProducts P
  exact .mk'

lemma prop_pullback {S : ShortComplex C} (hS : E.conflation S)
    (hX : P S.X₁) {T : C} (hT : P T) (g : T ⟶ S.X₃) [HasPullback S.g g] :
    P (pullback S.g g) :=
  IsExtensionClosed.prop_middle (E.pullbackConflation_mem hS g) hX hT

lemma prop_pushout {S : ShortComplex C} (hS : E.conflation S)
    (hZ : P S.X₃) {T : C} (hT : P T) (g : S.X₁ ⟶ T) [HasPushout S.f g] :
    P (pushout S.f g) :=
  IsExtensionClosed.prop_middle (E.pushoutConflation_mem hS g) hT hZ

end CategoryTheory.ExactCategory.ExactStructure

namespace CategoryTheory.ExactCategory.ExactSubcategory
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C) (P : ObjectProperty C)

/-- A short complex of subcategory objects is a conflation precisely when its
image is one in the ambient exact category. -/
def conflation (S : ShortComplex P.FullSubcategory) : Prop := E.conflation (S.map P.ι)

/-- The inherited conflation has the actual kernel universal property. -/
def kernel (S : ShortComplex P.FullSubcategory) (hS : conflation E P S) :
    IsLimit (KernelFork.ofι S.f S.zero) :=
  isLimitOfReflects P.ι ((KernelFork.isLimitMapConeEquiv _ _).symm (E.kernel _ hS))

/-- The inherited conflation has the actual cokernel universal property. -/
def cokernel (S : ShortComplex P.FullSubcategory) (hS : conflation E P S) :
    IsColimit (CokernelCofork.ofπ S.g S.zero) :=
  isColimitOfReflects P.ι ((CokernelCofork.isColimitMapCoconeEquiv _ _).symm (E.cokernel _ hS))

lemma iso_closed {S T : ShortComplex P.FullSubcategory} (e : S ≅ T)
    (hS : conflation E P S) : conflation E P T :=
  E.iso_closed ((P.ι.mapShortComplex).mapIso e) hS

/-- Admissible maps in the full exact subcategory remember an ambient
cokernel object which still belongs to the subcategory. -/
lemma inflation_iff {X Y : P.FullSubcategory} (i : X ⟶ Y) :
    Conflations.inflation P.FullSubcategory (conflation E P) i ↔
      ∃ (Z : C) (_hZ : P Z) (p : Y.obj ⟶ Z) (h : i.hom ≫ p = 0),
        E.conflation (ShortComplex.mk i.hom p h) := by
  constructor
  · rintro ⟨Z, p, h, hs⟩
    exact ⟨Z.obj, Z.property, p.hom, congrArg (fun f => f.hom) h, hs⟩
  · rintro ⟨Z, hZ, p, h, hs⟩
    exact ⟨⟨Z, hZ⟩, P.homMk p, ObjectProperty.hom_ext _ h, hs⟩

/-- Dual description using an ambient kernel still in the subcategory. -/
lemma deflation_iff {Y Z : P.FullSubcategory} (p : Y ⟶ Z) :
    Conflations.deflation P.FullSubcategory (conflation E P) p ↔
      ∃ (X : C) (_hX : P X) (i : X ⟶ Y.obj) (h : i ≫ p.hom = 0),
        E.conflation (ShortComplex.mk i p.hom h) := by
  constructor
  · rintro ⟨X, i, h, hs⟩
    exact ⟨X.obj, X.property, i.hom, congrArg (fun f => f.hom) h, hs⟩
  · rintro ⟨X, hX, i, h, hs⟩
    exact ⟨⟨X, hX⟩, P.homMk i, ObjectProperty.hom_ext _ h, hs⟩

variable [P.ContainsZero] [P.IsClosedUnderIsomorphisms]

lemma inflation_id (X : P.FullSubcategory) :
    Conflations.inflation P.FullSubcategory (conflation E P) (𝟙 X) := by
  apply (inflation_iff E P _).2
  refine ⟨0, P.prop_zero, 0, by simp, ?_⟩
  apply E.conflation_of_inflation_of_isCokernel (E.inflation_id X.obj)
  exact cokernel.isColimitCoconeZeroCocone (𝟙 X.obj)

lemma deflation_id (X : P.FullSubcategory) :
    Conflations.deflation P.FullSubcategory (conflation E P) (𝟙 X) := by
  apply (deflation_iff E P _).2
  refine ⟨0, P.prop_zero, 0, by simp, ?_⟩
  exact E.conflation_of_isKernel _ (kernel.isLimitConeZeroCone (𝟙 X.obj)) (E.deflation_id _)


variable [E.IsExtensionClosed P]

omit [P.ContainsZero] [P.IsClosedUnderIsomorphisms] in
lemma inflation_comp {X Y Z : P.FullSubcategory} (i : X ⟶ Y) (j : Y ⟶ Z)
    (hi : Conflations.inflation _ (conflation E P) i)
    (hj : Conflations.inflation _ (conflation E P) j) :
    Conflations.inflation _ (conflation E P) (i ≫ j) := by
  obtain ⟨A, hA, p, hp, hS⟩ := (inflation_iff E P i).1 hi
  obtain ⟨B, hB, q, hq, hT⟩ := (inflation_iff E P j).1 hj
  let : HasPushout j.hom p := E.inflation.hasPushout p (E.inflation_of_conflation hT)
  apply (inflation_iff E P _).2
  exact ⟨pushout j.hom p, E.prop_pushout P hT hB hA p, pushout.inl _ _,
    by rw [ObjectProperty.FullSubcategory.comp_hom, Category.assoc,
      pushout.condition, ← Category.assoc, hp, zero_comp],
    E.composite_inflation_conflation hS hT⟩

omit [P.ContainsZero] [P.IsClosedUnderIsomorphisms] in
lemma deflation_comp {X Y Z : P.FullSubcategory} (p : X ⟶ Y) (q : Y ⟶ Z)
    (hp : Conflations.deflation _ (conflation E P) p)
    (hq : Conflations.deflation _ (conflation E P) q) :
    Conflations.deflation _ (conflation E P) (p ≫ q) := by
  obtain ⟨A, hA, i, hi, hS⟩ := (deflation_iff E P p).1 hp
  obtain ⟨B, hB, j, hj, hT⟩ := (deflation_iff E P q).1 hq
  let : HasPullback p.hom j := E.deflation.hasPullback j (E.deflation_of_conflation hS)
  apply (deflation_iff E P _).2
  exact ⟨pullback p.hom j, E.prop_pullback P hS hA hB j, pullback.fst _ _,
    by rw [ObjectProperty.FullSubcategory.comp_hom, ← Category.assoc,
      pullback.condition, Category.assoc, hj, comp_zero],
    E.composite_deflation_conflation hS hT⟩

omit [P.ContainsZero] [P.IsClosedUnderIsomorphisms] in
/-- The required pushout lives in the subcategory because it is an extension
of its new source by the original cokernel. -/
lemma exists_pushout {X Y Z : P.FullSubcategory} (i : X ⟶ Y) (f : X ⟶ Z)
    (hi : Conflations.inflation _ (conflation E P) i) :
    ∃ (W : P.FullSubcategory) (a : Y ⟶ W) (b : Z ⟶ W),
      IsPushout i f a b ∧ Conflations.inflation _ (conflation E P) b := by
  obtain ⟨A, hA, p, hp, hS⟩ := (inflation_iff E P i).1 hi
  let : HasPushout i.hom f.hom := E.inflation.hasPushout f.hom (E.inflation_of_conflation hS)
  let W : P.FullSubcategory := ⟨pushout i.hom f.hom, E.prop_pushout P hS hA Z.property f.hom⟩
  let a : Y ⟶ W := P.homMk (pushout.inl _ _)
  let b : Z ⟶ W := P.homMk (pushout.inr _ _)
  refine ⟨W, a, b, ?_, ?_⟩
  · exact IsPushout.of_map_of_faithful P.ι (IsPushout.of_hasPushout i.hom f.hom)
  · apply (inflation_iff E P b).2
    exact ⟨A, hA, pushout.desc p 0 (by simp [hp]), by simp [b],
      E.pushoutConflation_mem hS f.hom⟩

omit [P.ContainsZero] [P.IsClosedUnderIsomorphisms] in
/-- Dually, the admissible pullback is an extension of the new target by the
original kernel. -/
lemma exists_pullback {X Y Z : P.FullSubcategory} (p : X ⟶ Z) (f : Y ⟶ Z)
    (hp : Conflations.deflation _ (conflation E P) p) :
    ∃ (W : P.FullSubcategory) (a : W ⟶ X) (b : W ⟶ Y),
      IsPullback a b p f ∧ Conflations.deflation _ (conflation E P) b := by
  obtain ⟨A, hA, i, hi, hS⟩ := (deflation_iff E P p).1 hp
  let : HasPullback p.hom f.hom := E.deflation.hasPullback f.hom (E.deflation_of_conflation hS)
  let W : P.FullSubcategory := ⟨pullback p.hom f.hom, E.prop_pullback P hS hA Y.property f.hom⟩
  let a : W ⟶ X := P.homMk (pullback.fst _ _)
  let b : W ⟶ Y := P.homMk (pullback.snd _ _)
  refine ⟨W, a, b, ?_, ?_⟩
  · exact IsPullback.of_map_of_faithful P.ι (IsPullback.of_hasPullback p.hom f.hom)
  · apply (deflation_iff E P b).2
    exact ⟨A, hA, pullback.lift i 0 (by simp [hi]), by simp [b],
      E.pullbackConflation_mem hS f.hom⟩


omit [P.ContainsZero] [P.IsClosedUnderIsomorphisms] [E.IsExtensionClosed P] in
lemma inflation_comp_iso {X Y Z : P.FullSubcategory} {i : X ⟶ Y}
    (hi : Conflations.inflation _ (conflation E P) i) (e : Y ≅ Z) :
    Conflations.inflation _ (conflation E P) (i ≫ e.hom) := by
  obtain ⟨A, p, hp, hS⟩ := hi
  refine ⟨A, e.inv ≫ p, by simpa using hp, ?_⟩
  exact iso_closed E P (S := ShortComplex.mk i p hp) (ShortComplex.isoMk (Iso.refl _) e (Iso.refl _)
    (by simp) (by simp)) hS

omit [P.ContainsZero] [P.IsClosedUnderIsomorphisms] [E.IsExtensionClosed P] in
lemma iso_comp_deflation {X Y Z : P.FullSubcategory} {p : Y ⟶ Z}
    (hp : Conflations.deflation _ (conflation E P) p) (e : X ≅ Y) :
    Conflations.deflation _ (conflation E P) (e.hom ≫ p) := by
  obtain ⟨A, i, hi, hS⟩ := hp
  refine ⟨A, i ≫ e.inv, by simpa using hi, ?_⟩
  exact iso_closed E P (S := ShortComplex.mk i p hi) (ShortComplex.isoMk (Iso.refl _) e.symm
    (Iso.refl _)
    (by simp) (by simp)) hS

omit [P.ContainsZero] [P.IsClosedUnderIsomorphisms] in
lemma inflation_hasPushouts :
    (Conflations.inflation _ (conflation E P)).HasPushouts where
  hasPushout {_ _ _} {_f} _g hf := by
    obtain ⟨W, a, b, hs, _⟩ := exists_pushout E P _ _ hf
    exact hs.hasPushout

omit [P.ContainsZero] [P.IsClosedUnderIsomorphisms] in
lemma deflation_hasPullbacks :
    (Conflations.deflation _ (conflation E P)).HasPullbacks where
  hasPullback {_ _ _} {_f} _g hf := by
    obtain ⟨W, a, b, hs, _⟩ := exists_pullback E P _ _ hf
    exact hs.hasPullback

omit [P.ContainsZero] [P.IsClosedUnderIsomorphisms] in
lemma inflation_cobaseChange :
    (Conflations.inflation _ (conflation E P)).IsStableUnderCobaseChange where
  of_isPushout {A A' B B' f g f' g'} sq hf := by
    obtain ⟨W, a, b, hs, hb⟩ := exists_pushout E P f g hf
    let e := hs.isColimit.coconePointUniqueUpToIso sq.flip.isColimit
    have he : b ≫ e.hom = f' :=
      hs.isColimit.comp_coconePointUniqueUpToIso_hom sq.flip.isColimit WalkingSpan.right
    rw [← he]
    exact inflation_comp_iso E P hb e

omit [P.ContainsZero] [P.IsClosedUnderIsomorphisms] in
lemma deflation_baseChange :
    (Conflations.deflation _ (conflation E P)).IsStableUnderBaseChange where
  of_isPullback {X Y Y' S f g f' g'} sq hg := by
    obtain ⟨W, a, b, hs, hb⟩ := exists_pullback E P g f hg
    let e := sq.isLimit.conePointUniqueUpToIso hs.isLimit
    have he : e.hom ≫ b = g' :=
      sq.isLimit.conePointUniqueUpToIso_hom_comp hs.isLimit WalkingCospan.right
    rw [← he]
    exact iso_comp_deflation E P hb e

variable [P.IsClosedUnderFiniteProducts]

instance subcategoryHasFiniteBiproducts : HasFiniteBiproducts P.FullSubcategory :=
  .of_hasFiniteProducts

/-- The inherited exact structure on an extension-closed full additive
subcategory. Every exact axiom is proved above from the ambient structure. -/
def exactStructure : ExactStructure P.FullSubcategory where
  conflation := conflation E P
  kernel := kernel E P
  cokernel := cokernel E P
  iso_closed := iso_closed E P
  inflation_id := inflation_id E P
  deflation_id := deflation_id E P
  inflation_comp := inflation_comp E P
  deflation_comp := deflation_comp E P
  inflation_hasPushouts := inflation_hasPushouts E P
  inflation_cobaseChange := inflation_cobaseChange E P
  deflation_hasPullbacks := deflation_hasPullbacks E P
  deflation_baseChange := deflation_baseChange E P

/-- The actual full-subcategory inclusion is an additive exact functor. -/
def exactInclusion : ExactFunctor (exactStructure E P) E where
  toFunctor := P.ι
  map_conflation _ hS := hS

/-- Full faithfulness concerns the original inclusion, without any unwarranted
fullness claim about its induced Q-functor. -/
def inclusionFullyFaithful : (exactInclusion E P).toFunctor.FullyFaithful := P.fullyFaithfulι

end CategoryTheory.ExactCategory.ExactSubcategory

namespace CategoryTheory.ExactCategory.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C) (P : ObjectProperty C)
  [E.IsExtensionClosed P] [P.ContainsZero] [P.IsClosedUnderIsomorphisms]

/-- The inherited exact structure with additivity derived automatically from
extension closure. No independent finite-product closure assumption is needed. -/
def fullSubcategoryExactStructure :
    letI : P.IsClosedUnderFiniteProducts := E.extensionClosed_finiteProducts P
    ExactStructure P.FullSubcategory := by
  letI : P.IsClosedUnderFiniteProducts := E.extensionClosed_finiteProducts P
  exact ExactSubcategory.exactStructure E P

/-- The exact inclusion for the automatically inherited structure. -/
def fullSubcategoryExactInclusion :
    letI : P.IsClosedUnderFiniteProducts := E.extensionClosed_finiteProducts P
    ExactFunctor (E.fullSubcategoryExactStructure P) E := by
  letI : P.IsClosedUnderFiniteProducts := E.extensionClosed_finiteProducts P
  exact ExactSubcategory.exactInclusion E P

end CategoryTheory.ExactCategory.ExactStructure
