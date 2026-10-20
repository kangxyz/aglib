/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.Closed.ReducedClosedUnion
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Binary reduced closed-union descent for actual schemes and arbitrary targets.

Source: `R5Lab.Aglib.AlgebraicGeometry.Gluing.ReducedClosedUnion`.
R5 packet revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256: `5931f4dc56507798fb347ed08626fada9b85a534872d03f3ca4a3ab1a578d3f6`.
Actual objects, maps, universes and hypotheses are retained.
Native declaration ownership replaces the source application namespaces.
-/

@[expose] public section

section

/-!


The union algebra is a RING PULLBACK. No comaximality is assumed. This
module also turns an actual ring pushout square with surjective first
maps into a ring pullback once the two kernels have zero intersection.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.ReducedClosedUnion

section Quotients

variable {A : Type u} [CommRing A] (I J : Ideal A)

/-- The actual compatible pairs over the quotient by the sum. -/
def compatiblePairs : Subring ((A ⧸ I) × (A ⧸ J)) :=
  ((Ideal.Quotient.factor (show I ≤ I ⊔ J from le_sup_left)).comp
    (RingHom.fst _ _)).eqLocus
  ((Ideal.Quotient.factor (show J ≤ I ⊔ J from le_sup_right)).comp
    (RingHom.snd _ _))

/-- Send a ring element to its two quotient classes, which agree in the quotient by I + J. -/
def toCompatiblePairs : A →+* compatiblePairs I J where
  toFun a := ⟨(Ideal.Quotient.mk I a, Ideal.Quotient.mk J a), rfl⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

@[simp] theorem toCompatiblePairs_fst (a : A) :
    (toCompatiblePairs I J a).val.1 = Ideal.Quotient.mk I a := rfl

@[simp] theorem toCompatiblePairs_snd (a : A) :
    (toCompatiblePairs I J a).val.2 = Ideal.Quotient.mk J a := rfl

theorem toCompatiblePairs_ker :
    RingHom.ker (toCompatiblePairs I J) = I ⊓ J := by
  ext a
  change toCompatiblePairs I J a = 0 ↔ a ∈ I ∧ a ∈ J
  constructor
  · intro h
    exact ⟨Ideal.Quotient.eq_zero_iff_mem.mp (congrArg (fun z => z.val.1) h),
      Ideal.Quotient.eq_zero_iff_mem.mp (congrArg (fun z => z.val.2) h)⟩
  · rintro ⟨ha, hb⟩
    apply Subtype.ext
    exact Prod.ext (Ideal.Quotient.eq_zero_iff_mem.mpr ha)
      (Ideal.Quotient.eq_zero_iff_mem.mpr hb)

/-- The elementary non-comaximal Chinese remainder argument. -/
theorem toCompatiblePairs_surjective : Function.Surjective (toCompatiblePairs I J) := by
  rintro ⟨⟨x, y⟩, hxy⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  change Ideal.Quotient.mk (I ⊔ J) a = Ideal.Quotient.mk (I ⊔ J) b at hxy
  obtain ⟨c, hc, d, hd, hcd⟩ :=
    Submodule.mem_sup.mp (Ideal.Quotient.eq.mp hxy)
  refine ⟨a - c, Subtype.ext (Prod.ext ?_ ?_)⟩
  · apply Ideal.Quotient.eq.mpr
    simpa using I.neg_mem hc
  · apply Ideal.Quotient.eq.mpr
    have he : a - c - b = d := by linear_combination -hcd
    simpa [he] using hd

/-- The full quotient-by-intersection theorem, with the genuine maps. -/
def quotientInfEquivCompatiblePairs :
    (A ⧸ (I ⊓ J)) ≃+* compatiblePairs I J := by
  rw [← toCompatiblePairs_ker]
  exact (toCompatiblePairs I J).quotientKerEquivOfSurjective
    (toCompatiblePairs_surjective I J)

/-- Zero kernel intersection identifies the ambient ring with compatible pairs. -/
def equivCompatiblePairs (hIJ : I ⊓ J = ⊥) : A ≃+* compatiblePairs I J :=
  RingEquiv.ofBijective (toCompatiblePairs I J)
    ⟨(RingHom.injective_iff_ker_eq_bot _).mpr ((toCompatiblePairs_ker I J).trans hIJ),
      toCompatiblePairs_surjective I J⟩

@[simp] theorem equivCompatiblePairs_apply (hIJ : I ⊓ J = ⊥) (a : A) :
    equivCompatiblePairs I J hIJ a = toCompatiblePairs I J a := rfl

end Quotients

section ActualSquare

variable {A B C D : CommRingCat.{u}}
  (f : A ⟶ B) (g : A ⟶ C) (p : B ⟶ D) (q : C ⟶ D)

/-- Joint injectivity follows from the actual two kernels. -/
theorem jointly_injective_of_ker_inf_eq_bot
    (hker : RingHom.ker f.hom ⊓ RingHom.ker g.hom = ⊥)
    {a b : A} (hf : f a = f b) (hg : g a = g b) : a = b := by
  apply sub_eq_zero.mp
  have hz : a - b ∈ RingHom.ker f.hom ⊓ RingHom.ker g.hom := by
    exact ⟨by change f (a - b) = 0; simpa [map_sub] using sub_eq_zero.mpr hf,
      by change g (a - b) = 0; simpa [map_sub] using sub_eq_zero.mpr hg⟩
  simpa [hker] using hz

/-- Matching elements in an actual pushout have a simultaneous preimage.
This is proved through the quotient by the sum; the ring pushout is not
mistaken for the desired union pullback. -/
theorem exists_simultaneous_preimage (h : IsPushout f g p q)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (b : B) (c : C) (hbc : p b = q c) :
    ∃ a : A, f a = b ∧ g a = c := by
  let I := RingHom.ker f.hom
  let J := RingHom.ker g.hom
  let r : A →+* A ⧸ (I ⊔ J) := Ideal.Quotient.mk (I ⊔ J)
  let p' : B ⟶ CommRingCat.of (A ⧸ (I ⊔ J)) :=
    CommRingCat.ofHom (f.hom.liftOfSurjective hf ⟨r, by
      intro a ha
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left ha)⟩)
  let q' : C ⟶ CommRingCat.of (A ⧸ (I ⊔ J)) :=
    CommRingCat.ofHom (g.hom.liftOfSurjective hg ⟨r, by
      intro a ha
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_right ha)⟩)
  have hpf (a : A) : p' (f a) = r a :=
    RingHom.liftOfSurjective_comp_apply _ _ _ _
  have hqg (a : A) : q' (g a) = r a :=
    RingHom.liftOfSurjective_comp_apply _ _ _ _
  have hw : f ≫ p' = g ≫ q' := by ext a; exact (hpf a).trans (hqg a).symm
  let d := h.desc p' q' hw
  have hbc' : p' b = q' c := by
    calc
      p' b = d (p b) := congrArg (fun k : B ⟶ CommRingCat.of (A ⧸ (I ⊔ J)) => k b)
        (h.inl_desc p' q' hw).symm
      _ = d (q c) := congrArg d hbc
      _ = q' c := congrArg (fun k : C ⟶ CommRingCat.of (A ⧸ (I ⊔ J)) => k c)
        (h.inr_desc p' q' hw)
  obtain ⟨x, rfl⟩ := hf b
  obtain ⟨y, rfl⟩ := hg c
  rw [hpf, hqg] at hbc'
  have hxy : x - y ∈ I ⊔ J := Ideal.Quotient.eq.mp hbc'
  obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.mp hxy
  refine ⟨x - s, ?_, ?_⟩
  · change f s = 0 at hs
    simp [map_sub, hs]
  · change g t = 0 at ht
    have he : x - s = y + t := by linear_combination -hst
    rw [he, map_add, ht, add_zero]

/-- A surjective square which is a pushout and has zero kernel intersection
is also a pullback. This version preserves every original structure map. -/
theorem isPullback_of_isPushout_of_surjective_of_ker_inf_eq_bot
    (h : IsPushout f g p q)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hker : RingHom.ker f.hom ⊓ RingHom.ker g.hom = ⊥) :
    IsPullback f g p q := by
  classical
  apply IsPullback.mk' h.w
  · intro T a b ha hb
    ext x
    exact jointly_injective_of_ker_inf_eq_bot f g hker
      (congrArg (fun k : T ⟶ B => k x) ha)
      (congrArg (fun k : T ⟶ C => k x) hb)
  · intro T a b hab
    have hex (x : T) : ∃ y : A, f y = a x ∧ g y = b x :=
      exists_simultaneous_preimage f g p q h hf hg (a x) (b x)
        (congrArg (fun k : T ⟶ D => k x) hab)
    choose l hl hr using hex
    let lift : T ⟶ A := CommRingCat.ofHom
      { toFun := l
        map_one' := jointly_injective_of_ker_inf_eq_bot f g hker
          (by simp [hl]) (by simp [hr])
        map_mul' x y := jointly_injective_of_ker_inf_eq_bot f g hker
          (by simp [hl]) (by simp [hr])
        map_zero' := jointly_injective_of_ker_inf_eq_bot f g hker
          (by simp [hl]) (by simp [hr])
        map_add' x y := jointly_injective_of_ker_inf_eq_bot f g hker
          (by simp [hl]) (by simp [hr]) }
    exact ⟨lift, by ext x; exact hl x, by ext x; exact hr x⟩

end ActualSquare

end AlgebraicGeometry.Scheme.ReducedClosedUnion

end -- original EOF scope

end


section

/-!


The only geometric inputs are actual reduced schemes, closed immersions,
and coverage of the actual underlying topological space. Kernel intersection
zero is derived from the permanent reduced_closed_union_ideal theorem.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme.ReducedClosedUnion

variable {X Y Z : Scheme.{u}} [hXred : IsReduced X] [hYred : IsReduced Y] [hZred : IsReduced Z]
  (i : Y ⟶ X) (j : Z ⟶ X) [hiClosed : IsClosedImmersion i] [hjClosed : IsClosedImmersion j]
  (hcover : Set.range i ∪ Set.range j = Set.univ)

include hcover

/-- The kernel condition is a theorem of the actual reduced closed cover. -/
theorem closed_union_ker_inf_eq_bot : i.ker ⊓ j.ker = ⊥ := by
  have h := Scheme.IdealSheafData.reduced_closed_union_ideal (𝟙 X) i j (by simpa using hcover)
  simpa using h.symm

theorem closed_union_appTop_ker_inf_eq_bot [IsAffine X] :
    RingHom.ker i.appTop.hom ⊓ RingHom.ker j.appTop.hom = ⊥ := by
  have h := congrArg (fun K : X.IdealSheafData =>
    K.ideal ⟨⊤, isAffineOpen_top X⟩) (closed_union_ker_inf_eq_bot i j hcover)
  simpa only [Scheme.IdealSheafData.ideal_inf, Pi.inf_apply,
    Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply] using h

omit hXred hYred hZred hiClosed hjClosed in
-- Retain the reduced closed-cover conditions for subsequent restricted union descent; coverage of
-- the restricted ranges itself is a pointwise inverse-image statement.
/-- Restriction retains coverage and uses the genuine restricted immersions. -/
@[nolint unusedArguments]
theorem restrict_ranges_cover
    [IsReduced X] [IsReduced Y] [IsReduced Z]
    [IsClosedImmersion i] [IsClosedImmersion j] (U : X.Opens) :
    Set.range (i ∣_ U) ∪ Set.range (j ∣_ U) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hx : x.val ∈ Set.range i ∪ Set.range j := by rw [hcover]; trivial
  rcases hx with ⟨y, hy⟩ | ⟨z, hz⟩
  · refine Or.inl ⟨⟨y, ?_⟩, ?_⟩
    · change i y ∈ U
      simp [hy, x.property]
    · apply Subtype.ext
      simpa only [morphismRestrict_base_coe] using hy
  · refine Or.inr ⟨⟨z, ?_⟩, ?_⟩
    · change j z ∈ U
      simp [hz, x.property]
    · apply Subtype.ext
      simpa only [morphismRestrict_base_coe] using hz

/-- The genuine scheme intersection yields a ring pushout; the zero-kernel
theorem then proves the separate, required ring pullback. -/
theorem affine_sections_isPullback [IsAffine X] :
    IsPullback i.appTop j.appTop (pullback.fst i j).appTop
      (pullback.snd i j).appTop := by
  let : IsAffine Y := isAffine_of_isAffineHom i
  let : IsAffine Z := isAffine_of_isAffineHom j
  exact isPullback_of_isPushout_of_surjective_of_ker_inf_eq_bot
    i.appTop j.appTop (pullback.fst i j).appTop (pullback.snd i j).appTop
    (isPushout_appTop_of_isPullback (IsPullback.of_hasPullback i j))
    (IsClosedImmersion.isAffine_surjective_of_isAffine i).2
    (IsClosedImmersion.isAffine_surjective_of_isAffine j).2
    (closed_union_appTop_ker_inf_eq_bot i j hcover)

theorem affine_target_hom_ext [IsAffine X] {T : Scheme.{u}} [IsAffine T]
    {a b : X ⟶ T} (hi : i ≫ a = i ≫ b) (hj : j ≫ a = j ≫ b) : a = b := by
  apply ext_of_isAffine
  ext s
  apply jointly_injective_of_ker_inf_eq_bot i.appTop j.appTop
    (closed_union_appTop_ker_inf_eq_bot i j hcover)
  · exact congrArg (fun k : Y ⟶ T => k.appTop s) hi
  · exact congrArg (fun k : Z ⟶ T => k.appTop s) hj

/-- Affine source and affine target descent with exact inclusion triangles. -/
theorem exists_desc_affine_target [IsAffine X] {T : Scheme.{u}} [IsAffine T]
    (a : Y ⟶ T) (b : Z ⟶ T)
    (hab : pullback.fst i j ≫ a = pullback.snd i j ≫ b) :
    ∃ d : X ⟶ T, i ≫ d = a ∧ j ≫ d = b := by
  let H := affine_sections_isPullback i j hcover
  have hw : a.appTop ≫ (pullback.fst i j).appTop =
      b.appTop ≫ (pullback.snd i j).appTop := by
    simpa only [Scheme.Hom.comp_appTop] using congrArg Scheme.Hom.appTop hab
  let l := H.lift a.appTop b.appTop hw
  refine ⟨X.toSpecΓ ≫ Spec.map l ≫ T.isoSpec.inv, ?_, ?_⟩
  · rw [Scheme.toSpecΓ_naturality_assoc, ← Spec.map_comp_assoc]
    change Y.toSpecΓ ≫ Spec.map (H.lift _ _ _ ≫ i.appTop) ≫ T.isoSpec.inv = a
    rw [H.lift_fst, ← Scheme.toSpecΓ_naturality_assoc]
    simp
  · rw [Scheme.toSpecΓ_naturality_assoc, ← Spec.map_comp_assoc]
    change Z.toSpecΓ ≫ Spec.map (H.lift _ _ _ ≫ j.appTop) ≫ T.isoSpec.inv = b
    rw [H.lift_snd, ← Scheme.toSpecΓ_naturality_assoc]
    simp

omit hcover

/-- The comparison to the original intersection preserves both projections. -/
def restrictedIntersectionToIntersection (U : X.Opens) :
    pullback (i ∣_ U) (j ∣_ U) ⟶ pullback i j :=
  pullback.lift (pullback.fst _ _ ≫ (i ⁻¹ᵁ U).ι)
    (pullback.snd _ _ ≫ (j ⁻¹ᵁ U).ι) (by
      simpa only [Category.assoc, morphismRestrict_ι] using
        congrArg (fun k : pullback (i ∣_ U) (j ∣_ U) ⟶ U.toScheme => k ≫ U.ι)
          (pullback.condition (f := i ∣_ U) (g := j ∣_ U)))

omit hXred hYred hZred hiClosed hjClosed in
-- Retain the reduced closed-cover conditions of the intersection comparison interface; this first
-- projection equation is the universal pullback-lift equation.
@[nolint unusedArguments, reassoc (attr := simp)]
theorem restrictedIntersectionToIntersection_fst
    [IsReduced X] [IsReduced Y] [IsReduced Z]
    [IsClosedImmersion i] [IsClosedImmersion j] (U : X.Opens) :
    restrictedIntersectionToIntersection i j U ≫ pullback.fst i j =
      pullback.fst (i ∣_ U) (j ∣_ U) ≫ (i ⁻¹ᵁ U).ι := by
  simp [restrictedIntersectionToIntersection]

omit hXred hYred hZred hiClosed hjClosed in
-- Retain the reduced closed-cover conditions of the intersection comparison interface; this
-- second projection equation is the universal pullback-lift equation.
@[nolint unusedArguments, reassoc (attr := simp)]
theorem restrictedIntersectionToIntersection_snd
    [IsReduced X] [IsReduced Y] [IsReduced Z]
    [IsClosedImmersion i] [IsClosedImmersion j] (U : X.Opens) :
    restrictedIntersectionToIntersection i j U ≫ pullback.snd i j =
      pullback.snd (i ∣_ U) (j ∣_ U) ≫ (j ⁻¹ᵁ U).ι := by
  simp [restrictedIntersectionToIntersection]

end AlgebraicGeometry.Scheme.ReducedClosedUnion

end -- original EOF scope

end


section

/-!


Joint uniqueness for an actual reduced closed cover. The target is arbitrary:
no separatedness hypothesis is used. Pointwise equality gives a common affine
target neighbourhood, after which affine uniqueness applies on a sufficiently
small affine source neighbourhood.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.ReducedClosedUnion

/-- Equality after a source morphism persists for simultaneous restrictions
to a common source open and target open. -/
private theorem restricted_comp_resLE_eq
    {X Y T : Scheme.{u}} (i : Y ⟶ X) {a b : X ⟶ T}
    (hi : i ≫ a = i ≫ b) (U : X.Opens) (V : T.Opens)
    (ha : U ≤ a ⁻¹ᵁ V) (hb : U ≤ b ⁻¹ᵁ V) :
    (i ∣_ U) ≫ a.resLE V U ha = (i ∣_ U) ≫ b.resLE V U hb := by
  rw [← cancel_mono V.ι]
  simp only [Category.assoc, Scheme.Hom.resLE_comp_ι,
    morphismRestrict_ι_assoc, hi]

/-- Two morphisms from a reduced scheme agree if they agree on each of two
reduced closed subschemes whose underlying closed sets cover it. -/
theorem hom_ext
    {X Y Z T : Scheme.{u}} [hXred : IsReduced X] [hYred : IsReduced Y] [hZred : IsReduced Z]
    (i : Y ⟶ X) (j : Z ⟶ X) [hiClosed : IsClosedImmersion i] [hjClosed : IsClosedImmersion j]
    (hcover : Set.range i ∪ Set.range j = Set.univ)
    {a b : X ⟶ T} (hi : i ≫ a = i ≫ b) (hj : j ≫ a = j ≫ b) : a = b := by
  have hab : ∀ x : X, a x = b x := by
    intro x
    have hx : x ∈ Set.range i ∪ Set.range j := by
      rw [hcover]
      trivial
    rcases hx with ⟨y, rfl⟩ | ⟨z, rfl⟩
    · simpa only [Scheme.Hom.comp_apply] using
        congrArg (fun f : Y ⟶ T => f y) hi
    · simpa only [Scheme.Hom.comp_apply] using
        congrArg (fun f : Z ⟶ T => f z) hj
  refine Scheme.hom_ext_of_forall a b fun x => ?_
  obtain ⟨V, hV, haxV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := T) (x := a x)
      (U := ⊤) (by simp)
  have hbxV : b x ∈ V := by
    rw [← hab x]
    exact haxV
  obtain ⟨U, hU, hxU, hUV : U ≤ a ⁻¹ᵁ V ⊓ b ⁻¹ᵁ V⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x)
      (U := a ⁻¹ᵁ V ⊓ b ⁻¹ᵁ V) ⟨haxV, hbxV⟩
  let : IsAffine U.toScheme := hU
  let : IsAffine V.toScheme := hV
  have ha : U ≤ a ⁻¹ᵁ V := hUV.trans inf_le_left
  have hb : U ≤ b ⁻¹ᵁ V := hUV.trans inf_le_right
  have hlocal : a.resLE V U ha = b.resLE V U hb :=
    affine_target_hom_ext (i ∣_ U) (j ∣_ U)
      (restrict_ranges_cover i j hcover U)
      (a := a.resLE V U ha) (b := b.resLE V U hb)
      (restricted_comp_resLE_eq i hi U V ha hb)
      (restricted_comp_resLE_eq j hj U V ha hb)
  refine ⟨U, hxU, ?_⟩
  simpa only [Scheme.Hom.resLE_comp_ι] using
    congrArg (fun f : U.toScheme ⟶ V.toScheme => f ≫ V.ι) hlocal

end AlgebraicGeometry.Scheme.ReducedClosedUnion

end -- original EOF scope

end


section

/-!


Arbitrary-target existence is genuinely local. For an affine target open V,
remove the two closed images of the complements of its inverse images. An
affine neighborhood inside the remaining open has both branches mapping to V.
The scheme-theoretic intersection, including its nilpotents, is retained.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme.ReducedClosedUnion

variable {X Y Z T : Scheme.{u}} [hXred : IsReduced X] [hYred : IsReduced Y] [hZred : IsReduced Z]
  (i : Y ⟶ X) (j : Z ⟶ X) [hiClosed : IsClosedImmersion i] [hjClosed : IsClosedImmersion j]
  (hcover : Set.range i ∪ Set.range j = Set.univ)
  (a : Y ⟶ T) (b : Z ⟶ T)
  (hab : pullback.fst i j ≫ a = pullback.snd i j ≫ b)

include hab

omit hXred hYred hZred hiClosed hjClosed in
-- Retain the reduced closed-cover conditions in the closed-union descent interface; equality of
-- these two images only uses the supplied compatibility on the actual pullback.
/-- Actual intersection compatibility implies equality over a common point. -/
@[nolint unusedArguments]
theorem images_eq_of_base_eq
    [IsReduced X] [IsReduced Y] [IsReduced Z]
    [IsClosedImmersion i] [IsClosedImmersion j] (y : Y) (z : Z) (hyz : i y = j z) : a y = b z := by
  obtain ⟨w, hwY, hwZ⟩ := Scheme.Pullback.exists_preimage_pullback y z hyz
  have h := congrArg (fun k : pullback i j ⟶ T => k w) hab
  simpa only [Scheme.Hom.comp_apply, hwY, hwZ] using h

include hcover

/-- All branch points above a given ambient point have one common target image. -/
theorem exists_common_image (x : X) :
    ∃ t : T, (∀ y : Y, i y = x → a y = t) ∧ (∀ z : Z, j z = x → b z = t) := by
  have hx : x ∈ Set.range i ∪ Set.range j := by rw [hcover]; trivial
  rcases hx with ⟨y, rfl⟩ | ⟨z, rfl⟩
  · refine ⟨a y, ?_, ?_⟩
    · intro y' hy'
      exact congrArg a (i.isClosedEmbedding.injective hy')
    · intro z hz
      exact (images_eq_of_base_eq i j a b hab y z hz.symm).symm
  · refine ⟨b z, ?_, ?_⟩
    · intro y hy
      exact images_eq_of_base_eq i j a b hab y z hy
    · intro z' hz'
      exact congrArg b (j.isClosedEmbedding.injective hz')

/-- The local affine map, with exact triangles to the original branch maps. -/
theorem exists_affine_local_desc (x : X) :
    ∃ (U : X.Opens), IsAffineOpen U ∧ x ∈ U ∧
      ∃ d : U.toScheme ⟶ T,
        (i ∣_ U) ≫ d = (i ⁻¹ᵁ U).ι ≫ a ∧
        (j ∣_ U) ≫ d = (j ⁻¹ᵁ U).ι ≫ b := by
  classical
  obtain ⟨t, htY, htZ⟩ := exists_common_image i j hcover a b hab x
  obtain ⟨V, hV, htV, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := T) (x := t) (U := ⊤) (by trivial)
  let KY : Set X := i '' (a ⁻¹ᵁ V : Set Y)ᶜ
  let KZ : Set X := j '' (b ⁻¹ᵁ V : Set Z)ᶜ
  have hKY : IsClosed KY := i.isClosedEmbedding.isClosedMap _
    (a ⁻¹ᵁ V).isOpen.isClosed_compl
  have hKZ : IsClosed KZ := j.isClosedEmbedding.isClosedMap _
    (b ⁻¹ᵁ V).isOpen.isClosed_compl
  let W : X.Opens := ⟨(KY ∪ KZ)ᶜ, (hKY.union hKZ).isOpen_compl⟩
  have hxW : x ∈ W := by
    change x ∉ KY ∪ KZ
    rintro (⟨y, hy, hyx⟩ | ⟨z, hz, hzx⟩)
    · apply hy
      change a y ∈ V
      rw [htY y hyx]
      exact htV
    · apply hz
      change b z ∈ V
      rw [htZ z hzx]
      exact htV
  obtain ⟨U, hU, hxU, hUW⟩ := exists_isAffineOpen_mem_and_subset hxW
  have hY : i ⁻¹ᵁ U ≤ a ⁻¹ᵁ V := by
    intro y hy
    by_contra hn
    exact (hUW hy) (Or.inl ⟨y, hn, rfl⟩)
  have hZ : j ⁻¹ᵁ U ≤ b ⁻¹ᵁ V := by
    intro z hz
    by_contra hn
    exact (hUW hz) (Or.inr ⟨z, hn, rfl⟩)
  let a' : (i ⁻¹ᵁ U).toScheme ⟶ V.toScheme := a.resLE V (i ⁻¹ᵁ U) hY
  let b' : (j ⁻¹ᵁ U).toScheme ⟶ V.toScheme := b.resLE V (j ⁻¹ᵁ U) hZ
  have hab' : pullback.fst (i ∣_ U) (j ∣_ U) ≫ a' =
      pullback.snd (i ∣_ U) (j ∣_ U) ≫ b' := by
    rw [← cancel_mono V.ι]
    simp only [Category.assoc, a', b', Scheme.Hom.resLE_comp_ι]
    rw [← restrictedIntersectionToIntersection_fst_assoc,
      ← restrictedIntersectionToIntersection_snd_assoc, hab]
  let : IsAffine U.toScheme := hU
  let : IsAffine V.toScheme := hV
  obtain ⟨d, hdY, hdZ⟩ := exists_desc_affine_target (i ∣_ U) (j ∣_ U)
    (restrict_ranges_cover i j hcover U) a' b' hab'
  refine ⟨U, hU, hxU, d ≫ V.ι, ?_, ?_⟩
  · rw [← Category.assoc, hdY]
    exact Scheme.Hom.resLE_comp_ι a hY
  · rw [← Category.assoc, hdZ]
    exact Scheme.Hom.resLE_comp_ι b hZ

end AlgebraicGeometry.Scheme.ReducedClosedUnion

end -- original EOF scope

end


section

/-!


Binary reduced closed-union pushout in Scheme, with arbitrary target and
the actual scheme-theoretic intersection. All inclusion maps are the
original morphisms. The base triangle is derived from joint uniqueness.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.ReducedClosedUnion

variable {X Y Z : Scheme.{u}} [hXred : IsReduced X] [hYred : IsReduced Y] [hZred : IsReduced Z]
  (i : Y ⟶ X) (j : Z ⟶ X) [hiClosed : IsClosedImmersion i] [hjClosed : IsClosedImmersion j]
  (hcover : Set.range i ∪ Set.range j = Set.univ)

include hcover

/-- Compatible morphisms to an arbitrary scheme descend across the actual
binary reduced closed cover. No target separatedness is needed. -/
theorem exists_desc {T : Scheme.{u}} (a : Y ⟶ T) (b : Z ⟶ T)
    (hab : pullback.fst i j ≫ a = pullback.snd i j ≫ b) :
    ∃ d : X ⟶ T, i ≫ d = a ∧ j ≫ d = b := by
  classical
  choose U hU hx d hdY hdZ using exists_affine_local_desc i j hcover a b hab
  let 𝒰 : X.OpenCover :=
    { I₀ := X
      X x := (U x).toScheme
      f x := (U x).ι
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        refine ⟨fun x => ⟨x, by simpa using hx x⟩, inferInstance⟩ }
  have hd : ∀ x y, pullback.fst (𝒰.f x) (𝒰.f y) ≫ d x =
      pullback.snd (𝒰.f x) (𝒰.f y) ≫ d y := by
    intro x y
    have hover : X.homOfLE (show U x ⊓ U y ≤ U x from inf_le_left) ≫ d x =
        X.homOfLE (show U x ⊓ U y ≤ U y from inf_le_right) ≫ d y := by
      apply hom_ext (i ∣_ (U x ⊓ U y)) (j ∣_ (U x ⊓ U y))
        (restrict_ranges_cover i j hcover (U x ⊓ U y))
      · rw [morphismRestrict_homOfLE_assoc, morphismRestrict_homOfLE_assoc,
          hdY x, hdY y]
        simp
      · rw [morphismRestrict_homOfLE_assoc, morphismRestrict_homOfLE_assoc,
          hdZ x, hdZ y]
        simp
    change pullback.fst (U x).ι (U y).ι ≫ d x =
      pullback.snd (U x).ι (U y).ι ≫ d y
    rw [← cancel_epi (isPullback_opens_inf (U x) (U y)).isoPullback.hom]
    simpa only [IsPullback.isoPullback_hom_fst_assoc,
      IsPullback.isoPullback_hom_snd_assoc] using hover
  let glued : X ⟶ T := 𝒰.glueMorphisms d hd
  have hglue (x : X) : (U x).ι ≫ glued = d x := 𝒰.ι_glueMorphisms d hd x
  refine ⟨glued, ?_, ?_⟩
  · apply Scheme.hom_ext_of_forall
    intro y
    refine ⟨i ⁻¹ᵁ U (i y), hx (i y), ?_⟩
    calc
      (i ⁻¹ᵁ U (i y)).ι ≫ i ≫ glued =
          (i ∣_ U (i y)) ≫ (U (i y)).ι ≫ glued := by
        rw [morphismRestrict_ι_assoc]
      _ = (i ∣_ U (i y)) ≫ d (i y) := by rw [hglue]
      _ = (i ⁻¹ᵁ U (i y)).ι ≫ a := hdY (i y)
  · apply Scheme.hom_ext_of_forall
    intro z
    refine ⟨j ⁻¹ᵁ U (j z), hx (j z), ?_⟩
    calc
      (j ⁻¹ᵁ U (j z)).ι ≫ j ≫ glued =
          (j ∣_ U (j z)) ≫ (U (j z)).ι ≫ glued := by
        rw [morphismRestrict_ι_assoc]
      _ = (j ∣_ U (j z)) ≫ d (j z) := by rw [hglue]
      _ = (j ⁻¹ᵁ U (j z)).ι ≫ b := hdZ (j z)

/-- The categorical Scheme pushout of the genuine intersection. -/
theorem isPushout :
    IsPushout (pullback.fst i j) (pullback.snd i j) i j := by
  apply IsPushout.mk' pullback.condition
  · intro T a b ha hb
    exact hom_ext i j hcover ha hb
  · intro T a b hab
    exact exists_desc i j hcover a b hab

/-- Canonical descent, defined by the proved Scheme pushout. -/
def desc {T : Scheme.{u}} (a : Y ⟶ T) (b : Z ⟶ T)
    (hab : pullback.fst i j ≫ a = pullback.snd i j ≫ b) : X ⟶ T :=
  (isPushout i j hcover).desc a b hab

@[reassoc (attr := simp)]
theorem inl_desc {T : Scheme.{u}} (a : Y ⟶ T) (b : Z ⟶ T)
    (hab : pullback.fst i j ≫ a = pullback.snd i j ≫ b) :
    i ≫ desc i j hcover a b hab = a :=
  (isPushout i j hcover).inl_desc a b hab

@[reassoc (attr := simp)]
theorem inr_desc {T : Scheme.{u}} (a : Y ⟶ T) (b : Z ⟶ T)
    (hab : pullback.fst i j ≫ a = pullback.snd i j ≫ b) :
    j ≫ desc i j hcover a b hab = b :=
  (isPushout i j hcover).inr_desc a b hab

theorem desc_unique {T : Scheme.{u}} (a : Y ⟶ T) (b : Z ⟶ T)
    (hab : pullback.fst i j ≫ a = pullback.snd i j ≫ b)
    (d : X ⟶ T) (hi : i ≫ d = a) (hj : j ≫ d = b) :
    d = desc i j hcover a b hab := by
  apply hom_ext i j hcover
  · simpa using hi
  · simpa using hj

/-- Descent respects an arbitrary base map. The base is not required to be
affine or separated, and this is an exact Scheme triangle. -/
@[reassoc]
theorem desc_base {T S : Scheme.{u}} (a : Y ⟶ T) (b : Z ⟶ T)
    (hab : pullback.fst i j ≫ a = pullback.snd i j ≫ b)
    (t : T ⟶ S) (s : X ⟶ S)
    (ha : a ≫ t = i ≫ s) (hb : b ≫ t = j ≫ s) :
    desc i j hcover a b hab ≫ t = s := by
  apply hom_ext i j hcover
  · simpa using ha
  · simpa using hb

@[reassoc]
theorem desc_comp {T S : Scheme.{u}} (a : Y ⟶ T) (b : Z ⟶ T)
    (hab : pullback.fst i j ≫ a = pullback.snd i j ≫ b) (t : T ⟶ S) :
    desc i j hcover a b hab ≫ t =
      desc i j hcover (a ≫ t) (b ≫ t) (by simpa using congrArg (fun k => k ≫ t) hab) := by
  apply hom_ext i j hcover <;> simp

end AlgebraicGeometry.Scheme.ReducedClosedUnion

end -- original EOF scope

end
