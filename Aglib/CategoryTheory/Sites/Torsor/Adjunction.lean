/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsor.InverseImage

/-! # Actual adjoint torsor maps in a native site presentation

The continuous site functor supplies the original Set and additive adjunctions.
The same free lift, augmentation kernel and pushout produce the middle map.
The intrinsic integer-one law proves its projection square and Ext naturality.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf

universe uC vC uD vD w
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {L : Sheaf J AddCommGrpCat.{w}} {M : Sheaf K AddCommGrpCat.{w}}

/-- The original adjoint carrier map and its literal coefficient-equivariance condition. -/
structure Torsor.AdjointHom (F : C ⥤ D) [F.IsContinuous J K]
    (q : L ⟶ (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj M)
    (P : Torsor L) (Q : Torsor M) where
  /-- The original Set direct-image map of the actual carrier. -/
  map : P.carrier ⟶ (F.sheafPushforwardContinuous (Type w) J K).obj Q.carrier
  equivariant : ∀ (U : Cᵒᵖ) (b : L.obj.obj U) (t : P.carrier.obj.obj U),
    map.hom.app U (P.action U b t) =
      Q.action (F.op.obj U) (q.hom.app U b) (map.hom.app U t)

variable [HasSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- Equality of morphisms out of the actual free sheaf is checked on its
canonical torsor generators. -/
theorem torsorFreeSheaf_hom_ext (P : Torsor L) {E : Sheaf J AddCommGrpCat.{w}}
    (a b : torsorFreeSheaf P ⟶ E)
    (h : ∀ U t, a.hom.app U (torsorGenerator P U t) = b.hom.app U (torsorGenerator P U t)) :
    a = b := by
  let adj := sheafificationAdjunction J AddCommGrpCat.{w}
  apply (adj.homEquiv (torsorFreePresheaf P) E).injective
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  let uU : FreeAbelianGroup (P.carrier.obj.obj U) →+ (torsorFreeSheaf P).obj.obj U :=
    ((toSheafify J (torsorFreePresheaf P)).app U).hom
  let aU : (torsorFreeSheaf P).obj.obj U →+ E.obj.obj U := (a.hom.app U).hom
  let bU : (torsorFreeSheaf P).obj.obj U →+ E.obj.obj U := (b.hom.app U).hom
  change aU.comp uU = bU.comp uU
  exact FreeAbelianGroup.lift_ext _ _ (h U)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The free-sheaf lift sends each canonical generator to its specified section. -/
theorem torsorFreeLiftSheaf_generator (P : Torsor L) {E : Sheaf J AddCommGrpCat.{w}}
    (r : P.carrier ⟶ underlyingSetSheaf E) (U : Cᵒᵖ) (t : P.carrier.obj.obj U) :
    (torsorFreeLiftSheaf P r).hom.app U (torsorGenerator P U t) = r.hom.app U t := by
  have h := congrArg (fun k => k.app U (FreeAbelianGroup.of t)) (torsorFreeLiftSheaf_unit P r)
  exact h.trans (FreeAbelianGroup.lift_apply_of _ t)

/-- The canonical inclusion of a genuine torsor lands over literal integer one. -/
theorem torsorCanonicalSetInclusion_projection (P : Torsor L)
    (U : Cᵒᵖ) (t : P.carrier.obj.obj U) :
    (torsorExtension P).g.hom.app U ((torsorCanonicalSetInclusion P).hom.app U t) =
      (constantIntegerOne J).hom.app U PUnit.unit :=
  ((torsorCanonicalExtensionIso P).carrierIso.hom.hom.app U t).property

variable (F : C ⥤ D) [F.IsContinuous J K]
  [(F.sheafPushforwardContinuous (Type w) J K).IsRightAdjoint]
  [PreservesFiniteLimits (F.sheafPullback (Type w) J K)]
  [(F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint]
  [PreservesFiniteLimits (F.sheafPullback AddCommGrpCat.{w} J K)]
  [HasSheafify K AddCommGrpCat.{w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {M : Sheaf K AddCommGrpCat.{w}}
  {q : L ⟶ (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj M}
  {P : Torsor L} {Q : Torsor M} (r : Torsor.AdjointHom F q P Q)


/-- Compose the actual carrier map with the canonical target-extension inclusion. -/
def torsorAdjunctionSetLift :
    P.carrier ⟶ underlyingSetSheaf ((F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj
      (torsorExtension Q).X₂) :=
  r.map ≫
    (F.sheafPushforwardContinuous (Type w) J K).map
      (torsorCanonicalSetInclusion Q)

omit [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [(F.sheafPushforwardContinuous (Type w) J K).IsRightAdjoint]
    [PreservesFiniteLimits (F.sheafPullback (Type w) J K)]
    [(F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint]
    [PreservesFiniteLimits (F.sheafPullback AddCommGrpCat.{w} J K)] in
/-- The resulting lift has the actual positive coefficient translation law. -/
theorem torsorAdjunctionSetLift_action (U : Cᵒᵖ) (a : L.obj.obj U)
    (t : P.carrier.obj.obj U) :
    (torsorAdjunctionSetLift F r).hom.app U (P.action U a t) =
      (q ≫ (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map (torsorExtension Q).f).hom.app
        U a +
        (show ((F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj (torsorExtension
          Q).X₂).obj.obj U from
          (torsorAdjunctionSetLift F r).hom.app U t) := by
  let V := F.op.obj U
  let a' : M.obj.obj V := q.hom.app U a
  let t' : Q.carrier.obj.obj V := r.map.hom.app U t
  have hr : r.map.hom.app U (P.action U a t) = Q.action V a' t' := r.equivariant U a t
  exact (congrArg (fun x : Q.carrier.obj.obj V =>
    (torsorCanonicalSetInclusion Q).hom.app V x) hr).trans
      (torsorCanonicalSetInclusion_action Q V a' t')

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The freely induced map lies over precisely the canonical integer adjunction map. -/
theorem torsorAdjunctionFreeLift_projection :
    torsorFreeLiftSheaf P (torsorAdjunctionSetLift F r) ≫
        (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map (torsorExtension Q).g =
      torsorAugmentation P ≫ (Topos.AdditiveCoefficientAction.ofSiteFunctor F J
        K).integerAdjunctionMap := by
  apply torsorFreeSheaf_hom_ext
  intro U t
  change (torsorExtension Q).g.hom.app (F.op.obj U)
      ((torsorFreeLiftSheaf P (torsorAdjunctionSetLift F r)).hom.app U (torsorGenerator P U t)) =
    (Topos.AdditiveCoefficientAction.ofSiteFunctor F J K).integerAdjunctionMap.hom.app U
      ((torsorAugmentation P).hom.app U (torsorGenerator P U t))
  rw [torsorFreeLiftSheaf_generator, torsorGenerator_augmentation]
  erw [Topos.AdditiveCoefficientAction.ofSiteFunctor_integerAdjunctionMap_one]
  exact torsorCanonicalSetInclusion_projection Q _ _

/-- The augmentation-kernel relation produces the actual canonical extension
map into direct image by the pushout universal property. -/
def torsorAdjunctionMiddle : (torsorExtension P).X₂ ⟶ (F.sheafPushforwardContinuous
  AddCommGrpCat.{w} J K).obj (torsorExtension Q).X₂ :=
  pushout.desc (torsorFreeLiftSheaf P (torsorAdjunctionSetLift F r))
    (q ≫ (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map (torsorExtension Q).f)
    (torsorFreeLiftSheaf_kernel P (torsorAdjunctionSetLift F r)
      (q ≫ (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map (torsorExtension Q).f)
        (torsorAdjunctionSetLift_action F r))

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [(F.sheafPushforwardContinuous (Type w) J K).IsRightAdjoint]
    [PreservesFiniteLimits (F.sheafPullback (Type w) J K)]
    [(F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint]
    [PreservesFiniteLimits (F.sheafPullback AddCommGrpCat.{w} J K)] in
/-- The coefficient square of the actual direct-image extension map. -/
@[simp] theorem torsorAdjunctionMiddle_inclusion :
    (torsorExtension P).f ≫ torsorAdjunctionMiddle F r =
      q ≫ (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map (torsorExtension Q).f :=
  pushout.inr_desc _ _ _

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [(F.sheafPushforwardContinuous (Type w) J K).IsRightAdjoint]
    [PreservesFiniteLimits (F.sheafPullback (Type w) J K)]
    [(F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint]
    [PreservesFiniteLimits (F.sheafPullback AddCommGrpCat.{w} J K)] in
/-- The free generators have their prescribed images in the target extension. -/
@[simp] theorem torsorAdjunctionMiddle_free :
    pushout.inl (torsorKernelSheafInclusion P) (torsorDifferenceSheafMap P) ≫
      torsorAdjunctionMiddle F r = torsorFreeLiftSheaf P (torsorAdjunctionSetLift F r) :=
  pushout.inl_desc _ _ _

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The projection square uses the canonical integer adjunction, proved on
actual free generators rather than assumed at the cohomology level. -/
theorem torsorAdjunctionMiddle_projection :
    torsorAdjunctionMiddle F r ≫ (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map
      (torsorExtension Q).g =
      (torsorExtension P).g ≫ (Topos.AdditiveCoefficientAction.ofSiteFunctor F J
        K).integerAdjunctionMap := by
  let R := F.sheafPushforwardContinuous AddCommGrpCat.{w} J K
  let iP : L ⟶ (torsorExtension P).X₂ := (torsorExtension P).f
  let pP : (torsorExtension P).X₂ ⟶ constantIntegerSheaf J := (torsorExtension P).g
  let iQ : M ⟶ (torsorExtension Q).X₂ := (torsorExtension Q).f
  let pQ : (torsorExtension Q).X₂ ⟶ constantIntegerSheaf K := (torsorExtension Q).g
  let k : constantIntegerSheaf J ⟶ R.obj (constantIntegerSheaf K) :=
    (Topos.AdditiveCoefficientAction.ofSiteFunctor F J K).integerAdjunctionMap
  let m : (torsorExtension P).X₂ ⟶ R.obj (torsorExtension Q).X₂ := torsorAdjunctionMiddle F r
  let j : torsorFreeSheaf P ⟶ (torsorExtension P).X₂ :=
    pushout.inl (torsorKernelSheafInclusion P) (torsorDifferenceSheafMap P)
  have hi : iP ≫ m = q ≫ R.map iQ := torsorAdjunctionMiddle_inclusion F r
  have hj : j ≫ m = torsorFreeLiftSheaf P (torsorAdjunctionSetLift F r) :=
    torsorAdjunctionMiddle_free F r
  have hp : j ≫ pP = torsorAugmentation P :=
    CategoryTheory.Abelian.ExtensionPushout.inl_projection
      (torsorAugmentationComplex P) (torsorDifferenceSheafMap P)
  have hzP : iP ≫ pP = 0 := (torsorExtension P).zero
  have hzQ : iQ ≫ pQ = 0 := (torsorExtension Q).zero
  apply pushout.hom_ext
  · change (j ≫ m) ≫ R.map pQ = (j ≫ pP) ≫ k
    rw [hj, hp]
    exact torsorAdjunctionFreeLift_projection F r
  · change (iP ≫ m) ≫ R.map pQ = (iP ≫ pP) ≫ k
    rw [hi, hzP, zero_comp, Category.assoc, ← Functor.map_comp]
    rw [hzQ]
    have hzero : R.map (0 : M ⟶ constantIntegerSheaf K) = 0 := by
      ext U b
      rfl
    rw [hzero, comp_zero]

/-- The coefficient map transposed through the actual inverse/direct image adjunction. -/
def torsorAdjunctionCoefficient : (F.sheafPullback AddCommGrpCat.{w} J K).obj L ⟶ M :=
  ((F.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).homEquiv L M).symm q

/-- The constructed middle-sheaf map transposed through the same actual adjunction. -/
def torsorAdjunctionMiddleAdjoint :
    (F.sheafPullback AddCommGrpCat.{w} J K).obj (torsorExtension P).X₂ ⟶ (torsorExtension Q).X₂ :=
  ((F.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).homEquiv _ _).symm (torsorAdjunctionMiddle
    F r)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [(F.sheafPushforwardContinuous (Type w) J K).IsRightAdjoint]
    [PreservesFiniteLimits (F.sheafPullback (Type w) J K)]
    [PreservesFiniteLimits (F.sheafPullback AddCommGrpCat.{w} J K)] in
/-- The coefficient square survives adjunction with its actual sheaf maps. -/
theorem torsorAdjunctionMiddleAdjoint_inclusion :
    torsorAdjunctionCoefficient F (q := q) ≫ (torsorExtension Q).f =
      (F.sheafPullback AddCommGrpCat.{w} J K).map (torsorExtension P).f ≫
        torsorAdjunctionMiddleAdjoint F r := by
  let adj := F.sheafAdjunctionContinuous AddCommGrpCat.{w} J K
  let iP : L ⟶ (torsorExtension P).X₂ := (torsorExtension P).f
  let iQ : M ⟶ (torsorExtension Q).X₂ := (torsorExtension Q).f
  let m : (torsorExtension P).X₂ ⟶
      (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj (torsorExtension Q).X₂ :=
    torsorAdjunctionMiddle F r
  have h : iP ≫ m = q ≫ (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map iQ :=
    torsorAdjunctionMiddle_inclusion F r
  change (adj.homEquiv L M).symm q ≫ iQ =
    (F.sheafPullback AddCommGrpCat.{w} J K).map iP ≫ (adj.homEquiv _ _).symm m
  exact (adj.homEquiv_naturality_right_symm q iQ).symm.trans
    ((congrArg (adj.homEquiv L (torsorExtension Q).X₂).symm h.symm).trans
      (adj.homEquiv_naturality_left_symm iP m))

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The projection square survives adjunction with the fixed integer transport. -/
theorem torsorAdjunctionMiddleAdjoint_projection :
    torsorAdjunctionMiddleAdjoint F r ≫ (torsorExtension Q).g =
      (torsorInverseImageExtension (Topos.AdditiveCoefficientAction.ofSiteFunctor F J K) P).g := by
  let adj := F.sheafAdjunctionContinuous AddCommGrpCat.{w} J K
  let pP : (torsorExtension P).X₂ ⟶ constantIntegerSheaf J := (torsorExtension P).g
  let pQ : (torsorExtension Q).X₂ ⟶ constantIntegerSheaf K := (torsorExtension Q).g
  let c : (F.sheafPullback AddCommGrpCat.{w} J K).obj (constantIntegerSheaf J) ⟶
      constantIntegerSheaf K :=
    (Topos.AdditiveCoefficientAction.ofSiteFunctor F J K).integerIso.hom
  let m : (torsorExtension P).X₂ ⟶
      (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj (torsorExtension Q).X₂ :=
    torsorAdjunctionMiddle F r
  have h : m ≫ (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map pQ =
      pP ≫ adj.homEquiv _ _ c := torsorAdjunctionMiddle_projection F r
  change (adj.homEquiv _ _).symm m ≫ pQ =
    (F.sheafPullback AddCommGrpCat.{w} J K).map pP ≫ c
  exact (adj.homEquiv_naturality_right_symm m pQ).symm.trans
    ((congrArg (adj.homEquiv (torsorExtension P).X₂ (constantIntegerSheaf K)).symm h).trans
      ((adj.homEquiv_naturality_left_symm pP (adj.homEquiv _ _ c)).trans
        (congrArg (fun q : (F.sheafPullback AddCommGrpCat.{w} J K).obj
          (constantIntegerSheaf J) ⟶ constantIntegerSheaf K =>
            (F.sheafPullback AddCommGrpCat.{w} J K).map pP ≫ q)
          ((adj.homEquiv _ _).symm_apply_apply c))))

/-- The actual canonical extension morphism induced by the ordinary adjoint
torsor map. Both squares were constructed above. -/
def torsorAdjunctionExtensionMap :
    torsorInverseImageExtension (Topos.AdditiveCoefficientAction.ofSiteFunctor F J K) P ⟶
      torsorExtension Q where
  τ₁ := torsorAdjunctionCoefficient F (q := q)
  τ₂ := torsorAdjunctionMiddleAdjoint F r
  τ₃ := 𝟙 _
  comm₁₂ := torsorAdjunctionMiddleAdjoint_inclusion F r
  comm₂₃ := (torsorAdjunctionMiddleAdjoint_projection F r).trans
    (Category.comp_id (torsorInverseImageExtension
      (Topos.AdditiveCoefficientAction.ofSiteFunctor F J K) P).g).symm

section ExtClass
universe eJ eK
variable [HasExt.{eJ} (Sheaf J AddCommGrpCat.{w})]
variable [HasExt.{eK} (Sheaf K AddCommGrpCat.{w})]

include r in
/-- Ordinary equivariance of the actual adjoint sheaf maps proves the exact
site/coefficient naturality identity of their canonical Ext classes. -/
theorem torsorExtClass_adjunction :
    H.map (torsorAdjunctionCoefficient F (q := q)) 1
      (torsorH1InverseImageMap (Topos.AdditiveCoefficientAction.ofSiteFunctor F J K) L
        (torsorExtClass P)) = torsorExtClass Q := by
  let c : (F.sheafPullback AddCommGrpCat.{w} J K).obj L ⟶ M :=
    torsorAdjunctionCoefficient F (q := q)
  let ξ : H ((F.sheafPullback AddCommGrpCat.{w} J K).obj L) 1 :=
    (torsorInverseImageExtension_shortExact
      (Topos.AdditiveCoefficientAction.ofSiteFunctor F J K) P).extClass
  let η : H M 1 := torsorExtClass Q
  have h : ξ.comp (Abelian.Ext.mk₀ c) (add_zero 1) =
      (Abelian.Ext.mk₀ (𝟙 (constantIntegerSheaf K))).comp η (zero_add 1) :=
    ShortComplex.ShortExact.extClass_naturality
      (torsorInverseImageExtension_shortExact
        (Topos.AdditiveCoefficientAction.ofSiteFunctor F J K) P)
      (torsorExtension_shortExact Q) (torsorAdjunctionExtensionMap F r)
  have himage : ξ = torsorH1InverseImageMap
      (Topos.AdditiveCoefficientAction.ofSiteFunctor F J K) L (torsorExtClass P) :=
    torsorInverseImageExtension_extClass (Topos.AdditiveCoefficientAction.ofSiteFunctor F J K) P
  have hclass : H.map c 1 ξ = η := h.trans (Abelian.Ext.mk₀_id_comp η)
  exact (congrArg (H.map c 1) himage).symm.trans hclass

end ExtClass
end CategoryTheory.Sheaf
