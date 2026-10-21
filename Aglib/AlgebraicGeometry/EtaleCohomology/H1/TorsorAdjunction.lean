/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Current interface basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original construction and mathematical provenance are retained below. -/
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.TorsorBaseChange

/-!
# Actual adjoint torsor maps and canonical extension naturality

Construction for `K2-018#eq:k2018-pointed-character`, frozen basis
`7f86e4a1763cc4ec35e9b0a8acd659750355a0de`. An actual carrier map into direct
image, equivariant for an actual coefficient map, induces a morphism of the
canonical extensions. The free-abelian sheaf, its augmentation-kernel relation,
and its pushout construct the middle map. The literal integer-one unit fixes
the projection square and hence the sign and variance of the Ext identity.
-/

@[expose] public section

noncomputable section
set_option maxRecDepth 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology
universe u
attribute [local instance] hasSheafifyLarge
variable {X S : Scheme.{u}} {L : AbelianSheaf.{u, u + 1} X} {M : AbelianSheaf.{u, u + 1} S}

/-- A genuine adjoint torsor map: the only conditions concern actual sheaf
maps and their ordinary action on sections. -/
structure Torsor.AdjointHom (f : S ⟶ X) (q : L ⟶ (directImage f).obj M)
    (P : Torsor L) (Q : Torsor M) where
  /-- The carrier sheaf map from `P` to the direct image of the carrier of `Q`. -/
  map : P.carrier ⟶ (setDirectImage f).obj Q.carrier
  equivariant : ∀ (U : X.Etaleᵒᵖ) (a : L.obj.obj U) (t : P.carrier.obj.obj U),
    map.hom.app U (P.action U a t) =
      Q.action ((siteBaseChange f).op.obj U) (q.hom.app U a) (map.hom.app U t)

/-- Equality of morphisms out of the actual free sheaf is checked on its
canonical torsor generators. -/
theorem torsorFreeSheaf_hom_ext (P : Torsor L) {E : AbelianSheaf.{u, u + 1} X}
    (a b : torsorFreeSheaf P ⟶ E)
    (h : ∀ U t, a.hom.app U (torsorGenerator P U t) = b.hom.app U (torsorGenerator P U t)) :
    a = b := by
  let adj := sheafificationAdjunction (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}
  apply (adj.homEquiv (torsorFreePresheaf P) E).injective
  ext U z
  change a.hom.app U ((toSheafify _ (torsorFreePresheaf P)).app U z) =
    b.hom.app U ((toSheafify _ (torsorFreePresheaf P)).app U z)
  induction z using FreeAbelianGroup.induction_on with
  | zero => simp only [map_zero]
  | of t => exact h U t
  | neg z hz => simp only [map_neg, hz]
  | add z w hz hw => simp only [map_add, hz, hw]

/-- The free-sheaf lift sends each canonical generator to its specified section. -/
theorem torsorFreeLiftSheaf_generator (P : Torsor L) {E : AbelianSheaf.{u, u + 1} X}
    (r : P.carrier ⟶ underlyingSetSheaf E) (U : X.Etaleᵒᵖ) (t : P.carrier.obj.obj U) :
    (torsorFreeLiftSheaf P r).hom.app U (torsorGenerator P U t) = r.hom.app U t := by
  have h := congrArg (fun k => k.app U (FreeAbelianGroup.of t)) (torsorFreeLiftSheaf_unit P r)
  exact h.trans (FreeAbelianGroup.lift_apply_of _ t)

/-- The canonical inclusion of a genuine torsor lands over literal integer one. -/
theorem torsorCanonicalSetInclusion_projection (P : Torsor L)
    (U : X.Etaleᵒᵖ) (t : P.carrier.obj.obj U) :
    (torsorExtension P).g.hom.app U ((torsorCanonicalSetInclusion P).hom.app U t) =
      restrictSection (constantIntegerSheaf X) (constantIntegerOne X) U :=
  ((torsorCanonicalExtensionIso P).carrierIso.hom.hom.app U t).property

variable (f : S ⟶ X) {q : L ⟶ (directImage f).obj M}
variable {P : Torsor L} {Q : Torsor M} (r : Torsor.AdjointHom f q P Q)

/-- Compose the actual carrier map with the canonical target-extension inclusion. -/
def torsorAdjunctionSetLift :
    P.carrier ⟶ underlyingSetSheaf ((directImage f).obj (torsorExtension Q).X₂) :=
  r.map ≫ (setDirectImage f).map (torsorCanonicalSetInclusion Q)

/-- The resulting lift has the actual positive coefficient translation law. -/
theorem torsorAdjunctionSetLift_action (U : X.Etaleᵒᵖ) (a : L.obj.obj U)
    (t : P.carrier.obj.obj U) :
    (torsorAdjunctionSetLift f r).hom.app U (P.action U a t) =
      (q ≫ (directImage f).map (torsorExtension Q).f).hom.app U a +
        (show ((directImage f).obj (torsorExtension Q).X₂).obj.obj U from
          (torsorAdjunctionSetLift f r).hom.app U t) := by
  change (torsorCanonicalSetInclusion Q).hom.app ((siteBaseChange f).op.obj U)
    (r.map.hom.app U (P.action U a t)) = _
  rw [r.equivariant, torsorCanonicalSetInclusion_action]
  rfl

/-- The canonical integer map adjoint to the fixed inverse-image integer isomorphism. -/
def integerAdjunctionMap : constantIntegerSheaf X ⟶ (directImage f).obj (constantIntegerSheaf S) :=
  (inverseImageAdjunction f).homEquiv _ _ (inverseImageIntegerIso f).hom

/-- This particular adjoint integer map sends actual integer one to actual integer one. -/
theorem integerAdjunctionMap_one (U : X.Etaleᵒᵖ) :
    (integerAdjunctionMap f).hom.app U
      (restrictSection (constantIntegerSheaf X) (constantIntegerOne X) U) =
    restrictSection (constantIntegerSheaf S) (constantIntegerOne S)
      ((siteBaseChange f).op.obj U) :=
  inverseImageIntegerIso_unit_restrict_one f U

/-- The freely induced map lies over precisely the canonical integer adjunction map. -/
theorem torsorAdjunctionFreeLift_projection :
    torsorFreeLiftSheaf P (torsorAdjunctionSetLift f r) ≫
        (directImage f).map (torsorExtension Q).g =
      torsorAugmentation P ≫ integerAdjunctionMap f := by
  apply torsorFreeSheaf_hom_ext
  intro U t
  change (torsorExtension Q).g.hom.app ((siteBaseChange f).op.obj U)
      ((torsorFreeLiftSheaf P (torsorAdjunctionSetLift f r)).hom.app U (torsorGenerator P U t)) =
    (integerAdjunctionMap f).hom.app U ((torsorAugmentation P).hom.app U (torsorGenerator P U t))
  rw [torsorFreeLiftSheaf_generator, torsorGenerator_augmentation]
  erw [integerAdjunctionMap_one]
  exact torsorCanonicalSetInclusion_projection Q _ _

/-- The augmentation-kernel relation produces the actual canonical extension
map into direct image by the pushout universal property. -/
def torsorAdjunctionMiddle : (torsorExtension P).X₂ ⟶ (directImage f).obj (torsorExtension Q).X₂ :=
  pushout.desc (torsorFreeLiftSheaf P (torsorAdjunctionSetLift f r))
    (q ≫ (directImage f).map (torsorExtension Q).f)
    (torsorFreeLiftSheaf_kernel P (torsorAdjunctionSetLift f r)
      (q ≫ (directImage f).map (torsorExtension Q).f) (torsorAdjunctionSetLift_action f r))

/-- The coefficient square of the actual direct-image extension map. -/
@[simp] theorem torsorAdjunctionMiddle_inclusion :
    (torsorExtension P).f ≫ torsorAdjunctionMiddle f r =
      q ≫ (directImage f).map (torsorExtension Q).f :=
  pushout.inr_desc _ _ _

/-- The free generators have their prescribed images in the target extension. -/
@[simp] theorem torsorAdjunctionMiddle_free :
    pushout.inl (torsorKernelSheafInclusion P) (torsorDifferenceSheafMap P) ≫
      torsorAdjunctionMiddle f r = torsorFreeLiftSheaf P (torsorAdjunctionSetLift f r) :=
  pushout.inl_desc _ _ _

/-- The projection square uses the canonical integer adjunction, proved on
actual free generators rather than assumed at the cohomology level. -/
theorem torsorAdjunctionMiddle_projection :
    torsorAdjunctionMiddle f r ≫ (directImage f).map (torsorExtension Q).g =
      (torsorExtension P).g ≫ integerAdjunctionMap f := by
  apply pushout.hom_ext
  · simp only [← Category.assoc]
    erw [torsorAdjunctionMiddle_free]
    change _ = (pushout.inl (torsorAugmentationComplex P).f (torsorDifferenceSheafMap P) ≫
      CategoryTheory.Abelian.ExtensionPushout.projection (torsorAugmentationComplex P)
        (torsorDifferenceSheafMap P)) ≫
        integerAdjunctionMap f
    rw [CategoryTheory.Abelian.ExtensionPushout.inl_projection]
    exact torsorAdjunctionFreeLift_projection f r
  · simp only [← Category.assoc]
    erw [torsorAdjunctionMiddle_inclusion]
    change (q ≫ (directImage f).map (torsorExtension Q).f) ≫
      (directImage f).map (torsorExtension Q).g =
        ((torsorExtension P).f ≫ (torsorExtension P).g) ≫ integerAdjunctionMap f
    rw [ShortComplex.zero, zero_comp, Category.assoc, ← Functor.map_comp, ShortComplex.zero]
    ext U a
    rfl

/-- The coefficient map transposed through the actual inverse/direct image adjunction. -/
def torsorAdjunctionCoefficient : (inverseImage f).obj L ⟶ M :=
  ((inverseImageAdjunction f).homEquiv L M).symm q

/-- The constructed middle-sheaf map transposed through the same actual adjunction. -/
def torsorAdjunctionMiddleAdjoint :
    (inverseImage f).obj (torsorExtension P).X₂ ⟶ (torsorExtension Q).X₂ :=
  ((inverseImageAdjunction f).homEquiv _ _).symm (torsorAdjunctionMiddle f r)

/-- The coefficient square survives adjunction with its actual sheaf maps. -/
theorem torsorAdjunctionMiddleAdjoint_inclusion :
    torsorAdjunctionCoefficient f (q := q) ≫ (torsorExtension Q).f =
      (inverseImage f).map (torsorExtension P).f ≫ torsorAdjunctionMiddleAdjoint f r := by
  apply ((inverseImageAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left]
  change (inverseImageAdjunction f).homEquiv _ _
      (((inverseImageAdjunction f).homEquiv _ _).symm q) ≫ _ =
    (torsorExtension P).f ≫ (inverseImageAdjunction f).homEquiv _ _
      (((inverseImageAdjunction f).homEquiv _ _).symm (torsorAdjunctionMiddle f r))
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, torsorAdjunctionMiddle_inclusion]

/-- The projection square survives adjunction with the fixed integer transport. -/
theorem torsorAdjunctionMiddleAdjoint_projection :
    torsorAdjunctionMiddleAdjoint f r ≫ (torsorExtension Q).g =
      (torsorInverseImageExtension f P).g := by
  apply ((inverseImageAdjunction f).homEquiv _ _).injective
  change (inverseImageAdjunction f).homEquiv _ _ (torsorAdjunctionMiddleAdjoint f r ≫
      (torsorExtension Q).g) = (inverseImageAdjunction f).homEquiv _ _
        ((inverseImage f).map (torsorExtension P).g ≫ (inverseImageIntegerIso f).hom)
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left]
  change (inverseImageAdjunction f).homEquiv _ _
      (((inverseImageAdjunction f).homEquiv _ _).symm (torsorAdjunctionMiddle f r)) ≫ _ =
    (torsorExtension P).g ≫ integerAdjunctionMap f
  rw [Equiv.apply_symm_apply]
  exact torsorAdjunctionMiddle_projection f r

/-- The actual canonical extension morphism induced by the ordinary adjoint
torsor map. Both squares were constructed above. -/
def torsorAdjunctionExtensionMap : torsorInverseImageExtension f P ⟶ torsorExtension Q where
  τ₁ := torsorAdjunctionCoefficient f (q := q)
  τ₂ := torsorAdjunctionMiddleAdjoint f r
  τ₃ := 𝟙 _
  comm₁₂ := torsorAdjunctionMiddleAdjoint_inclusion f r
  comm₂₃ := by
    rw [Category.comp_id]
    exact torsorAdjunctionMiddleAdjoint_projection f r

section ExtClass
universe w w'
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
variable [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]

include r in
/-- Ordinary equivariance of the actual adjoint sheaf maps proves the exact
scheme/coefficient naturality identity of their canonical Ext classes. -/
theorem torsorExtClass_adjunction :
    coefficientMap (torsorAdjunctionCoefficient f (q := q))
      (h1Pullback f L (torsorExtClass P)) = torsorExtClass Q := by
  have h := ShortComplex.ShortExact.extClass_naturality
    (torsorInverseImageExtension_shortExact f P) (torsorExtension_shortExact Q)
    (torsorAdjunctionExtensionMap f r)
  change (torsorInverseImageExtension_shortExact f P).extClass.comp
      (Abelian.Ext.mk₀ (torsorAdjunctionCoefficient f (q := q))) (add_zero 1) =
    (Abelian.Ext.mk₀ (𝟙 (constantIntegerSheaf S))).comp
      (torsorExtension_shortExact Q).extClass (zero_add 1) at h
  rw [Abelian.Ext.mk₀_id_comp, torsorInverseImageExtension_extClass] at h
  exact h

end ExtClass
end AlgebraicGeometry.Scheme.EtaleCohomology

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 fad776fbdf0774c33d188410d4fd6c1a9c9e78de2e79aea164a2e8e003d3270e.
Definitions, hypotheses and universes are retained modulo native names. -/
