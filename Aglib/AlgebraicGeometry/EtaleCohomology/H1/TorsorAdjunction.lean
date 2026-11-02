/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Current interface basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original construction and mathematical provenance are retained below. -/
public import Aglib.CategoryTheory.Sites.Torsor.Adjunction
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.TorsorBaseChange
public import Aglib.AlgebraicGeometry.Sites.EtaleTopos

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
abbrev Torsor.AdjointHom (f : S ⟶ X) (q : L ⟶ (directImage f).obj M)
    (P : Torsor L) (Q : Torsor M) :=
  CategoryTheory.Sheaf.Torsor.AdjointHom (siteBaseChange f) q P Q

/-- Equality of morphisms out of the actual free sheaf is checked on its
canonical torsor generators. -/
theorem torsorFreeSheaf_hom_ext (P : Torsor L) {E : AbelianSheaf.{u, u + 1} X}
    (a b : torsorFreeSheaf P ⟶ E)
    (h : ∀ U t, a.hom.app U (torsorGenerator P U t) = b.hom.app U (torsorGenerator P U t)) :
    a = b :=
  CategoryTheory.Sheaf.torsorFreeSheaf_hom_ext P a b h

/-- The free-sheaf lift sends each canonical generator to its specified section. -/
theorem torsorFreeLiftSheaf_generator (P : Torsor L) {E : AbelianSheaf.{u, u + 1} X}
    (r : P.carrier ⟶ underlyingSetSheaf E) (U : X.Etaleᵒᵖ) (t : P.carrier.obj.obj U) :
    (torsorFreeLiftSheaf P r).hom.app U (torsorGenerator P U t) = r.hom.app U t :=
  CategoryTheory.Sheaf.torsorFreeLiftSheaf_generator P r U t

/-- The canonical inclusion of a genuine torsor lands over literal integer one. -/
theorem torsorCanonicalSetInclusion_projection (P : Torsor L)
    (U : X.Etaleᵒᵖ) (t : P.carrier.obj.obj U) :
    (torsorExtension P).g.hom.app U ((torsorCanonicalSetInclusion P).hom.app U t) =
      restrictSection (constantIntegerSheaf X) (constantIntegerOne X) U := by
  rw [torsorCanonicalSetInclusion_eq_generic]
  exact (CategoryTheory.Sheaf.torsorCanonicalSetInclusion_projection P U t).trans
    (restrict_constantIntegerOne (X := X) U).symm

variable (f : S ⟶ X) {q : L ⟶ (directImage f).obj M}
variable {P : Torsor L} {Q : Torsor M} (r : Torsor.AdjointHom f q P Q)

local instance nativeTorsorAdjunctionPullbackPreservesFiniteLimits :
    PreservesFiniteLimits ((siteBaseChange f).sheafPullback AddCommGrpCat.{u + 1}
      X.smallEtaleTopology S.smallEtaleTopology) :=
  inverseImage_preservesFiniteLimits f

/-- Compose the actual carrier map with the canonical target-extension inclusion. -/
abbrev torsorAdjunctionSetLift :
    P.carrier ⟶ underlyingSetSheaf ((directImage f).obj (torsorExtension Q).X₂) :=
  CategoryTheory.Sheaf.torsorAdjunctionSetLift (siteBaseChange f) r

/-- The topos direct-image lift is the original native carrier-map composition. -/
theorem torsorAdjunctionSetLift_eq_original :
    torsorAdjunctionSetLift f r =
      r.map ≫ (setDirectImage f).map (torsorCanonicalSetInclusion Q) := by
  rw [torsorCanonicalSetInclusion_eq_generic]
  rfl

/-- The resulting lift has the actual positive coefficient translation law. -/
theorem torsorAdjunctionSetLift_action (U : X.Etaleᵒᵖ) (a : L.obj.obj U)
    (t : P.carrier.obj.obj U) :
    (torsorAdjunctionSetLift f r).hom.app U (P.action U a t) =
      (q ≫ (directImage f).map (torsorExtension Q).f).hom.app U a +
        (show ((directImage f).obj (torsorExtension Q).X₂).obj.obj U from
          (torsorAdjunctionSetLift f r).hom.app U t) :=
  CategoryTheory.Sheaf.torsorAdjunctionSetLift_action (siteBaseChange f) r U a t

/-- The canonical integer map adjoint to the fixed inverse-image integer isomorphism. -/
def integerAdjunctionMap : constantIntegerSheaf X ⟶ (directImage f).obj (constantIntegerSheaf S) :=
  (inverseImageAdjunction f).homEquiv _ _ (inverseImageIntegerIso f).hom

/-- The whole native integer transpose is the generic one on the same adjunction. -/
theorem integerAdjunctionMap_eq_generic :
    integerAdjunctionMap f = (etaleAdditiveCoefficientAction f).integerAdjunctionMap := by
  unfold integerAdjunctionMap Topos.AdditiveCoefficientAction.integerAdjunctionMap
  rw [etaleAdditiveCoefficientAction_integerIso]
  rfl

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
  rw [integerAdjunctionMap_eq_generic]
  exact CategoryTheory.Sheaf.torsorAdjunctionFreeLift_projection (siteBaseChange f) r

/-- The augmentation-kernel relation produces the actual canonical extension
map into direct image by the pushout universal property. -/
abbrev torsorAdjunctionMiddle : (torsorExtension P).X₂ ⟶ (directImage f).obj (torsorExtension
  Q).X₂ :=
  CategoryTheory.Sheaf.torsorAdjunctionMiddle (siteBaseChange f) r

/-- The coefficient square of the actual direct-image extension map. -/
theorem torsorAdjunctionMiddle_inclusion :
    (torsorExtension P).f ≫ torsorAdjunctionMiddle f r =
      q ≫ (directImage f).map (torsorExtension Q).f :=
  CategoryTheory.Sheaf.torsorAdjunctionMiddle_inclusion (siteBaseChange f) r

/-- The free generators have their prescribed images in the target extension. -/
theorem torsorAdjunctionMiddle_free :
    pushout.inl (torsorKernelSheafInclusion P) (torsorDifferenceSheafMap P) ≫
      torsorAdjunctionMiddle f r = torsorFreeLiftSheaf P (torsorAdjunctionSetLift f r) :=
  CategoryTheory.Sheaf.torsorAdjunctionMiddle_free (siteBaseChange f) r

/-- The projection square uses the canonical integer adjunction, proved on
actual free generators rather than assumed at the cohomology level. -/
theorem torsorAdjunctionMiddle_projection :
    torsorAdjunctionMiddle f r ≫ (directImage f).map (torsorExtension Q).g =
      (torsorExtension P).g ≫ integerAdjunctionMap f := by
  rw [integerAdjunctionMap_eq_generic]
  exact CategoryTheory.Sheaf.torsorAdjunctionMiddle_projection (siteBaseChange f) r

/-- The coefficient map transposed through the actual inverse/direct image adjunction. -/
abbrev torsorAdjunctionCoefficient : (inverseImage f).obj L ⟶ M :=
  CategoryTheory.Sheaf.torsorAdjunctionCoefficient.{u + 1, u, u + 1, u, u + 1}
    (siteBaseChange f) (q := q)

/-- The constructed middle-sheaf map transposed through the same actual adjunction. -/
abbrev torsorAdjunctionMiddleAdjoint :
    (inverseImage f).obj (torsorExtension P).X₂ ⟶ (torsorExtension Q).X₂ :=
  CategoryTheory.Sheaf.torsorAdjunctionMiddleAdjoint.{u + 1, u, u + 1, u, u + 1}
    (siteBaseChange f) r

/-- The coefficient square survives adjunction with its actual sheaf maps. -/
theorem torsorAdjunctionMiddleAdjoint_inclusion :
    torsorAdjunctionCoefficient f (q := q) ≫ (torsorExtension Q).f =
      (inverseImage f).map (torsorExtension P).f ≫ torsorAdjunctionMiddleAdjoint f r :=
  CategoryTheory.Sheaf.torsorAdjunctionMiddleAdjoint_inclusion (siteBaseChange f) r

/-- The projection square survives adjunction with the fixed integer transport. -/
theorem torsorAdjunctionMiddleAdjoint_projection :
    torsorAdjunctionMiddleAdjoint f r ≫ (torsorExtension Q).g =
      (torsorInverseImageExtension f P).g :=
  (CategoryTheory.Sheaf.torsorAdjunctionMiddleAdjoint_projection (siteBaseChange f) r).trans
    (torsorInverseImageProjection_eq_generic f P).symm

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
  rw [h1Pullback_eq_generic]
  exact CategoryTheory.Sheaf.torsorExtClass_adjunction (siteBaseChange f) r

end ExtClass
end AlgebraicGeometry.Scheme.EtaleCohomology

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 fad776fbdf0774c33d188410d4fd6c1a9c9e78de2e79aea164a2e8e003d3270e.
Definitions, hypotheses and universes are retained modulo native names. -/
