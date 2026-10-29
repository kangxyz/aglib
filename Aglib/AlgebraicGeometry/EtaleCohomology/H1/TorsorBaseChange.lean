/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Current interface basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original construction and mathematical provenance are retained below. -/
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.TorsorPullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.EtaleRestriction
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Literal set-sheaf fibres under actual scheme inverse image

Construction for `K2-018#eq:k2018-pointed-character`, frozen basis
`7f86e4a1763cc4ec35e9b0a8acd659750355a0de`. This layer identifies the
inverse-image-extension fibre with actual set-sheaf inverse image, using
finite-limit preservation and the canonical integer-one transport.
-/

@[expose] public section

noncomputable section
set_option maxRecDepth 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open MonoidalCategory CartesianMonoidalCategory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
universe u w w'
attribute [local instance] hasSheafifyLarge
variable {X : Scheme.{u}}

/-- The concrete terminal sheaf of sets. -/
abbrev setTerminal (X : Scheme.{u}) : SetSheaf X := 𝟙_ (SetSheaf X)

/-- A global abelian section as an actual morphism of set sheaves. -/
abbrev globalSectionSetMap (L : AbelianSheaf.{u, u + 1} X)
    (z : L.obj.obj (op (etaleTerminal X))) : setTerminal X ⟶ underlyingSetSheaf L :=
  (Topos.globalPointTerminalEquiv (etaleTerminalIsTerminal X) (underlyingSetSheaf L)).symm z

/-- The actual integer-one section as a sheaf morphism. -/
abbrev integerOneSetMap (X : Scheme.{u}) :
    setTerminal X ⟶ underlyingSetSheaf (constantIntegerSheaf X) :=
  globalSectionSetMap (constantIntegerSheaf X) (constantIntegerOne X)

variable (S : ShortComplex (AbelianSheaf.{u, u + 1} X))
variable (z : S.X₃.obj.obj (op (etaleTerminal X)))

/-- Actual inclusion of the fibre subsheaf in its middle sheaf. -/
abbrev extensionFiberSetInclusion :
    extensionFiberSheaf S z ⟶ underlyingSetSheaf S.X₂ :=
  CategoryTheory.Sheaf.extensionFiberInclusion S (globalSectionSetMap S.X₃ z)

/-- The defining sheaf-theoretic fibre square commutes. -/
theorem extensionFiberSet_condition :
    extensionFiberSetInclusion S z ≫ (underlyingSetFunctor X).map S.g =
      toUnit (extensionFiberSheaf S z) ≫ globalSectionSetMap S.X₃ z := by
  ext U t
  exact t.property

/-- The actual fibre subsheaf satisfies the pullback universal property. -/
def extensionFiberSetIsLimit :
    IsLimit (PullbackCone.mk (extensionFiberSetInclusion S z)
      (toUnit (extensionFiberSheaf S z)) (extensionFiberSet_condition S z)) := by
  refine IsLimit.ofIsoLimit
    (CategoryTheory.Sheaf.extensionFiberPullbackIsLimit S (globalSectionSetMap S.X₃ z)) ?_
  refine PullbackCone.ext (Iso.refl _) ?_ ?_
  · simp only [Iso.refl_hom, Category.id_comp]
    rfl
  · exact toUnit_unique _ _

section IntegerTransport
variable {S : Scheme.{u}} (f : S ⟶ X)

/-- Underlying-set transport in the inverse-image direction. -/
abbrev setInverseImageAbelianIso (L : AbelianSheaf.{u, u + 1} X) :
    (setInverseImage f).obj (underlyingSetSheaf L) ≅
      underlyingSetSheaf ((inverseImage f).obj L) :=
  ((inverseImageUnderlyingSetIso f).app L).symm

/-- The underlying-set inverse-image comparison also respects the unit in
the direction used to compare actual set-sheaf fibres. -/
theorem setInverseImageAbelianIso_unit (L : AbelianSheaf.{u, u + 1} X) :
    (setInverseImageAdjunction f).unit.app ((underlyingSetFunctor X).obj L) ≫
      (setDirectImage f).map ((inverseImageUnderlyingSetIso f).inv.app L) =
        (underlyingSetFunctor X).map ((inverseImageAdjunction f).unit.app L) := by
  have h := Topos.AdditiveCoefficientAction.leftComparison_unit
    (etaleAdditiveCoefficientAction f) L
  rw [etaleAdditiveCoefficientAction_leftComparison] at h
  exact h.symm.trans (Category.comp_id _)

/-- The actual image of the constant integer sheaf, including its forgetful comparison. -/
abbrev setInverseImageIntegerIso :
    (setInverseImage f).obj (underlyingSetSheaf (constantIntegerSheaf X)) ≅
      underlyingSetSheaf (constantIntegerSheaf S) :=
  setInverseImageAbelianIso f (constantIntegerSheaf X) ≪≫
    (underlyingSetFunctor S).mapIso (inverseImageIntegerIso f)

/-- The original terminal formula presents the intrinsic integer-one arrow. -/
theorem integerOneSetMap_eq_generic (X : Scheme.{u}) :
    integerOneSetMap X = CategoryTheory.Sheaf.constantIntegerOne X.smallEtaleTopology :=
  constantIntegerOne_asGlobalPoint (X := X)

/-- Finite-limit inverse image preserves the original integer-one point. -/
theorem setInverseImage_integerOne :
    (setInverseImage f).map (integerOneSetMap X) ≫ (setInverseImageIntegerIso f).hom =
      toUnit ((setInverseImage f).obj (setTerminal X)) ≫ integerOneSetMap S := by
  have h := Topos.AdditiveCoefficientAction.integerOne_image (etaleAdditiveCoefficientAction f)
  rw [etaleAdditiveCoefficientAction_leftComparison,
    etaleAdditiveCoefficientAction_integerIso, ← integerOneSetMap_eq_generic X,
    ← integerOneSetMap_eq_generic S] at h
  exact h.trans (congrArg (fun q => q ≫ integerOneSetMap S) (toUnit_unique _ _))

/-- The same native image equation retains the literal original unit-one formula. -/
theorem setInverseImageIntegerIso_unit_one :
    integerOneSetMap X ≫
        (setInverseImageAdjunction f).unit.app (underlyingSetSheaf (constantIntegerSheaf X)) ≫
        (setDirectImage f).map (setInverseImageIntegerIso f).hom =
      (setDirectImage f).map (integerOneSetMap S) := by
  have h := congrArg ((setInverseImageAdjunction f).homEquiv _ _)
    (setInverseImage_integerOne f)
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc] at h
  have hn := (setInverseImageAdjunction f).unit.naturality (integerOneSetMap X)
  change integerOneSetMap X ≫
      (setInverseImageAdjunction f).unit.app (underlyingSetSheaf (constantIntegerSheaf X)) =
    (setInverseImageAdjunction f).unit.app (setTerminal X) ≫
      (setDirectImage f).map ((setInverseImage f).map (integerOneSetMap X)) at hn
  have ht : (setInverseImageAdjunction f).unit.app (setTerminal X) ≫
      (setDirectImage f).map (toUnit ((setInverseImage f).obj (setTerminal X))) =
        𝟙 (setTerminal X) := toUnit_unique _ _
  rw [← hn, ht, Category.id_comp] at h
  simpa only [Category.assoc] using h

end IntegerTransport

namespace Torsor
variable {L : AbelianSheaf.{u, u + 1} X} (P : Torsor L) {T : SetSheaf X}

/-- Transport along an actual sheaf isomorphism keeps the geometric action explicit. -/
abbrev transportCarrier (e : T ≅ P.carrier) : Torsor L :=
  CategoryTheory.Sheaf.Torsor.transportCarrier P e

/-- Carrier transport is the original equivariant torsor isomorphism. -/
abbrev transportCarrierIso (e : T ≅ P.carrier) : Iso (P.transportCarrier e) P :=
  CategoryTheory.Sheaf.Torsor.transportCarrierIso P e

end Torsor

section FibrePullback
variable {S : Scheme.{u}} (f : S ⟶ X)
variable {L : AbelianSheaf.{u, u + 1} X} (P : Torsor L)

local instance nativeTorsorImagePullbackPreservesFiniteLimits :
    PreservesFiniteLimits ((siteBaseChange f).sheafPullback AddCommGrpCat.{u + 1}
      X.smallEtaleTopology S.smallEtaleTopology) :=
  inverseImage_preservesFiniteLimits f

/-- The actual finite-limit terminal transport for set-sheaf inverse image. -/
def setInverseImageTerminalIso :
    (setInverseImage f).obj (setTerminal X) ≅ setTerminal S :=
  ((isTerminalTensorUnit (C := SetSheaf X)).isTerminalObj (setInverseImage f)).uniqueUpToIso
    isTerminalTensorUnit

/-- The projection of the inverse image of the original extension fibre. -/
def inverseImageFiberSetInclusion :
    (setInverseImage f).obj (extensionFiberSheaf (torsorExtension P) (constantIntegerOne X)) ⟶
      underlyingSetSheaf ((inverseImage f).obj (torsorExtension P).X₂) :=
  (setInverseImage f).map (extensionFiberSetInclusion (torsorExtension P) (constantIntegerOne X)) ≫
    (setInverseImageAbelianIso f (torsorExtension P).X₂).hom

/-- The image of the original fibre square is literally the transported
extension's fibre square after the canonical integer-one comparison. -/
theorem inverseImageFiberSetIsPullback :
    IsPullback (inverseImageFiberSetInclusion f P)
      (toUnit ((setInverseImage f).obj
        (extensionFiberSheaf (torsorExtension P) (constantIntegerOne X))))
      ((underlyingSetFunctor S).map (torsorInverseImageExtension f P).g)
      (integerOneSetMap S) := by
  let square (z : Topos.GlobalPoint (underlyingSetSheaf (constantIntegerSheaf X)))
      (p : (inverseImage f).obj (torsorExtension P).X₂ ⟶ constantIntegerSheaf S)
      (c : (setInverseImage f).obj (underlyingSetSheaf (torsorExtension P).X₂) ⟶
        underlyingSetSheaf ((inverseImage f).obj (torsorExtension P).X₂))
      (z' : Topos.GlobalPoint (underlyingSetSheaf (constantIntegerSheaf S))) : Prop :=
    IsPullback
      ((setInverseImage f).map (CategoryTheory.Sheaf.extensionFiberInclusion
        (torsorExtension P) z) ≫ c)
      (toUnit ((setInverseImage f).obj
        (CategoryTheory.Sheaf.extensionFiberSheaf (torsorExtension P) z)))
      ((underlyingSetFunctor S).map p) z'
  have h : square (CategoryTheory.Sheaf.constantIntegerOne X.smallEtaleTopology)
      (CategoryTheory.Sheaf.torsorInverseImageProjection (etaleAdditiveCoefficientAction f) P)
      ((etaleAdditiveCoefficientAction f).leftComparison.app (torsorExtension P).X₂)
      (CategoryTheory.Sheaf.constantIntegerOne S.smallEtaleTopology) := by
    let T : SetSheaf S := (setInverseImage f).obj
      (CategoryTheory.Sheaf.extensionFiberSheaf (torsorExtension P)
        (CategoryTheory.Sheaf.constantIntegerOne X.smallEtaleTopology))
    let j : T ⟶ underlyingSetSheaf ((inverseImage f).obj (torsorExtension P).X₂) :=
      CategoryTheory.Sheaf.inverseImageFiberSetInclusion (etaleAdditiveCoefficientAction f) P
    let p : (inverseImage f).obj (torsorExtension P).X₂ ⟶ constantIntegerSheaf S :=
      CategoryTheory.Sheaf.torsorInverseImageProjection (etaleAdditiveCoefficientAction f) P
    let predicate (t : T ⟶ setTerminal S) : Prop :=
      IsPullback j t ((underlyingSetFunctor S).map p)
        (CategoryTheory.Sheaf.constantIntegerOne S.smallEtaleTopology)
    have ht : (Topos.terminalSheafIsTerminal S.smallEtaleTopology).from T = toUnit T :=
      toUnit_unique (C := SetSheaf S) _ _
    have hg : predicate ((Topos.terminalSheafIsTerminal S.smallEtaleTopology).from T) :=
      CategoryTheory.Sheaf.inverseImageFiberSetIsPullback (etaleAdditiveCoefficientAction f) P
    exact Eq.mp (congrArg predicate ht) hg
  have hc := congrArg (fun q => q.app (torsorExtension P).X₂)
    (etaleAdditiveCoefficientAction_leftComparison f)
  rw [← constantIntegerOne_asGlobalPoint (X := X),
    ← constantIntegerOne_asGlobalPoint (X := S),
    ← torsorInverseImageProjection_eq_generic f P, hc] at h
  exact h

/-- The fibre of the inverse-image extension is canonically the actual set
inverse image of the original fibre. -/
def inverseImageExtensionFiberIso :
    (setInverseImage f).obj (extensionFiberSheaf (torsorExtension P) (constantIntegerOne X)) ≅
      (torsorInverseImageFiber f P).carrier :=
  (inverseImageFiberSetIsPullback f P).isoIsPullback _ _
    (IsPullback.of_isLimit (extensionFiberSetIsLimit
      (torsorInverseImageExtension f P) (constantIntegerOne S)))

/-- Its map to the middle sheaf is the image of the literal original inclusion. -/
theorem inverseImageExtensionFiberIso_hom_inclusion :
    (inverseImageExtensionFiberIso f P).hom ≫
      extensionFiberSetInclusion (torsorInverseImageExtension f P) (constantIntegerOne S) =
        inverseImageFiberSetInclusion f P :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- The canonical extension-fibre presentation identifies actual sheaf inverse
image of a torsor with the constructed inverse-image-extension torsor. -/
def torsorSetInverseImageIso :
    (setInverseImage f).obj P.carrier ≅ (torsorInverseImageFiber f P).carrier :=
  (setInverseImage f).mapIso (torsorCanonicalExtensionIso P).carrierIso ≪≫
    inverseImageExtensionFiberIso f P

/-- The original torsor's canonical map into its extension middle sheaf. -/
def torsorCanonicalSetInclusion : P.carrier ⟶ underlyingSetSheaf (torsorExtension P).X₂ :=
  (torsorCanonicalExtensionIso P).carrierIso.hom ≫
    extensionFiberSetInclusion (torsorExtension P) (constantIntegerOne X)

/-- Both presentations retain the identical original free-generator inclusion. -/
theorem torsorCanonicalSetInclusion_eq_generic :
    torsorCanonicalSetInclusion P = CategoryTheory.Sheaf.torsorCanonicalSetInclusion P := by
  ext U t
  rfl

/-- The canonical embedding has the original positive coefficient action. -/
theorem torsorCanonicalSetInclusion_action (U : X.Etaleᵒᵖ) (a : L.obj.obj U)
    (t : P.carrier.obj.obj U) :
    (torsorCanonicalSetInclusion P).hom.app U (P.action U a t) =
      (torsorExtension P).f.hom.app U a +
        (show (torsorExtension P).X₂.obj.obj U from
          (torsorCanonicalSetInclusion P).hom.app U t) := by
  rw [torsorCanonicalSetInclusion_eq_generic]
  exact CategoryTheory.Sheaf.torsorCanonicalSetInclusion_action P U a t

/-- The carrier comparison's middle-sheaf projection is the actual image of
the original canonical embedding. -/
theorem torsorSetInverseImageIso_hom_inclusion :
    (torsorSetInverseImageIso f P).hom ≫
      extensionFiberSetInclusion (torsorInverseImageExtension f P) (constantIntegerOne S) =
        (setInverseImage f).map (torsorCanonicalSetInclusion P) ≫
          (setInverseImageAbelianIso f (torsorExtension P).X₂).hom := by
  change ((setInverseImage f).map (torsorCanonicalExtensionIso P).carrierIso.hom ≫
      (inverseImageExtensionFiberIso f P).hom) ≫ _ = _
  rw [Category.assoc, inverseImageExtensionFiberIso_hom_inclusion]
  exact (Functor.map_comp_assoc _ _ _ _).symm

/-- The original pullback comparison retains the entire generic middle-sheaf map. -/
theorem torsorSetInverseImageIso_inclusion_eq_generic :
    (torsorSetInverseImageIso f P).hom ≫
        extensionFiberSetInclusion (torsorInverseImageExtension f P) (constantIntegerOne S) =
      (CategoryTheory.Sheaf.torsorSetInverseImageIso (etaleAdditiveCoefficientAction f) P).hom ≫
        CategoryTheory.Sheaf.extensionFiberInclusion
          (CategoryTheory.Sheaf.torsorInverseImageExtension (etaleAdditiveCoefficientAction f) P)
          (CategoryTheory.Sheaf.constantIntegerOne S.smallEtaleTopology) := by
  rw [torsorSetInverseImageIso_hom_inclusion,
    CategoryTheory.Sheaf.torsorSetInverseImageIso_hom_inclusion,
    torsorCanonicalSetInclusion_eq_generic,
    etaleAdditiveCoefficientAction_leftComparison]
  rfl

/-- The canonical unit square for the actual torsor carrier and its embedding. -/
theorem torsorSetInverseImageIso_unit_inclusion :
    (setInverseImageAdjunction f).unit.app P.carrier ≫
      (setDirectImage f).map ((torsorSetInverseImageIso f P).hom ≫
        extensionFiberSetInclusion (torsorInverseImageExtension f P) (constantIntegerOne S)) =
      torsorCanonicalSetInclusion P ≫
        (underlyingSetFunctor X).map ((inverseImageAdjunction f).unit.app (torsorExtension P).X₂)
          := by
  let E := (torsorExtension P).X₂
  let k : underlyingSetSheaf E ⟶ underlyingSetSheaf ((directImage f).obj
      ((inverseImage f).obj E)) :=
    (underlyingSetFunctor X).map ((inverseImageAdjunction f).unit.app E)
  let j : P.carrier ⟶ underlyingSetSheaf E :=
    CategoryTheory.Sheaf.torsorCanonicalSetInclusion P
  have hi : j = torsorCanonicalSetInclusion P := (torsorCanonicalSetInclusion_eq_generic P).symm
  have h := CategoryTheory.Sheaf.torsorSetInverseImageIso_unit_inclusion
    (etaleAdditiveCoefficientAction f) P
  have hh := congrArg
    (fun q : (setInverseImage f).obj P.carrier ⟶
      underlyingSetSheaf ((inverseImage f).obj E) =>
        (setInverseImageAdjunction f).unit.app P.carrier ≫ (setDirectImage f).map q)
    (torsorSetInverseImageIso_inclusion_eq_generic f P)
  exact hh.trans (h.trans ((congrArg (fun q => j ≫ q) (Category.comp_id k)).trans
    (congrArg (fun q : P.carrier ⟶ underlyingSetSheaf E => q ≫ k) hi)))

/-- Actual scheme inverse image of a sheaf torsor. Its carrier is definitionally
the set-sheaf inverse image; its action comes from the canonical extension fibre. -/
def torsorInverseImage : Torsor ((inverseImage f).obj L) :=
  (torsorInverseImageFiber f P).transportCarrier (torsorSetInverseImageIso f P)

/-- The actual pullback torsor is identified equivariantly with the pulled-back
extension fibre; no torsor-classification premise is used. -/
def torsorInverseImageFiberIso :
    Torsor.Iso (torsorInverseImage f P) (torsorInverseImageFiber f P) :=
  (torsorInverseImageFiber f P).transportCarrierIso (torsorSetInverseImageIso f P)

/-- The literal original action equals the generic action on the very same Set image carrier. -/
theorem torsorInverseImage_action_eq_generic (U : S.Etaleᵒᵖ)
    (a : ((inverseImage f).obj L).obj.obj U)
    (t : ((setInverseImage f).obj P.carrier).obj.obj U) :
    (torsorInverseImage f P).action U a t =
      (CategoryTheory.Sheaf.torsorInverseImage (etaleAdditiveCoefficientAction f) P).action U a t
        := by
  let e := torsorSetInverseImageIso f P
  let Qg := CategoryTheory.Sheaf.torsorInverseImage (etaleAdditiveCoefficientAction f) P
  have hp (x : ((setInverseImage f).obj P.carrier).obj.obj U) :=
    congrArg (fun q => q.hom.app U x) (torsorSetInverseImageIso_inclusion_eq_generic f P)
  apply (ConcreteCategory.bijective_of_isIso (e.hom.hom.app U)).injective
  apply Subtype.ext
  have ha := congrArg Subtype.val ((torsorInverseImageFiberIso f P).equivariant U a t)
  have hag := CategoryTheory.Sheaf.torsorInverseImage_inclusion_action
    (etaleAdditiveCoefficientAction f) P U a t
  exact ha.trans ((congrArg
    (fun x : ((inverseImage f).obj (torsorExtension P).X₂).obj.obj U =>
      ((inverseImage f).map (torsorExtension P).f).hom.app U a + x) (hp t)).trans
        (hag.symm.trans (hp (Qg.action U a t)).symm))

/-- The two presentations agree by identity on their original common carrier. -/
def torsorInverseImageIsoGeneric :
    Torsor.Iso (torsorInverseImage f P)
      (CategoryTheory.Sheaf.torsorInverseImage (etaleAdditiveCoefficientAction f) P) where
  carrierIso := Iso.refl _
  equivariant := torsorInverseImage_action_eq_generic f P

/-- The actual inverse-image unit is equivariant for the actual coefficient
unit. This identifies the transported action with the sheaf inverse-image
action, including its coefficient variance and positive sign. -/
theorem torsorInverseImage_unit_equivariant (U : X.Etaleᵒᵖ)
    (a : L.obj.obj U) (t : P.carrier.obj.obj U) :
    ((setInverseImageAdjunction f).unit.app P.carrier).hom.app U (P.action U a t) =
      (torsorInverseImage f P).action ((siteBaseChange f).op.obj U)
        (((inverseImageAdjunction f).unit.app L).hom.app U a)
        (((setInverseImageAdjunction f).unit.app P.carrier).hom.app U t) := by
  have h := CategoryTheory.Sheaf.torsorInverseImage_unit_equivariant
    (siteBaseChange f) X.smallEtaleTopology S.smallEtaleTopology P U a t
  exact h.trans (torsorInverseImage_action_eq_generic f P _ _ _).symm

/-- Actual set-sheaf pullback has the actual contravariant Ext class. -/
theorem torsorExtClass_inverseImage
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)] [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)] :
    torsorExtClass (torsorInverseImage f P) = h1Pullback f L (torsorExtClass P) := by
  rw [torsorExtClass_iso (torsorInverseImageIsoGeneric f P), h1Pullback_eq_generic]
  exact CategoryTheory.Sheaf.torsorExtClass_inverseImage (etaleAdditiveCoefficientAction f) P

end FibrePullback

end AlgebraicGeometry.Scheme.EtaleCohomology

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 fb3a3b171fc976533443eafb7a028f5bcb42c44567b2fdb418789a46ed665aa7.
Definitions, hypotheses and universes are retained modulo native names. -/
