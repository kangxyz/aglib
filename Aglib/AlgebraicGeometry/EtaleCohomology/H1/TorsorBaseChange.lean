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
def globalSectionSetMap (L : AbelianSheaf.{u, u + 1} X)
    (z : L.obj.obj (op (etaleTerminal X))) : setTerminal X ⟶ underlyingSetSheaf L :=
  ⟨{ app U := TypeCat.ofHom (fun _ => restrictSection L z U)
     naturality {U V} f := by
       ext t
       exact (restrictSection_naturality L z f).symm }⟩

/-- The actual integer-one section as a sheaf morphism. -/
abbrev integerOneSetMap (X : Scheme.{u}) :
    setTerminal X ⟶ underlyingSetSheaf (constantIntegerSheaf X) :=
  globalSectionSetMap (constantIntegerSheaf X) (constantIntegerOne X)

variable (S : ShortComplex (AbelianSheaf.{u, u + 1} X))
variable (z : S.X₃.obj.obj (op (etaleTerminal X)))

/-- Actual inclusion of the fibre subsheaf in its middle sheaf. -/
noncomputable def extensionFiberSetInclusion :
    extensionFiberSheaf S z ⟶ underlyingSetSheaf S.X₂ :=
  ⟨{ app _ := TypeCat.ofHom Subtype.val
     naturality {_ _} _ := rfl }⟩

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
  refine PullbackCone.IsLimit.mk _ (fun q => ?_) ?_ ?_ ?_
  · exact ⟨{
      app U := TypeCat.ofHom (fun t => ⟨q.fst.hom.app U t, by
        have h := congrArg (fun r => r.hom.app U t) q.condition
        exact h⟩)
      naturality {U V} f := by
        ext t
        apply Subtype.ext
        exact ConcreteCategory.congr_hom (q.fst.hom.naturality f) t }⟩
  · intro q
    ext U t
    rfl
  · intro q
    exact toUnit_unique _ _
  · intro q m hm₁ hm₂
    ext U t
    apply Subtype.ext
    exact congrArg (fun r => r.hom.app U t) hm₁

section IntegerTransport
variable {S : Scheme.{u}} (f : S ⟶ X)

/-- The constant-integer inverse-image comparison carries the adjunction image
of the literal integer one to literal integer one. -/
theorem inverseImageIntegerIso_unit_one :
    (inverseImageIntegerIso f).hom.hom.app
        (op ((siteBaseChange f).obj (etaleTerminal X)))
      (((inverseImageAdjunction f).unit.app (constantIntegerSheaf X)).hom.app
        (op (etaleTerminal X)) (constantIntegerOne X)) =
    restrictSection (constantIntegerSheaf S) (constantIntegerOne S)
      (op ((siteBaseChange f).obj (etaleTerminal X))) := by
  let hT := etaleTerminalIsTerminal X
  let cAdj := constantSheafAdj (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1} hT
  let sAdj := constantSheafAdj (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}
    (hT.isTerminalObj (siteBaseChange f))
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (cAdj.comp (inverseImageAdjunction f)) sAdj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  have he := ConcreteCategory.congr_hom h (ULift.up (1 : ℤ))
  change (inverseImageIntegerIso f).hom.hom.app _
    (((inverseImageAdjunction f).unit.app (constantIntegerSheaf X)).hom.app _
      (constantIntegerOne X)) = _ at he
  rw [restrict_constantIntegerOne]
  exact he

/-- Naturality extends the literal integer-one unit computation to each test object. -/
theorem inverseImageIntegerIso_unit_restrict_one (U : X.Etaleᵒᵖ) :
    (inverseImageIntegerIso f).hom.hom.app ((siteBaseChange f).op.obj U)
      (((inverseImageAdjunction f).unit.app (constantIntegerSheaf X)).hom.app U
        (restrictSection (constantIntegerSheaf X) (constantIntegerOne X) U)) =
    restrictSection (constantIntegerSheaf S) (constantIntegerOne S)
      ((siteBaseChange f).op.obj U) := by
  let r := (inverseImageAdjunction f).unit.app (constantIntegerSheaf X) ≫
    (directImage f).map (inverseImageIntegerIso f).hom
  have h := ConcreteCategory.congr_hom
    (r.hom.naturality ((etaleTerminalIsTerminal X).from U.unop).op)
    (constantIntegerOne X)
  change r.hom.app U (restrictSection (constantIntegerSheaf X) (constantIntegerOne X) U) =
    (constantIntegerSheaf S).obj.map
      ((siteBaseChange f).map ((etaleTerminalIsTerminal X).from U.unop)).op
      (r.hom.app (op (etaleTerminal X)) (constantIntegerOne X)) at h
  change r.hom.app U _ = _
  rw [h]
  change (constantIntegerSheaf S).obj.map _
    ((inverseImageIntegerIso f).hom.hom.app _
      (((inverseImageAdjunction f).unit.app _).hom.app _ (constantIntegerOne X))) = _
  exact (congrArg ((constantIntegerSheaf S).obj.map
    ((siteBaseChange f).map ((etaleTerminalIsTerminal X).from U.unop)).op)
    (inverseImageIntegerIso_unit_one f)).trans (restrictSection_naturality (constantIntegerSheaf
      S) (constantIntegerOne S) _)

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
  rw [← inverseImageUnderlyingSetIso_unit]
  rw [Category.assoc, ← Functor.map_comp, (inverseImageUnderlyingSetIso f).hom_inv_id_app]
  exact Category.comp_id _

/-- The actual image of the constant integer sheaf, including its forgetful comparison. -/
abbrev setInverseImageIntegerIso :
    (setInverseImage f).obj (underlyingSetSheaf (constantIntegerSheaf X)) ≅
      underlyingSetSheaf (constantIntegerSheaf S) :=
  setInverseImageAbelianIso f (constantIntegerSheaf X) ≪≫
    (underlyingSetFunctor S).mapIso (inverseImageIntegerIso f)

/-- The canonical set-sheaf comparison respects literal integer one at the unit. -/
theorem setInverseImageIntegerIso_unit_one :
    integerOneSetMap X ≫
        (setInverseImageAdjunction f).unit.app (underlyingSetSheaf (constantIntegerSheaf X)) ≫
        (setDirectImage f).map (setInverseImageIntegerIso f).hom =
      (setDirectImage f).map (integerOneSetMap S) := by
  ext U t
  let e := (inverseImageUnderlyingSetIso f).app (constantIntegerSheaf X)
  have hu := congrArg (fun q => q.hom.app U
      (restrictSection (constantIntegerSheaf X) (constantIntegerOne X) U))
    (inverseImageUnderlyingSetIso_unit f (constantIntegerSheaf X))
  have hi := congrArg (fun q => q.hom.app ((siteBaseChange f).op.obj U)
      (((inverseImageAdjunction f).unit.app (constantIntegerSheaf X)).hom.app U
        (restrictSection (constantIntegerSheaf X) (constantIntegerOne X) U)))
    e.hom_inv_id
  change e.inv.hom.app ((siteBaseChange f).op.obj U)
    (e.hom.hom.app ((siteBaseChange f).op.obj U) _) = _ at hi
  have he := congrArg (fun v => (inverseImageIntegerIso f).hom.hom.app
      ((siteBaseChange f).op.obj U) (e.inv.hom.app ((siteBaseChange f).op.obj U) v)) hu.symm
  exact he.trans ((congrArg ((inverseImageIntegerIso f).hom.hom.app
    ((siteBaseChange f).op.obj U)) hi).trans (inverseImageIntegerIso_unit_restrict_one f U))

/-- Finite-limit inverse image preserves the actual section one, not merely
some point of the transported constant sheaf. -/
theorem setInverseImage_integerOne :
    (setInverseImage f).map (integerOneSetMap X) ≫ (setInverseImageIntegerIso f).hom =
      toUnit ((setInverseImage f).obj (setTerminal X)) ≫ integerOneSetMap S := by
  apply ((setInverseImageAdjunction f).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  have hn := (setInverseImageAdjunction f).unit.naturality (integerOneSetMap X)
  change integerOneSetMap X ≫
      (setInverseImageAdjunction f).unit.app (underlyingSetSheaf (constantIntegerSheaf X)) =
    (setInverseImageAdjunction f).unit.app (setTerminal X) ≫
      (setDirectImage f).map ((setInverseImage f).map (integerOneSetMap X)) at hn
  rw [← hn, Category.assoc]
  have ht : (setInverseImageAdjunction f).unit.app (setTerminal X) ≫
      (setDirectImage f).map (toUnit ((setInverseImage f).obj (setTerminal X))) =
      𝟙 (setTerminal X) := toUnit_unique _ _
  erw [setInverseImageIntegerIso_unit_one, ht, Category.id_comp]

end IntegerTransport

namespace Torsor
variable {L : AbelianSheaf.{u, u + 1} X} (P : Torsor L) {T : SetSheaf X}

/-- Transport along an actual sheaf isomorphism keeps the geometric action explicit. -/
def transportCarrier (e : T ≅ P.carrier) : Torsor L where
  carrier := T
  action U a t := e.inv.hom.app U (P.action U a (e.hom.hom.app U t))
  zero_action U t := by
    rw [P.zero_action]
    exact congrArg (fun r => r.hom.app U t) e.hom_inv_id
  add_action U a b t := by
    have h := congrArg (fun r => r.hom.app U (P.action U b (e.hom.hom.app U t)))
      e.inv_hom_id
    change e.hom.hom.app U (e.inv.hom.app U _) = _ at h
    rw [h, P.add_action]
    rfl
  naturality {U V} g a t := by
    have he := ConcreteCategory.congr_hom (e.inv.hom.naturality g)
      (P.action U a (e.hom.hom.app U t))
    have hh := ConcreteCategory.congr_hom (e.hom.hom.naturality g) t
    exact he.symm.trans (congrArg (e.inv.hom.app V)
      ((P.naturality g a _).trans (congrArg (P.action V (L.obj.map g a)) hh.symm)))
  unique_transport U s t := by
    obtain ⟨a, ha, hu⟩ := P.unique_transport U (e.hom.hom.app U s) (e.hom.hom.app U t)
    refine ⟨a, ?_, ?_⟩
    · exact (congrArg (e.inv.hom.app U) ha).trans
        (congrArg (fun r => r.hom.app U t) e.hom_inv_id)
    · intro b hb
      apply hu b
      exact (congrArg (fun r => r.hom.app U (P.action U b (e.hom.hom.app U s)))
        e.inv_hom_id).symm.trans (congrArg (e.hom.hom.app U) hb)
  locally_nonempty U := by
    refine (Scheme.smallEtaleTopology X).superset_covering ?_ (P.locally_nonempty U)
    intro V g ht
    exact ht.map (e.inv.hom.app (op V))

/-- Carrier transport is an actual equivariant torsor isomorphism. -/
def transportCarrierIso (e : T ≅ P.carrier) : Iso (P.transportCarrier e) P where
  carrierIso := e
  equivariant U a t := congrArg (fun r => r.hom.app U
    (P.action U a (e.hom.hom.app U t))) e.inv_hom_id

end Torsor

section FibrePullback
variable {S : Scheme.{u}} (f : S ⟶ X)
variable {L : AbelianSheaf.{u, u + 1} X} (P : Torsor L)

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
  have h := (setInverseImage f).map_isPullback
    (IsPullback.of_isLimit (extensionFiberSetIsLimit (torsorExtension P) (constantIntegerOne X)))
  apply h.of_iso (Iso.refl _) (setInverseImageAbelianIso f (torsorExtension P).X₂)
    (setInverseImageTerminalIso f) (setInverseImageIntegerIso f)
  · exact (Category.id_comp _).symm
  · exact toUnit_unique _ _
  · change (setInverseImage f).map ((underlyingSetFunctor X).map (torsorExtension P).g) ≫
        (setInverseImageAbelianIso f (constantIntegerSheaf X)).hom ≫
          (underlyingSetFunctor S).map (inverseImageIntegerIso f).hom =
      (setInverseImageAbelianIso f (torsorExtension P).X₂).hom ≫
        (underlyingSetFunctor S).map ((inverseImage f).map (torsorExtension P).g ≫
          (inverseImageIntegerIso f).hom)
    rw [Functor.map_comp, ← Category.assoc, ← Category.assoc]
    exact congrArg (fun q => q ≫ (underlyingSetFunctor S).map (inverseImageIntegerIso f).hom)
      ((inverseImageUnderlyingSetIso f).inv.naturality (torsorExtension P).g)
  · exact (setInverseImage_integerOne f).trans
      (congrArg (fun q => q ≫ integerOneSetMap S) (toUnit_unique _ _))

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

/-- The canonical embedding has the original positive coefficient action. -/
theorem torsorCanonicalSetInclusion_action (U : X.Etaleᵒᵖ) (a : L.obj.obj U)
    (t : P.carrier.obj.obj U) :
    (torsorCanonicalSetInclusion P).hom.app U (P.action U a t) =
      (torsorExtension P).f.hom.app U a +
        (show (torsorExtension P).X₂.obj.obj U from (torsorCanonicalSetInclusion P).hom.app U t) :=
  congrArg Subtype.val ((torsorCanonicalExtensionIso P).equivariant U a t)

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

/-- The canonical unit square for the actual torsor carrier and its embedding. -/
theorem torsorSetInverseImageIso_unit_inclusion :
    (setInverseImageAdjunction f).unit.app P.carrier ≫
      (setDirectImage f).map ((torsorSetInverseImageIso f P).hom ≫
        extensionFiberSetInclusion (torsorInverseImageExtension f P) (constantIntegerOne S)) =
      torsorCanonicalSetInclusion P ≫
        (underlyingSetFunctor X).map ((inverseImageAdjunction f).unit.app (torsorExtension P).X₂)
          := by
  rw [torsorSetInverseImageIso_hom_inclusion, Functor.map_comp, ← Category.assoc]
  have hn := (setInverseImageAdjunction f).unit.naturality (torsorCanonicalSetInclusion P)
  change _ = (setInverseImageAdjunction f).unit.app P.carrier ≫
    (setDirectImage f).map ((setInverseImage f).map (torsorCanonicalSetInclusion P)) at hn
  rw [← hn, Category.assoc]
  exact congrArg (fun q => torsorCanonicalSetInclusion P ≫ q)
    (setInverseImageAbelianIso_unit f (torsorExtension P).X₂)

/-- Actual scheme inverse image of a sheaf torsor. Its carrier is definitionally
the set-sheaf inverse image; its action comes from the canonical extension fibre. -/
def torsorInverseImage : Torsor ((inverseImage f).obj L) :=
  (torsorInverseImageFiber f P).transportCarrier (torsorSetInverseImageIso f P)

/-- The actual pullback torsor is identified equivariantly with the pulled-back
extension fibre; no torsor-classification premise is used. -/
def torsorInverseImageFiberIso :
    Torsor.Iso (torsorInverseImage f P) (torsorInverseImageFiber f P) :=
  (torsorInverseImageFiber f P).transportCarrierIso (torsorSetInverseImageIso f P)

/-- The actual inverse-image unit is equivariant for the actual coefficient
unit. This identifies the transported action with the sheaf inverse-image
action, including its coefficient variance and positive sign. -/
theorem torsorInverseImage_unit_equivariant (U : X.Etaleᵒᵖ)
    (a : L.obj.obj U) (t : P.carrier.obj.obj U) :
    ((setInverseImageAdjunction f).unit.app P.carrier).hom.app U (P.action U a t) =
      (torsorInverseImage f P).action ((siteBaseChange f).op.obj U)
        (((inverseImageAdjunction f).unit.app L).hom.app U a)
        (((setInverseImageAdjunction f).unit.app P.carrier).hom.app U t) := by
  let V := (siteBaseChange f).op.obj U
  let e := torsorSetInverseImageIso f P
  apply (ConcreteCategory.bijective_of_isIso (e.hom.hom.app V)).injective
  have heq := (torsorInverseImageFiberIso f P).equivariant V
    (((inverseImageAdjunction f).unit.app L).hom.app U a)
    (((setInverseImageAdjunction f).unit.app P.carrier).hom.app U t)
  change e.hom.hom.app V _ = e.hom.hom.app V _
  erw [heq]
  apply Subtype.ext
  have hu (t' : P.carrier.obj.obj U) := congrArg (fun q => q.hom.app U t')
    (torsorSetInverseImageIso_unit_inclusion f P)
  have hn := congrArg (fun q => q.hom.app U a)
    ((inverseImageAdjunction f).unit.naturality (torsorExtension P).f)
  change ((inverseImageAdjunction f).unit.app (torsorExtension P).X₂).hom.app U
      ((torsorExtension P).f.hom.app U a) =
    ((inverseImage f).map (torsorExtension P).f).hom.app V
      (((inverseImageAdjunction f).unit.app L).hom.app U a) at hn
  change (e.hom.hom.app V
    (((setInverseImageAdjunction f).unit.app P.carrier).hom.app U (P.action U a t))).val =
      ((inverseImage f).map (torsorExtension P).f).hom.app V
        (((inverseImageAdjunction f).unit.app L).hom.app U a) +
      (show ((inverseImage f).obj (torsorExtension P).X₂).obj.obj V from
        (e.hom.hom.app V (((setInverseImageAdjunction f).unit.app P.carrier).hom.app U t)).val)
  refine (hu (P.action U a t)).trans ?_
  change ((inverseImageAdjunction f).unit.app (torsorExtension P).X₂).hom.app U
    ((torsorCanonicalSetInclusion P).hom.app U (P.action U a t)) = _
  rw [torsorCanonicalSetInclusion_action, map_add, hn]
  exact congrArg (fun v : ((inverseImage f).obj (torsorExtension P).X₂).obj.obj V =>
    ((inverseImage f).map (torsorExtension P).f).hom.app V
    (((inverseImageAdjunction f).unit.app L).hom.app U a) + v) (hu t).symm

/-- Actual set-sheaf pullback has the actual contravariant Ext class. -/
theorem torsorExtClass_inverseImage
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)] [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)] :
    torsorExtClass (torsorInverseImage f P) = h1Pullback f L (torsorExtClass P) := by
  rw [torsorExtClass_iso (torsorInverseImageFiberIso f P), torsorExtClass_inverseImageFiber]

end FibrePullback

end AlgebraicGeometry.Scheme.EtaleCohomology

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 fb3a3b171fc976533443eafb7a028f5bcb42c44567b2fdb418789a46ed665aa7.
Definitions, hypotheses and universes are retained modulo native names. -/
