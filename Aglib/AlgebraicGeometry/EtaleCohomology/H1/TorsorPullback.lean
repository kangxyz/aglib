/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Current interface basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original construction and mathematical provenance are retained below. -/
public import Aglib.CategoryTheory.Sites.Torsor.InverseImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.EtaleRestriction
public import Aglib.CategoryTheory.Sites.Torsor.Pushout
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.ExtensionFiberClass
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.TorsorSum

/-!
# Actual inverse-image extensions and their torsor fibres

Construction for `K2-018#eq:k2018-pointed-character`, frozen basis
`7f86e4a1763cc4ec35e9b0a8acd659750355a0de`. The exact abelian inverse-image
functor is applied to the constructed torsor extension. Constant integers
are transported by the canonical constant-sheaf isomorphism. The class of
its actual augmentation-one fibre is the previously constructed H¹ pullback.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology
universe u
attribute [local instance] hasSheafifyLarge
section TorsorIsomorphisms
variable {X : Scheme.{u}} {L : AbelianSheaf.{u, u + 1} X} {P Q : Torsor L}

/-- A same-coefficient equivariant torsor morphism is injective on every section set. -/
theorem Torsor.Hom.injective (r : Torsor.Hom (𝟙 L) P Q) (U : X.Etaleᵒᵖ) :
    Function.Injective (r.map.hom.app U) :=
  CategoryTheory.Sheaf.Torsor.Hom.injective r U

/-- Local nonemptiness of the source proves local surjectivity. -/
instance Torsor.Hom.locallySurjective (r : Torsor.Hom (𝟙 L) P Q) :
    Sheaf.IsLocallySurjective r.map :=
  CategoryTheory.Sheaf.Torsor.Hom.locallySurjective r

/-- The actual underlying sheaf map of a same-coefficient torsor map is invertible. -/
instance Torsor.Hom.map_isIso (r : Torsor.Hom (𝟙 L) P Q) : IsIso r.map :=
  CategoryTheory.Sheaf.Torsor.Hom.map_isIso r

/-- Genuine torsor maps are actual equivariant isomorphisms, without 03AJ. -/
abbrev Torsor.Hom.toIso (r : Torsor.Hom (𝟙 L) P Q) : Torsor.Iso P Q :=
  CategoryTheory.Sheaf.Torsor.Hom.toIso r

/-- The original torsor maps canonically to the one-fibre of its constructed extension. -/
noncomputable def torsorCanonicalExtensionMap (P : Torsor L) :
    Torsor.Hom (𝟙 L) P
      (extensionFiberTorsor (torsorExtension P) (constantIntegerOne X)
        (torsorExtension_shortExact P)) := by
  have h : torsorPushout P (𝟙 L) =
      extensionFiberTorsor (torsorExtension P) (constantIntegerOne X)
        (torsorExtension_shortExact P) := by
    rfl
  exact h ▸ torsorPushoutMap P (𝟙 L)

/-- The canonical extension's augmentation-one fibre recovers the actual torsor. -/
noncomputable def torsorCanonicalExtensionIso (P : Torsor L) :
    Torsor.Iso P (extensionFiberTorsor (torsorExtension P) (constantIntegerOne X)
      (torsorExtension_shortExact P)) :=
  (torsorCanonicalExtensionMap P).toIso

end TorsorIsomorphisms

variable {X S : Scheme.{u}} (f : S ⟶ X) {L : AbelianSheaf.{u, u + 1} X}
variable (P : Torsor L)

/-- Canonical constant-integer transport for the actual inverse image. -/
abbrev inverseImageIntegerIso : (inverseImage f).obj (constantIntegerSheaf X) ≅
    constantIntegerSheaf S :=
  (inverseImageConstantIso f).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))


local instance nativeAbelianPullback_preservesFiniteLimits :
    PreservesFiniteLimits ((siteBaseChange f).sheafPullback AddCommGrpCat.{u + 1}
      X.smallEtaleTopology S.smallEtaleTopology) :=
  inverseImage_preservesFiniteLimits f

/-- The additive fragment of the actual etale geometric morphism and coefficient adjunction. -/
abbrev etaleAdditiveCoefficientAction :
    Topos.AdditiveCoefficientAction.{u + 1, u, u + 1, u, u + 1}
      (Scheme.etaleToposMorphism f)
      (Topos.AdditiveCoefficientAction.coefficientAdjunctionOfSiteFunctor.{u + 1, u,
        u + 1, u, u + 1}
        (siteBaseChange f) X.smallEtaleTopology S.smallEtaleTopology) :=
  Topos.AdditiveCoefficientAction.ofSiteFunctor.{u + 1, u, u + 1, u, u + 1}
    (siteBaseChange f) X.smallEtaleTopology S.smallEtaleTopology

/-- The native mate is the original whole underlying inverse-image comparison. -/
theorem etaleAdditiveCoefficientAction_leftComparison :
    (etaleAdditiveCoefficientAction f).leftComparison = (inverseImageUnderlyingSetIso f).inv := by
  apply NatTrans.ext
  funext A
  apply ((setInverseImageAdjunction f).homEquiv _ _).injective
  change (setInverseImageAdjunction f).unit.app (underlyingSetSheaf A) ≫
      (setDirectImage f).map ((etaleAdditiveCoefficientAction f).leftComparison.app A) =
    (setInverseImageAdjunction f).unit.app (underlyingSetSheaf A) ≫
      (setDirectImage f).map ((inverseImageUnderlyingSetIso f).inv.app A)
  have h := Topos.AdditiveCoefficientAction.leftComparison_unit
    (etaleAdditiveCoefficientAction f) A
  change (underlyingSetFunctor X).map ((inverseImageAdjunction f).unit.app A) ≫ 𝟙 _ =
    (setInverseImageAdjunction f).unit.app (underlyingSetSheaf A) ≫
      (setDirectImage f).map ((etaleAdditiveCoefficientAction f).leftComparison.app A) at h
  rw [Category.comp_id] at h
  rw [← h, ← inverseImageUnderlyingSetIso_unit]
  rw [Category.assoc, ← Functor.map_comp, (inverseImageUnderlyingSetIso f).hom_inv_id_app]
  exact (Category.comp_id _).symm

/-- Invertibility comes from the original native Kan and sheafification comparison. -/
instance etaleAdditiveCoefficientAction_leftComparison_isIso :
    IsIso (etaleAdditiveCoefficientAction f).leftComparison := by
  rw [etaleAdditiveCoefficientAction_leftComparison]
  infer_instance

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


/-- Intrinsic integer transport is the original terminal-site constant-integer Iso. -/
theorem etaleAdditiveCoefficientAction_integerIso :
    (etaleAdditiveCoefficientAction f).integerIso = inverseImageIntegerIso f := by
  apply Iso.ext
  apply ((inverseImageAdjunction f).homEquiv _ _).injective
  apply (CategoryTheory.Sheaf.constantIntegerHomGlobalPointEquiv _).injective
  ext U x
  change (PUnit : Type (u + 1)) at x
  cases x
  change (etaleAdditiveCoefficientAction f).integerAdjunctionMap.hom.app U
      ((CategoryTheory.Sheaf.constantIntegerOne X.smallEtaleTopology).hom.app U PUnit.unit) =
    (inverseImageIntegerIso f).hom.hom.app ((siteBaseChange f).op.obj U)
      (((inverseImageAdjunction f).unit.app (constantIntegerSheaf X)).hom.app U
        ((CategoryTheory.Sheaf.constantIntegerOne X.smallEtaleTopology).hom.app U PUnit.unit))
  rw [← constantIntegerOne_asGlobalPoint (X := X)]
  have h : (etaleAdditiveCoefficientAction f).integerAdjunctionMap.hom.app U
      (show (constantIntegerSheaf X).obj.obj U from
        (CategoryTheory.Sheaf.constantIntegerOne X.smallEtaleTopology).hom.app U PUnit.unit) =
    (show (constantIntegerSheaf S).obj.obj ((siteBaseChange f).op.obj U) from
      (CategoryTheory.Sheaf.constantIntegerOne S.smallEtaleTopology).hom.app
        ((siteBaseChange f).op.obj U) PUnit.unit) :=
    Topos.AdditiveCoefficientAction.ofSiteFunctor_integerAdjunctionMap_one.{u + 1, u,
      u + 1, u, u + 1} (siteBaseChange f) X.smallEtaleTopology S.smallEtaleTopology U
  rw [← constantIntegerOne_asGlobalPoint (X := X),
    ← constantIntegerOne_asGlobalPoint (X := S)] at h
  exact h.trans (inverseImageIntegerIso_unit_restrict_one f U).symm

/-- Projection of the actual inverse-image extension onto constant integers. -/
def torsorInverseImageProjection :
    (inverseImage f).obj (torsorExtension P).X₂ ⟶ constantIntegerSheaf S :=
  (inverseImage f).map (torsorExtension P).g ≫ (inverseImageIntegerIso f).hom

/-- The same right-endpoint transport gives equality of the entire projection map. -/
theorem torsorInverseImageProjection_eq_generic :
    torsorInverseImageProjection f P =
      CategoryTheory.Sheaf.torsorInverseImageProjection (etaleAdditiveCoefficientAction f) P := by
  let p : (torsorExtension P).X₂ ⟶ constantIntegerSheaf X := (torsorExtension P).g
  change (inverseImage f).map p ≫ (inverseImageIntegerIso f).hom =
    (inverseImage f).map p ≫ (etaleAdditiveCoefficientAction f).integerIso.hom
  exact congrArg
    (fun e : (inverseImage f).obj (constantIntegerSheaf X) ≅ constantIntegerSheaf S =>
      (inverseImage f).map p ≫ e.hom) (etaleAdditiveCoefficientAction_integerIso f).symm

private theorem shortComplex_mk_eq_of_projection_eq
    {A B C : AbelianSheaf.{u, u + 1} S} (i : A ⟶ B) {p p' : B ⟶ C}
    (hp : p = p') (h : i ≫ p = 0) (h' : i ≫ p' = 0) :
    ShortComplex.mk i p h = ShortComplex.mk i p' h' := by
  cases hp
  rfl

private theorem fibre_mk_eq_of_projection_and_point_eq
    {A B C : AbelianSheaf.{u, u + 1} S} (i : A ⟶ B) {p p' : B ⟶ C}
    (hp : p = p') {h : i ≫ p = 0} {h' : i ≫ p' = 0}
    (e : (ShortComplex.mk i p h).ShortExact) (e' : (ShortComplex.mk i p' h').ShortExact)
    {z z' : Topos.GlobalPoint (underlyingSetSheaf C)} (hz : z = z') :
    CategoryTheory.Sheaf.extensionFiberTorsor (ShortComplex.mk i p h) z e =
      CategoryTheory.Sheaf.extensionFiberTorsor (ShortComplex.mk i p' h') z' e' := by
  cases hp
  cases hz
  rfl

/-- Exact inverse image preserves the augmentation relation. -/
theorem torsorInverseImage_zero :
    (inverseImage f).map (torsorExtension P).f ≫ torsorInverseImageProjection f P = 0 := by
  rw [torsorInverseImageProjection, ← Category.assoc, ← Functor.map_comp,
    ShortComplex.zero, Functor.map_zero, zero_comp]

/-- The actual inverse-image extension with canonical constant-ℤ transport. -/
def torsorInverseImageExtension : ShortComplex (AbelianSheaf.{u, u + 1} S) :=
  ShortComplex.mk ((inverseImage f).map (torsorExtension P).f)
    (torsorInverseImageProjection f P) (torsorInverseImage_zero f P)

/-- The literal native complex is the generic complex on the same actual functors. -/
theorem torsorInverseImageExtension_eq_generic :
    torsorInverseImageExtension f P =
      CategoryTheory.Sheaf.torsorInverseImageExtension (etaleAdditiveCoefficientAction f) P := by
  exact shortComplex_mk_eq_of_projection_eq
    ((inverseImage f).map (torsorExtension P).f)
    (torsorInverseImageProjection_eq_generic f P)
    (torsorInverseImage_zero f P)
    (CategoryTheory.Sheaf.torsorInverseImage_zero (etaleAdditiveCoefficientAction f) P)

/-- The canonical transport is an isomorphism of actual short complexes. -/
def torsorInverseImageExtensionIso :
    (torsorExtension P).map (inverseImage f) ≅ torsorInverseImageExtension f P :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (inverseImageIntegerIso f)
    (by simp [torsorInverseImageExtension])
    (by simp [torsorInverseImageExtension, torsorInverseImageProjection])

/-- Short exactness is preserved, without any exactness premise for the scheme map. -/
theorem torsorInverseImageExtension_shortExact : (torsorInverseImageExtension f P).ShortExact := by
  rw [torsorInverseImageExtension_eq_generic]
  exact CategoryTheory.Sheaf.torsorInverseImageExtension_shortExact
    (etaleAdditiveCoefficientAction f) P

/-- A genuine torsor formed from the actual inverse-image extension. -/
def torsorInverseImageFiber : Torsor ((inverseImage f).obj L) :=
  extensionFiberTorsor (torsorInverseImageExtension f P) (constantIntegerOne S)
    (torsorInverseImageExtension_shortExact f P)

/-- The original terminal-one fibre is the same intrinsic one-fibre torsor. -/
theorem torsorInverseImageFiber_eq_generic :
    torsorInverseImageFiber f P =
      CategoryTheory.Sheaf.torsorInverseImageFiber (etaleAdditiveCoefficientAction f) P := by
  exact fibre_mk_eq_of_projection_and_point_eq
    ((inverseImage f).map (torsorExtension P).f)
    (torsorInverseImageProjection_eq_generic f P)
    (torsorInverseImageExtension_shortExact f P)
    (CategoryTheory.Sheaf.torsorInverseImageExtension_shortExact
      (etaleAdditiveCoefficientAction f) P)
    (constantIntegerOne_asGlobalPoint (X := S))

universe e
private theorem extClass_mk_eq_of_projection_eq
    [HasExt.{e} (AbelianSheaf.{u, u + 1} S)]
    {A B C : AbelianSheaf.{u, u + 1} S} (i : A ⟶ B) {p p' : B ⟶ C}
    (hp : p = p') {h : i ≫ p = 0} {h' : i ≫ p' = 0}
    (e : (ShortComplex.mk i p h).ShortExact) (e' : (ShortComplex.mk i p' h').ShortExact) :
    e.extClass = e'.extClass := by
  cases hp
  rfl

section ExtClass
universe w w'
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
variable [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]

/-- The generic H1 map is the original map, including its inverse integer transport. -/
theorem h1Pullback_eq_generic :
    h1Pullback f L =
      CategoryTheory.Sheaf.torsorH1InverseImageMap (etaleAdditiveCoefficientAction f) L := by
  unfold h1Pullback CategoryTheory.Sheaf.torsorH1InverseImageMap
  rw [etaleAdditiveCoefficientAction_integerIso]
  rfl

/-- The canonical Ext class of the inverse-image extension uses the inverse
constant transport in the contravariant first Ext variable. -/
theorem torsorInverseImageExtension_extClass :
    (torsorInverseImageExtension_shortExact f P).extClass =
      h1Pullback f L (torsorExtClass P) := by
  have he : (torsorInverseImageExtension_shortExact f P).extClass =
      (CategoryTheory.Sheaf.torsorInverseImageExtension_shortExact
        (etaleAdditiveCoefficientAction f) P).extClass :=
    extClass_mk_eq_of_projection_eq ((inverseImage f).map (torsorExtension P).f)
      (torsorInverseImageProjection_eq_generic f P)
      (torsorInverseImageExtension_shortExact f P)
      (CategoryTheory.Sheaf.torsorInverseImageExtension_shortExact
        (etaleAdditiveCoefficientAction f) P)
  exact he.trans ((CategoryTheory.Sheaf.torsorInverseImageExtension_extClass
    (etaleAdditiveCoefficientAction f) P).trans
      (congrArg (fun m : H1Etale X L →+ H1Etale S ((inverseImage f).obj L) =>
        m (torsorExtClass P)) (h1Pullback_eq_generic f (L := L)).symm))

/-- Canonical class compatibility for the genuinely constructed inverse-image
extension fibre. Identification with the set-sheaf inverse image is separate. -/
theorem torsorExtClass_inverseImageFiber :
    torsorExtClass (torsorInverseImageFiber f P) = h1Pullback f L (torsorExtClass P) := by
  rw [torsorInverseImageFiber_eq_generic, h1Pullback_eq_generic]
  exact CategoryTheory.Sheaf.torsorExtClass_inverseImageFiber
    (etaleAdditiveCoefficientAction f) P

end ExtClass
end AlgebraicGeometry.Scheme.EtaleCohomology

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 bc3efa93f0550d2614c6d83cecfc91235de388d6f1955901118d6d6c1ea84b0a.
Definitions, hypotheses and universes are retained modulo native names. -/
