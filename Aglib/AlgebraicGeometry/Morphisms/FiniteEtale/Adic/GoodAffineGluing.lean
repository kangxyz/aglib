/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.RelativeFiniteEtaleGluing
public import Aglib.AlgebraicGeometry.Morphisms.Proper.LocalBaseOpenCover
public import Aglib.AlgebraicGeometry.AffineScheme.TensorPullback

/-!
# Gluing good affine section algebras

The affine pieces are spectra of the original ring-valued section presheaf;
the transition arrows are its original restrictions. Canonical affine
base-change squares produce an equifibered diagram on the good affine basis,
and the native relative gluing theorem constructs the actual finite-etale
cover. No finite subcover or general relative spectrum is constructed.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.FiniteEtale.AffineAlgebraGluing

universe u
variable {X : Scheme.{u}} (F : X.Opensᵒᵖ ⥤ CommRingCat.{u}) (η : X.presheaf ⟶ F)

/-- An affine open is good when its actual section algebra is etale. -/
def IsGood (U : X.Opens) : Prop := IsAffineOpen U ∧ (η.app (op U)).hom.Etale

/-- The good-open index is a subtype of the original opens, ordered by inclusion. -/
abbrev GoodOpen := {U : X.Opens // IsGood F η U}

/-- The original section-algebra spectrum over its own affine open. -/
def toOpen (U : X.Opens) (hU : IsAffineOpen U) :
    Spec (F.obj (op U)) ⟶ U.toScheme :=
  Spec.map (η.app (op U)) ≫ hU.isoSpec.inv

/-- Original restriction maps commute with the original structure maps. -/
@[reassoc]
theorem restriction_toOpen {U V : X.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (h : U ≤ V) :
    Spec.map (F.map (homOfLE h).op) ≫ toOpen F η V hV =
      toOpen F η U hU ≫ X.homOfLE h := by
  apply (cancel_mono V.ι).mp
  simp only [toOpen, Category.assoc, Scheme.homOfLE_ι]
  change Spec.map (F.map (homOfLE h).op) ≫
      Spec.map (η.app (op V)) ≫ hV.fromSpec =
    Spec.map (η.app (op U)) ≫ hU.fromSpec
  rw [← Spec.map_comp_assoc, ← η.naturality, Spec.map_comp_assoc,
    hV.map_fromSpec hU (homOfLE h).op]

/-- Transport a canonical spectrum pullback square to the actual affine opens. -/
theorem restriction_isPullback {U V : X.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (h : U ≤ V)
    (hcart : IsPullback (Spec.map (F.map (homOfLE h).op))
      (Spec.map (η.app (op U))) (Spec.map (η.app (op V)))
      (Spec.map (X.presheaf.map (homOfLE h).op))) :
    IsPullback (Spec.map (F.map (homOfLE h).op)) (toOpen F η U hU)
      (toOpen F η V hV) (X.homOfLE h) := by
  apply hcart.of_iso (Iso.refl _) (Iso.refl _) hU.isoSpec.symm hV.isoSpec.symm
  · simp
  · simp [toOpen]
  · simp [toOpen]
  · apply (cancel_mono V.ι).mp
    simpa only [Iso.symm_hom, Category.assoc, IsAffineOpen.isoSpec_inv_ι, Scheme.homOfLE_ι] using
      hV.map_fromSpec hU (homOfLE h).op

variable (hcart : ∀ (U V : X.Opens) (_hU : IsAffineOpen U) (_hV : IsAffineOpen V)
  (h : U ≤ V), IsPullback (Spec.map (F.map (homOfLE h).op))
    (Spec.map (η.app (op U))) (Spec.map (η.app (op V)))
    (Spec.map (X.presheaf.map (homOfLE h).op)))

include hcart in
/-- Goodness is stable under every affine refinement, by the canonical
section-algebra base-change square. -/
theorem isGood_restrict {U V : X.Opens} (hV : IsGood F η V)
    (h : U ≤ V) (hU : IsAffineOpen U) : IsGood F η U := by
  refine ⟨hU, ?_⟩
  have : Etale (Spec.map (η.app (op V))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr hV.2
  have : Etale (Spec.map (η.app (op U))) :=
    MorphismProperty.of_isPullback (P := @Etale) (hcart U V hU hV.1 h) inferInstance
  exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp inferInstance

variable (hcover : ∀ x : X, ∃ U, IsGood F η U ∧ x ∈ U)

include hcart hcover in
/-- Downward affine stability and actual pointwise coverage make the good
opens a basis, not merely a finite subcover. -/
theorem goodOpen_isBasis : Opens.IsBasis {U : X.Opens | IsGood F η U} := by
  rw [Opens.isBasis_iff_nbhd]
  intro V x hxV
  obtain ⟨U, hU, hxU⟩ := hcover x
  obtain ⟨W, hW, hxW, hWU⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show x ∈ U ⊓ V from ⟨hxU, hxV⟩)
  exact ⟨W, isGood_restrict F η hcart hU (hWU.trans inf_le_left) hW,
    hxW, hWU.trans inf_le_right⟩

/-- The cover by all good original affine opens. -/
def goodOpenCover : X.OpenCover where
  I₀ := GoodOpen F η
  X U := U.val.toScheme
  f U := U.val.ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, inferInstance⟩
    obtain ⟨U, hU, hxU, _⟩ := Opens.isBasis_iff_nbhd.mp
      (goodOpen_isBasis F η hcart hcover) (Opens.mem_top x)
    exact ⟨⟨U, hU⟩, ⟨x, hxU⟩, rfl⟩

/-- The good affine cover is ordered by inclusion of its original opens. -/
instance instPreorderGoodOpenCover : Preorder (goodOpenCover F η hcart hcover).I₀ :=
  inferInstanceAs (Preorder (GoodOpen F η))

/-- Refinements of the good affine basis make its original open cover locally directed. -/
instance instLocallyDirectedGoodOpenCover : (goodOpenCover F η hcart hcover).LocallyDirected :=
  .ofIsBasisOpensRange (by intros; simp [goodOpenCover]) (by
    convert goodOpen_isBasis F η hcart hcover
    ext U
    simp [goodOpenCover])

@[simp]
theorem goodOpenCover_trans {U V : GoodOpen F η} (h : U ≤ V) :
    (goodOpenCover F η hcart hcover).trans (homOfLE h) = X.homOfLE h := rfl

/-- The spectra of the actual section rings, with the actual restrictions. -/
def diagram : (goodOpenCover F η hcart hcover).I₀ ⥤ Scheme.{u} where
  obj U := Spec (F.obj (op U.val))
  map {U V} h := Spec.map (F.map (homOfLE (show U.val ≤ V.val from leOfHom h)).op)
  map_id U := by simp
  map_comp {U V W} f g := by
    rw [← Spec.map_comp, ← F.map_comp]
    rfl

/-- The original algebra structure maps to their affine opens form a
natural transformation to the native locally directed cover diagram. -/
def diagramToBase :
    diagram F η hcart hcover ⟶ (goodOpenCover F η hcart hcover).functorOfLocallyDirected where
  app U := toOpen F η U.val U.property.1
  naturality U V h := restriction_toOpen F η U.property.1 V.property.1 (leOfHom h)

/-- Canonical affine base change supplies the actual relative gluing datum. -/
def datum : Scheme.Cover.RelativeGluingData (goodOpenCover F η hcart hcover) where
  functor := diagram F η hcart hcover
  natTrans := diagramToBase F η hcart hcover
  equifibered {U V} h :=
    restriction_isPullback F η U.property.1 V.property.1 (leOfHom h)
      (hcart U.val V.val U.property.1 V.property.1 (leOfHom h))

variable (hfinite : ∀ (U : X.Opens), IsAffineOpen U → (η.app (op U)).hom.Finite)

include hfinite in
theorem datum_finite (U : (goodOpenCover F η hcart hcover).I₀) :
    IsFinite ((datum F η hcart hcover).natTrans.app U) := by
  have : IsFinite (Spec.map (η.app (op U.val))) :=
    (IsFinite.SpecMap_iff _).mpr (hfinite U.val U.property.1)
  change IsFinite (Spec.map (η.app (op U.val)) ≫ U.property.1.isoSpec.inv)
  infer_instance

/-- Each original section-spectrum chart maps etale to its good affine open. -/
instance instEtaleDatum (U : (goodOpenCover F η hcart hcover).I₀) :
    Etale ((datum F η hcart hcover).natTrans.app U) := by
  have : Etale (Spec.map (η.app (op U.val))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr U.property.2
  change Etale (Spec.map (η.app (op U.val)) ≫ U.property.1.isoSpec.inv)
  infer_instance

/-- The native glued cover has exactly the original section spectra as
its affine base changes. -/
def cover : Scheme.FiniteEtale X := by
  let : ∀ U, IsFinite ((datum F η hcart hcover).natTrans.app U) :=
    datum_finite F η hcart hcover hfinite
  exact RelativeGluing.gluedCover.{u, u, u} (datum F η hcart hcover)

/-- The local cover uses the original section spectrum and structure map. -/
def localCover (U : GoodOpen F η) : Scheme.FiniteEtale U.val.toScheme :=
  ⟨Over.mk (toOpen F η U.val U.property.1),
    datum_finite F η hcart hcover hfinite U, instEtaleDatum F η hcart hcover U⟩

/-- The specified local comparison retains the native base-change functor. -/
def localCoverIso (U : GoodOpen F η) :
    (baseChange U.val.ι).obj (cover F η hcart hcover hfinite) ≅
      localCover F η hcart hcover hfinite U := by
  let : ∀ V, IsFinite ((datum F η hcart hcover).natTrans.app V) :=
    datum_finite F η hcart hcover hfinite
  exact RelativeGluing.localCoverIso.{u, u, u} (datum F η hcart hcover) U

/-- Over a local base, it suffices to find good opens at the actual closed
fibre. Properness supplies this hypothesis through universal closedness. -/
theorem goodOpen_cover_of_closedFiber {R : Type u} [CommRing R] [IsLocalRing R]
    (f : X ⟶ Spec (.of R)) [UniversallyClosed f]
    (hfibre : ∀ x ∈ Set.range (LocalRing.ResidueFiber.projection f),
      ∃ U, IsGood F η U ∧ x ∈ U) : ∀ x : X, ∃ U, IsGood F η U ∧ x ∈ U :=
  LocalRing.exists_goodOpen_of_closedFiber f hfibre

end AlgebraicGeometry.Scheme.FiniteEtale.AffineAlgebraGluing
