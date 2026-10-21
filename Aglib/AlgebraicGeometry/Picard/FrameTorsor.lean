/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.IsomorphismSheaf
public import Aglib.AlgebraicGeometry.Modules.Invertible.Power.Pullback
public import Aglib.AlgebraicGeometry.Picard.UnitDescent
public import Aglib.AlgebraicGeometry.Modules.Invertible.ScalarAutomorphisms
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.Coefficients
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.Torsors
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Picard.FrameTorsor` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`399e2084e1bfe9378fc151d934f50010f41046f928393f0b38e95bd0e9c39542`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.EtaleCohomology
open _root_.AlgebraicGeometry.Scheme.Modules.Invertible
  (LineBundle isLocallyRankOne_iff_restrict_unit isLocallyRankOne_of_iso
    pullback_locallyRankOne trivialLineBundle)
open _root_.AlgebraicGeometry.Scheme.Modules (pullbackUnitIso)
/-!
Interface migration basis: `46f53465aaf3b0167049e9c8e9e2294111bb4281`.
Accepted object-owner map SHA-256:
`8a638d1a1d17381235478e81285ee940a20aedecb03e9d3ff1ae9878791e1868`.
Imports follow the current object owners; existing R5Lab declaration names and
all construction/proof bodies are preserved. Historical source and validation
receipts below retain their original basis. New-interface validation is pending.
-/
/-!
# Actual O-linear frame sheaves and their Gm torsors

Manuscript locator: `K2-018#lem:k2018-geometric-exact-order`.
Mathematical source revision: `e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Engineering source revision: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.

For an actual locally free rank-one module sheaf L, sections on an etale
U over X are actual O_U-linear isomorphisms from U^*L to O_U. The frame
sheaf is explicitly the restriction of the big-etale module-isomorphism
sheaf to the small site, with the required value-universe lift. Its only
retained background premise is the fixed general EtaleLineBundleDescent,
used for the isomorphism-sheaf condition. Its Gm action is positive scalar
postcomposition. Naturality follows from the native pullHom scalar square;
unique transport follows from the actual O-automorphism/global-unit
equivalence; local nonemptiness follows from genuine open rank-one charts
and the actual small-etale covering criterion. Thus frameTorsor is a genuine
sheaf torsor. No Gm/Picard or H1 classification is assumed or asserted here.
No arbitrary-base inverse-image equivalence for the Gm sheaf is used.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Hom
open AlgebraicGeometry.Scheme.Modules.Invertible
namespace AlgebraicGeometry.Scheme.Modules.Invertible.FrameTorsor
open EtaleDescent
open AlgebraicGeometry.Scheme.EtaleCohomology
universe u

/-- The actual structure module as a line bundle. -/
def unitBundle (X : Scheme.{u}) : LineBundle X :=
  ⟨SheafOfModules.unit X.ringCatSheaf, isLocallyRankOne_of_iso X
    (Limits.coproductUniqueIso (fun _ : PUnit.{u + 1} => SheafOfModules.unit X.ringCatSheaf))
      (trivialLineBundle X).property⟩

/-- Postcomposition with `e` as an equivalence between the corresponding sets of isomorphisms. -/
def isoRightEquiv {C : Type*} [Category C] {A B D : C} (e : B ≅ D) : (A ≅ B) ≃ (A ≅ D) where
  toFun φ := φ ≪≫ e
  invFun φ := φ ≪≫ e.symm
  left_inv φ := by ext; simp
  right_inv φ := by ext; simp

/-- The genuine sheaf of O-linear trivializations, restricted from the big
scheme-over-X site to the small etale site and lifted in value universe. -/
def frameSheaf (h : EtaleLineBundleDescent.{u}) (X : Scheme.{u}) (L : LineBundle X) : SetSheaf
    X where
  obj := (Scheme.Etale.forget X).op ⋙
    (isoSheaf (ofLineBundle X L) (ofLineBundle X (unitBundle X)) h).obj ⋙ uliftFunctor.{u + 1}
  property := by
    change Presheaf.IsSheaf (Scheme.smallEtaleTopology X)
      (((Scheme.Etale.forget X).op ⋙
        (isoSheaf (ofLineBundle X L) (ofLineBundle X (unitBundle X)) h).obj) ⋙ uliftFunctor.{u + 1})
    apply Presheaf.isSheaf_comp_of_isSheaf _ _ uliftFunctor.{u + 1}
    apply (Scheme.Etale.forget X).op_comp_isSheaf_of_isSheaf
      (Scheme.smallEtaleTopology X) (Scheme.etaleTopology.over X)
    exact (isoSheaf (ofLineBundle X L) (ofLineBundle X (unitBundle X)) h).property

/-- Sections are literal isomorphisms of the pulled line bundle with O_U. -/
def frameSectionsEquiv (h : EtaleLineBundleDescent.{u}) (X : Scheme.{u}) (L : LineBundle X)
    (U : X.Etaleᵒᵖ) :
    (frameSheaf h X L).obj.obj U ≃
      ((Scheme.Modules.pullback U.unop.hom).obj L.val ≅ SheafOfModules.unit
          U.unop.left.ringCatSheaf) :=
  ((Equiv.ulift.trans (isoSectionsEquiv (ofLineBundle X L) (ofLineBundle X (unitBundle X)) h
    (op ((Scheme.Etale.forget X).obj U.unop)))).trans
      (rankOne.prop (.mk (op U.unop.left))).fullyFaithfulι.isoEquiv).trans
        (isoRightEquiv (pullbackUnitIso U.unop.hom))

open _root_.AlgebraicGeometry.Scheme.Modules.Invertible.TrivializedPower
open _root_.GroupCohomology.Kummer.Coefficients
open _root_.AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms

/-- The genuine positive scalar action on O-linear frames. -/
def frameAction (h : EtaleLineBundleDescent.{u}) (X : Scheme.{u}) (L : LineBundle X)
    (U : X.Etaleᵒᵖ) (a : (gm X).obj.obj U) (s : (frameSheaf h X L).obj.obj U) :
    (frameSheaf h X L).obj.obj U :=
  (frameSectionsEquiv h X L U).symm
    (frameSectionsEquiv h X L U s ≪≫
      AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.scalarIso U.unop.left
          (SheafOfModules.unit U.unop.left.ringCatSheaf)
        (unitsSections X U a).toMul)

@[simp] theorem frameAction_sections (h : EtaleLineBundleDescent.{u}) (X : Scheme.{u})
    (L : LineBundle X) (U : X.Etaleᵒᵖ) (a : (gm X).obj.obj U)
    (s : (frameSheaf h X L).obj.obj U) :
    frameSectionsEquiv h X L U (frameAction h X L U a s) =
      frameSectionsEquiv h X L U s ≪≫
        AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.scalarIso U.unop.left
            (SheafOfModules.unit U.unop.left.ringCatSheaf)
          (unitsSections X U a).toMul := (frameSectionsEquiv h X L U).apply_symm_apply _

theorem frameAction_zero (h : EtaleLineBundleDescent.{u}) (X : Scheme.{u})
    (L : LineBundle X) (U : X.Etaleᵒᵖ) (s : (frameSheaf h X L).obj.obj U) :
    frameAction h X L U 0 s = s := by
  apply (frameSectionsEquiv h X L U).injective
  rw [frameAction_sections, map_zero]
  apply Iso.ext
  change _ ≫ scalarMap U.unop.left _ 1 = _
  rw [AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.scalarMap_one,
      Category.comp_id]

theorem frameAction_add (h : EtaleLineBundleDescent.{u}) (X : Scheme.{u})
    (L : LineBundle X) (U : X.Etaleᵒᵖ) (a b : (gm X).obj.obj U)
    (s : (frameSheaf h X L).obj.obj U) :
    frameAction h X L U (a + b) s = frameAction h X L U a (frameAction h X L U b s) := by
  apply (frameSectionsEquiv h X L U).injective
  rw [frameAction_sections, frameAction_sections, frameAction_sections, map_add]
  apply Iso.ext
  change _ ≫ scalarMap U.unop.left _ ((unitsSections X U a).toMul * (unitsSections X U b).toMul
      : Γ(U.unop.left, ⊤)ˣ) =
    (_ ≫ scalarMap U.unop.left _ (unitsSections X U b).toMul) ≫
      scalarMap U.unop.left _ (unitsSections X U a).toMul
  rw [Category.assoc,
      AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.scalarMap_mul, mul_comm]
  rfl

/-- A chosen frame identifies actual global units with every other frame. -/
def frameActionEquiv (h : EtaleLineBundleDescent.{u}) (X : Scheme.{u})
    (L : LineBundle X) (U : X.Etaleᵒᵖ) (s : (frameSheaf h X L).obj.obj U) :
    (gm X).obj.obj U ≃ (frameSheaf h X L).obj.obj U :=
  (unitsSections X U).toEquiv.trans (Additive.toMul.trans
    ((AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.unitAutoEquiv
        U.unop.left).symm.trans
      ((Iso.isoCongrLeft (frameSectionsEquiv h X L U s).symm).trans
        (frameSectionsEquiv h X L U).symm)))

theorem frameActionEquiv_apply (h : EtaleLineBundleDescent.{u}) (X : Scheme.{u})
    (L : LineBundle X) (U : X.Etaleᵒᵖ) (s : (frameSheaf h X L).obj.obj U)
    (a : (gm X).obj.obj U) :
    frameActionEquiv h X L U s a = frameAction h X L U a s := by
  apply (frameSectionsEquiv h X L U).injective
  rw [frameAction_sections]
  apply Iso.ext
  simp [frameActionEquiv, Iso.isoCongrLeft, Iso.isoCongr,
      AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.unitAutoEquiv]

theorem frameAction_unique_transport (h : EtaleLineBundleDescent.{u}) (X : Scheme.{u})
    (L : LineBundle X) (U : X.Etaleᵒᵖ) (s t : (frameSheaf h X L).obj.obj U) :
    ∃! a, frameAction h X L U a s = t := by
  refine ⟨(frameActionEquiv h X L U s).symm t, ?_, ?_⟩
  · change frameAction h X L U ((frameActionEquiv h X L U s).symm t) s = t
    rw [← frameActionEquiv_apply, Equiv.apply_symm_apply]
  · intro a ha
    apply (frameActionEquiv h X L U s).injective
    rw [frameActionEquiv_apply, Equiv.apply_symm_apply, ha]

/-- Every point of every etale test scheme has an actual frame on an open neighborhood. -/
theorem frameSheaf_locally_nonempty (h : EtaleLineBundleDescent.{u}) (X : Scheme.{u})
    (L : LineBundle X) (U : X.Etale) :
    nonemptySieve (frameSheaf h X L) U ∈ Scheme.smallEtaleTopology X U := by
  change _ ∈ X.smallGrothendieckTopology @Etale U
  rw [Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology _ le_rfl,
    Scheme.mem_toGrothendieck_smallPretopology]
  intro x
  obtain ⟨W, hx, ⟨e⟩⟩ := (isLocallyRankOne_iff_restrict_unit (X := U.left)
    ((Scheme.Modules.pullback U.hom).obj L.val)).mp
      (pullback_locallyRankOne U.hom L.val L.property) x
  let V : X.Etale := Scheme.Etale.mk (W.ι ≫ U.hom)
  let f : V ⟶ U := MorphismProperty.Over.homMk W.ι rfl (by trivial)
  refine ⟨V, f, ⟨x, hx⟩, ?_, inferInstanceAs (Etale W.ι), rfl⟩
  apply Nonempty.intro
  refine (frameSectionsEquiv h X L (op V)).symm ?_
  exact ((Scheme.Modules.pullbackComp W.ι U.hom).app L.val).symm ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback W.ι).app
      ((Scheme.Modules.pullback U.hom).obj L.val)).symm ≪≫ e


/-- The literal O-linear map underlying a frame, before identifying pulled O with O. -/
def frameHom (h : EtaleLineBundleDescent.{u}) (X : Scheme.{u}) (L : LineBundle X)
    (U : X.Etaleᵒᵖ) (s : (frameSheaf h X L).obj.obj U) :
    (Scheme.Modules.pullback U.unop.hom).obj L.val ⟶
      (Scheme.Modules.pullback U.unop.hom).obj (SheafOfModules.unit X.ringCatSheaf) :=
  s.down.val.1.hom

theorem frameHom_injective (h : EtaleLineBundleDescent.{u}) (X : Scheme.{u})
    (L : LineBundle X) (U : X.Etaleᵒᵖ) : Function.Injective (frameHom h X L U) := by
  intro s t hst
  apply (frameSectionsEquiv h X L U).injective
  apply Iso.ext
  change frameHom h X L U s ≫ (pullbackUnitIso U.unop.hom).hom =
    frameHom h X L U t ≫ (pullbackUnitIso U.unop.hom).hom
  rw [hst]

/-- The scalar action is literal postcomposition on the actual module maps. -/
theorem frameHom_action (h : EtaleLineBundleDescent.{u}) (X : Scheme.{u})
    (L : LineBundle X) (U : X.Etaleᵒᵖ) (a : (gm X).obj.obj U)
    (s : (frameSheaf h X L).obj.obj U) :
    frameHom h X L U (frameAction h X L U a s) =
      frameHom h X L U s ≫ (pullbackUnitIso U.unop.hom).hom ≫
        scalarMap U.unop.left (SheafOfModules.unit U.unop.left.ringCatSheaf)
          (unitsSections X U a).toMul ≫ (pullbackUnitIso U.unop.hom).inv := by
  change ((frameHom h X L U s ≫ (pullbackUnitIso U.unop.hom).hom) ≫ _) ≫ _ = _
  simp only [Category.assoc]
  rfl


/-- The actual full-subcategory map contained in a frame section. -/
def frameRawHom (h : EtaleLineBundleDescent.{u}) (X : Scheme.{u}) (L : LineBundle X)
    (U : X.Etaleᵒᵖ) (s : (frameSheaf h X L).obj.obj U) :
    (lineBundles.presheafHom (ofLineBundle X L) (ofLineBundle X (unitBundle X))).obj
      (op ((Scheme.Etale.forget X).obj U.unop)) := s.down.val.1

theorem frameRawHom_injective (h : EtaleLineBundleDescent.{u}) (X : Scheme.{u})
    (L : LineBundle X) (U : X.Etaleᵒᵖ) : Function.Injective (frameRawHom h X L U) := by
  intro s t hst
  apply frameHom_injective h X L U
  exact congrArg (fun v => v.hom) hst

theorem frameRawHom_naturality (h : EtaleLineBundleDescent.{u}) (X : Scheme.{u})
    (L : LineBundle X) {U V : X.Etaleᵒᵖ} (f : U ⟶ V)
    (s : (frameSheaf h X L).obj.obj U) :
    frameRawHom h X L V ((frameSheaf h X L).obj.map f s) =
      (lineBundles.presheafHom (ofLineBundle X L) (ofLineBundle X (unitBundle X))).map
        ((Scheme.Etale.forget X).map f.unop).op (frameRawHom h X L U s) := rfl

theorem frameRawHom_action (h : EtaleLineBundleDescent.{u}) (X : Scheme.{u})
    (L : LineBundle X) (U : X.Etaleᵒᵖ) (a : (gm X).obj.obj U)
    (s : (frameSheaf h X L).obj.obj U) :
    frameRawHom h X L U (frameAction h X L U a s) =
      frameRawHom h X L U s ≫
          AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.transition U.unop.hom U.unop.hom
        ((unitsSections X U a).toMul : Γ(U.unop.left, ⊤)) := by
  apply ObjectProperty.hom_ext
  exact frameHom_action h X L U a s

/-- Restriction of frames commutes with the genuine represented Gm action. -/
theorem frameAction_naturality (h : EtaleLineBundleDescent.{u}) (X : Scheme.{u})
    (L : LineBundle X) {U V : X.Etaleᵒᵖ} (f : U ⟶ V) (a : (gm X).obj.obj U)
    (s : (frameSheaf h X L).obj.obj U) :
    (frameSheaf h X L).obj.map f (frameAction h X L U a s) =
      frameAction h X L V ((gm X).obj.map f a) ((frameSheaf h X L).obj.map f s) := by
  apply frameRawHom_injective h X L V
  rw [frameRawHom_naturality h X L f, frameRawHom_action h X L U a s]
  have hc := homRestriction_comp (ofLineBundle X L) (ofLineBundle X (unitBundle X))
    (ofLineBundle X (unitBundle X)) ((Scheme.Etale.forget X).map f.unop).op
    (frameRawHom h X L U s)
    (AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.transition U.unop.hom U.unop.hom
      ((unitsSections X U a).toMul : Γ(U.unop.left, ⊤)))
  rw [hc, frameRawHom_action h X L V, frameRawHom_naturality h X L f]
  apply congrArg (fun k => (lineBundles.presheafHom (ofLineBundle X L)
    (ofLineBundle X (unitBundle X))).map ((Scheme.Etale.forget X).map f.unop).op
      (frameRawHom h X L U s) ≫ k)
  change Pseudofunctor.LocallyDiscreteOpToCat.pullHom
    (AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.transition U.unop.hom U.unop.hom
      ((unitsSections X U a).toMul : Γ(U.unop.left, ⊤)))
      f.unop.left V.unop.hom V.unop.hom = _
  rw [AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.pullHom_transition]
  exact congrArg (AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.transition V.unop.hom
      V.unop.hom)
    (congrArg Units.val (unitsSections_naturality X f a)).symm

/-- The actual sheaf of O-linear frames is a Gm torsor. -/
def frameTorsor (h : EtaleLineBundleDescent.{u}) (X : Scheme.{u}) (L : LineBundle X) :
    Torsor (gm X) where
  carrier := frameSheaf h X L
  action := frameAction h X L
  zero_action := frameAction_zero h X L
  add_action := frameAction_add h X L
  naturality := frameAction_naturality h X L
  unique_transport := frameAction_unique_transport h X L
  locally_nonempty := frameSheaf_locally_nonempty h X L

end AlgebraicGeometry.Scheme.Modules.Invertible.FrameTorsor
