/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.GaloisAction
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GaloisOverlap
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.EtaleSectionDescent
public import Mathlib.RepresentationTheory.Invariants
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.InvariantSections

/-! # Original module sections as deck invariants

The actual Galois overlap and categorical sheaf amalgamation identify original
global sections with invariant original cover sections. All gluing occurs in
ModuleCat R, so scalar linearity is retained without set-theoretic choices.
No torsion or finite-generation hypothesis on the coefficient is used here.
This is section descent, not effective descent of arbitrary module sheaves.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

open Scheme.FiniteEtale
open Scheme.FiniteEtale.ProperResidue (productCover productFirst productSecond)

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable {R : Type r} [CommRing R] {X : Scheme.{u}}

/-- The actual structural arrow from the cover object to the terminal test scheme. -/
def finiteEtaleTerminalMap (Y : Scheme.FiniteEtale X) :
    (toEtale X).obj Y ⟶ etaleTerminal X :=
  MorphismProperty.Over.homMk Y.obj.hom (by simp) (by trivial)

/-- The literal original section restriction along the structural map. -/
def finiteEtaleGlobalRestriction (F : ModuleSheaf R X) (Y : Scheme.FiniteEtale X) :
    (moduleGlobalSections R X).obj F ⟶ finiteEtaleSections F Y :=
  F.obj.map (finiteEtaleTerminalMap Y).op

/-- The original structural map is a single covering arrow when it is surjective. -/
theorem finiteEtaleTerminalMap_covering (Y : Scheme.FiniteEtale X)
    [Surjective Y.obj.hom] :
    Sieve.ofArrows (fun _ : Unit => (toEtale X).obj Y)
      (fun _ => finiteEtaleTerminalMap Y) ∈ X.smallEtaleTopology (etaleTerminal X) := by
  apply Scheme.FiniteEtale.SheafDescent.etaleFamily_covering
  intro x
  obtain ⟨y, hy⟩ := Y.obj.hom.surjective x
  exact ⟨(), y, hy⟩

/-- Original global sections restrict to deck-invariant sections. -/
theorem finiteEtaleGlobalRestriction_invariant (F : ModuleSheaf R X)
    (Y : Scheme.FiniteEtale X) (s : (moduleGlobalSections R X).obj F) :
    finiteEtaleGlobalRestriction F Y s ∈ (finiteEtaleSectionsRepresentation F Y).invariants := by
  exact ModuleCat.Sheaf.ConstantRing.sectionRestriction_invariant F
    (Functor.mapAut Y (toEtale X)) (finiteEtaleTerminalMap Y)
    (fun _ => (etaleTerminalIsTerminal X).hom_ext _ _) s

/-- Restriction with codomain the native invariant submodule. -/
def finiteEtaleInvariantRestriction (F : ModuleSheaf R X) (Y : Scheme.FiniteEtale X) :
    (moduleGlobalSections R X).obj F ⟶
      ModuleCat.of R (finiteEtaleSectionsRepresentation F Y).invariants :=
  ModuleCat.Sheaf.ConstantRing.invariantRestriction F
    (Functor.mapAut Y (toEtale X)) (finiteEtaleTerminalMap Y)
    (fun _ => (etaleTerminalIsTerminal X).hom_ext _ _)

/-- Forgetting invariance gives exactly the original restriction map. -/
@[reassoc (attr := simp)]
theorem finiteEtaleInvariantRestriction_subtype (F : ModuleSheaf R X)
    (Y : Scheme.FiniteEtale X) :
    finiteEtaleInvariantRestriction F Y ≫
      ModuleCat.ofHom (finiteEtaleSectionsRepresentation F Y).invariants.subtype =
        finiteEtaleGlobalRestriction F Y := rfl

/-- The selected original self-overlap is the native pullback in the small-etale site. -/
theorem finiteEtaleOverlap_isPullback (Y : Scheme.FiniteEtale X) :
    IsPullback ((toEtale X).map (productFirst Y Y))
      ((toEtale X).map (productSecond Y Y))
      (finiteEtaleTerminalMap Y) (finiteEtaleTerminalMap Y) := by
  let lift : ∀ s : PullbackCone (finiteEtaleTerminalMap Y) (finiteEtaleTerminalMap Y),
      s.pt ⟶ (toEtale X).obj (productCover Y Y) := fun s =>
    MorphismProperty.Over.homMk
      (pullback.lift s.fst.left s.snd.left
        ((MorphismProperty.Over.w s.fst).trans (MorphismProperty.Over.w s.snd).symm)) (by
        change pullback.lift _ _ _ ≫ (pullback.fst _ _ ≫ Y.obj.hom) = s.pt.hom
        rw [← Category.assoc, pullback.lift_fst]
        exact MorphismProperty.Over.w s.fst) (by trivial)
  have hl₁ (s : PullbackCone (finiteEtaleTerminalMap Y) (finiteEtaleTerminalMap Y)) :
      lift s ≫ (toEtale X).map (productFirst Y Y) = s.fst := by
    apply MorphismProperty.Over.Hom.ext
    exact pullback.lift_fst _ _ _
  have hl₂ (s : PullbackCone (finiteEtaleTerminalMap Y) (finiteEtaleTerminalMap Y)) :
      lift s ≫ (toEtale X).map (productSecond Y Y) = s.snd := by
    apply MorphismProperty.Over.Hom.ext
    exact pullback.lift_snd _ _ _
  apply IsPullback.of_isLimit
    (c := PullbackCone.mk ((toEtale X).map (productFirst Y Y))
      ((toEtale X).map (productSecond Y Y)) ((etaleTerminalIsTerminal X).hom_ext _ _))
  refine PullbackCone.IsLimit.mk ((etaleTerminalIsTerminal X).hom_ext _ _) lift hl₁ hl₂ ?_
  intro s m h₁ h₂
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · change (m ≫ (toEtale X).map (productFirst Y Y)).left =
      (lift s ≫ (toEtale X).map (productFirst Y Y)).left
    exact congrArg (fun f => f.left) (h₁.trans (hl₁ s).symm)
  · change (m ≫ (toEtale X).map (productSecond Y Y)).left =
      (lift s ≫ (toEtale X).map (productSecond Y Y)).left
    exact congrArg (fun f => f.left) (h₂.trans (hl₂ s).symm)

variable [ConnectedSpace X] (Y : Scheme.FiniteEtale X) [PreGaloisCategory.IsGalois Y]

/-- The original deck graph family covers the original overlap in the small-etale site. -/
theorem galoisOverlapGraph_covering :
    Sieve.ofArrows (fun _ : Aut Y => (toEtale X).obj Y)
      (fun σ => (toEtale X).map (galoisOverlapGraph Y σ)) ∈
        X.smallEtaleTopology ((toEtale X).obj (productCover Y Y)) := by
  apply Scheme.FiniteEtale.SheafDescent.etaleFamily_covering
  exact galoisOverlapGraph_jointly_surjective Y

/-- Invariant linear section maps satisfy the original two-projection compatibility. -/
theorem invariantLinearSection_overlap (F : ModuleSheaf R X) {E : ModuleCat.{u + 1} R}
    (a : E ⟶ finiteEtaleSections F Y)
    (ha : ∀ σ : Aut Y, a ≫ F.obj.map ((toEtale X).map σ.hom).op = a) :
    a ≫ F.obj.map ((toEtale X).map (productFirst Y Y)).op =
      a ≫ F.obj.map ((toEtale X).map (productSecond Y Y)).op := by
  apply ModuleCat.Sheaf.ConstantRing.invariantSection_overlap F
    (Functor.mapAut Y (toEtale X))
    ((toEtale X).map (productFirst Y Y)) ((toEtale X).map (productSecond Y Y))
    (fun σ => (toEtale X).map (galoisOverlapGraph Y σ)) (galoisOverlapGraph_covering Y)
    _ _ a ha
  · intro σ
    rw [← Functor.map_comp, galoisOverlapGraph_fst, CategoryTheory.Functor.map_id]
  · intro σ
    rw [← Functor.map_comp, galoisOverlapGraph_snd]
    rfl

/-- Pairwise compatibility for the original single-cover sheaf condition. -/
theorem invariantLinearSection_compatible (F : ModuleSheaf R X)
    {E : ModuleCat.{u + 1} R} (a : E ⟶ finiteEtaleSections F Y)
    (ha : ∀ σ : Aut Y, a ≫ F.obj.map ((toEtale X).map σ.hom).op = a)
    {W : X.Etale} (b c : W ⟶ (toEtale X).obj Y) :
    a ≫ F.obj.map b.op = a ≫ F.obj.map c.op := by
  exact ModuleCat.Sheaf.ConstantRing.invariantSection_compatible F
    (Functor.mapAut Y (toEtale X)) (finiteEtaleTerminalMap Y)
    ((toEtale X).map (productFirst Y Y)) ((toEtale X).map (productSecond Y Y))
    (finiteEtaleOverlap_isPullback Y) (invariantLinearSection_overlap Y F) a ha b c
    ((etaleTerminalIsTerminal X).hom_ext _ _)

variable [Surjective Y.obj.hom]

/-- Actual categorical amalgamation of an invariant R-linear section map. -/
def invariantLinearSectionDescend (F : ModuleSheaf R X) {E : ModuleCat.{u + 1} R}
    (a : E ⟶ finiteEtaleSections F Y)
    (ha : ∀ σ : Aut Y, a ≫ F.obj.map ((toEtale X).map σ.hom).op = a) :
    E ⟶ (moduleGlobalSections R X).obj F :=
  ModuleCat.Sheaf.ConstantRing.invariantSectionDescend F
    (Functor.mapAut Y (toEtale X)) (finiteEtaleTerminalMap Y)
    (finiteEtaleTerminalMap_covering Y)
    ((toEtale X).map (productFirst Y Y)) ((toEtale X).map (productSecond Y Y))
    (finiteEtaleOverlap_isPullback Y) (invariantLinearSection_overlap Y F) a ha

/-- The descended linear map restricts to the supplied original map exactly. -/
@[reassoc (attr := simp)]
theorem invariantLinearSectionDescend_restriction (F : ModuleSheaf R X)
    {E : ModuleCat.{u + 1} R} (a : E ⟶ finiteEtaleSections F Y)
    (ha : ∀ σ : Aut Y, a ≫ F.obj.map ((toEtale X).map σ.hom).op = a) :
    invariantLinearSectionDescend Y F a ha ≫ finiteEtaleGlobalRestriction F Y = a :=
  ModuleCat.Sheaf.ConstantRing.invariantSectionDescend_restriction F
    (Functor.mapAut Y (toEtale X)) (finiteEtaleTerminalMap Y)
    (finiteEtaleTerminalMap_covering Y)
    ((toEtale X).map (productFirst Y Y)) ((toEtale X).map (productSecond Y Y))
    (finiteEtaleOverlap_isPullback Y) (invariantLinearSection_overlap Y F) a ha

omit [ConnectedSpace X] [PreGaloisCategory.IsGalois Y] [Surjective Y.obj.hom] in
/-- The native invariant-submodule inclusion is fixed under original deck restriction. -/
theorem invariantSections_subtype_fixed (F : ModuleSheaf R X) (σ : Aut Y) :
    ModuleCat.ofHom (finiteEtaleSectionsRepresentation F Y).invariants.subtype ≫
      F.obj.map ((toEtale X).map σ.hom).op =
        ModuleCat.ofHom (finiteEtaleSectionsRepresentation F Y).invariants.subtype := by
  exact ModuleCat.Sheaf.ConstantRing.invariantSections_subtype_fixed F
    (Functor.mapAut Y (toEtale X)) σ

/-- Descent of the original invariant submodule, directly in ModuleCat R. -/
def finiteEtaleInvariantDescent (F : ModuleSheaf R X) :
    ModuleCat.of R (finiteEtaleSectionsRepresentation F Y).invariants ⟶
      (moduleGlobalSections R X).obj F :=
  invariantLinearSectionDescend Y F
    (ModuleCat.ofHom (finiteEtaleSectionsRepresentation F Y).invariants.subtype)
    (invariantSections_subtype_fixed Y F)

/-- Original global sections are precisely original invariant cover sections. -/
def finiteEtaleInvariantSectionsIso (F : ModuleSheaf R X) :
    (moduleGlobalSections R X).obj F ≅
      ModuleCat.of R (finiteEtaleSectionsRepresentation F Y).invariants :=
  ModuleCat.Sheaf.ConstantRing.invariantSectionsIso F
    (Functor.mapAut Y (toEtale X)) (finiteEtaleTerminalMap Y)
    (finiteEtaleTerminalMap_covering Y)
    ((toEtale X).map (productFirst Y Y)) ((toEtale X).map (productSecond Y Y))
    (finiteEtaleOverlap_isPullback Y) (invariantLinearSection_overlap Y F)
    (fun _ => (etaleTerminalIsTerminal X).hom_ext _ _)

/-- The R-linear equivalence retains the original global-section module. -/
def finiteEtaleInvariantSectionsLinearEquiv (F : ModuleSheaf R X) :
    (moduleGlobalSections R X).obj F ≃ₗ[R]
      (finiteEtaleSectionsRepresentation F Y).invariants :=
  (finiteEtaleInvariantSectionsIso Y F).toLinearEquiv

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
