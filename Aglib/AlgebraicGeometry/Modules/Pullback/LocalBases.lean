/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Locality
public import Aglib.AlgebraicGeometry.Modules.Pullback.Free
public import Aglib.AlgebraicGeometry.Modules.Support
public import Aglib.AlgebraicGeometry.Modules.Stalk.Basic
public import Aglib.Algebra.Category.ModuleCat.Sheaf.Epimorphisms
public import Aglib.AlgebraicGeometry.Modules.Exact
public import Aglib.AlgebraicGeometry.Modules.Generators.LocalLifting
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.LocalBases
public import Aglib.CategoryTheory.ExactCategory.MatrixDeflation
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.LocalSplitting
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Exact
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Pullback

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Modules.Pullback.LocalBases` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`f3c7dfa95fc4b7d1d43d9ffed90d8d0a1d140bc38f8202c989bed29801c236a8`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
attribute [local instance] Abelian.hasFiniteBiproducts
universe u
namespace AlgebraicGeometry.Scheme.Modules.Pullback

variable {X Y Z : Scheme.{u}}

/-- Inverse image on opens is final, so actual module pullback carries the unit to the unit. -/
instance opensMap_final (f : X ⟶ Y) : (Opens.map f.base).Final :=
  final_of_representablyFlat _

/-- The natural comparison between restriction followed by pullback and pullback followed by
restriction. -/
def pullbackRestrictIso (f : X ⟶ Y) (U : Y.Opens) :
    Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (f ∣_ U) ≅
      Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι :=
  (Scheme.Modules.pullbackRestrictIso f U).symm

/-- Pullback between the local slice sites, expressed through genuine open subschemes. -/
def localPullback (f : X ⟶ Y) (U : Y.Opens) :
    SheafOfModules.{u} (Y.ringCatSheaf.over U) ⥤
      SheafOfModules.{u} (X.ringCatSheaf.over (f ⁻¹ᵁ U)) :=
  (Scheme.Modules.overEquiv U).functor ⋙ Scheme.Modules.pullback (f ∣_ U) ⋙
    (Scheme.Modules.overEquiv (f ⁻¹ᵁ U)).inverse

instance localPullback_isLeftAdjoint (f : X ⟶ Y) (U : Y.Opens) :
    (localPullback f U).IsLeftAdjoint := by
  dsimp [localPullback]
  infer_instance

instance localPullback_preservesColimits (f : X ⟶ Y) (U : Y.Opens) :
    PreservesColimits (localPullback f U) := by
  dsimp [localPullback]
  infer_instance

/-- The comparison from the unit module on the inverse-image open to the local pullback of the
unit. -/
def localPullbackUnitIso (f : X ⟶ Y) (U : Y.Opens) :
    SheafOfModules.unit (X.ringCatSheaf.over (f ⁻¹ᵁ U)) ≅
      (localPullback f U).obj (SheafOfModules.unit (Y.ringCatSheaf.over U)) :=
  ((Scheme.Modules.overEquiv (f ⁻¹ᵁ U)).inverse.mapIso
    ((Scheme.Modules.pullback (f ∣_ U)).mapIso
      (U.sheafOfModulesEquivOverUnit Y.ringCatSheaf) ≪≫ pullbackUnitIso (f ∣_ U)) ≪≫
    (f ⁻¹ᵁ U).sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm

/-- Slice-site restriction commutes with actual module pullback. -/
def pullbackOverIso (f : X ⟶ Y) (U : Y.Opens) :
    SheafOfModules.overFunctor Y.ringCatSheaf U ⋙ localPullback f U ≅
      Scheme.Modules.pullback f ⋙
        SheafOfModules.overFunctor X.ringCatSheaf (f ⁻¹ᵁ U) :=
  (Functor.associator _ (Scheme.Modules.overEquiv U).functor _).symm ≪≫
    Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv U) _ ≪≫
    (Functor.associator _ (Scheme.Modules.pullback (f ∣_ U)) _).symm ≪≫
    Functor.isoWhiskerRight (pullbackRestrictIso f U) _ ≪≫
    Functor.associator (Scheme.Modules.pullback f) _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv (f ⁻¹ᵁ U)).symm _ ≪≫
        Functor.associator _ (Scheme.Modules.overEquiv (f ⁻¹ᵁ U)).functor _ ≪≫
        Functor.isoWhiskerLeft _ (Scheme.Modules.overEquiv (f ⁻¹ᵁ U)).unitIso.symm ≪≫
        Functor.rightUnitor _)

instance localPullback_additive (f : X ⟶ Y) (U : Y.Opens) :
    (localPullback f U).Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryCoproducts (localPullback f U)
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- Pull back a genuine finite local basis, without altering its index set. -/
def pullbackLocalBasis (f : X ⟶ Y) {M : Y.Modules} (U : Y.Opens)
    (G : (M.over U).GeneratingSections) :
    (((Scheme.Modules.pullback f).obj M).over (f ⁻¹ᵁ U)).GeneratingSections :=
  (G.map (localPullback f U) (localPullbackUnitIso f U)).ofEpi
    ((pullbackOverIso f U).app M).hom

instance pullbackLocalBasis_isIso (f : X ⟶ Y) {M : Y.Modules} (U : Y.Opens)
    (G : (M.over U).GeneratingSections) [IsIso G.π] :
    IsIso (pullbackLocalBasis f U G).π := by
  dsimp [pullbackLocalBasis]
  infer_instance

instance pullbackLocalBasis_isFiniteType (f : X ⟶ Y) {M : Y.Modules} (U : Y.Opens)
    (G : (M.over U).GeneratingSections) [G.IsFiniteType] :
    (pullbackLocalBasis f U G).IsFiniteType := by
  dsimp [pullbackLocalBasis]
  infer_instance

/-- Arbitrary actual scheme pullback preserves the upstream vector-bundle objects. -/
theorem exists_local_pullback_splitting {S : ShortComplex Y.Modules}
    (hS : S.ShortExact) [Scheme.Modules.IsFiniteLocallyFree Y S.X₃]
    (f : X ⟶ Y) (x : X) :
    ∃ V : X.Opens, x ∈ V ∧
      Nonempty ((S.map (Scheme.Modules.pullback f)).map
        (Scheme.Modules.overRestriction V)).Splitting := by
  obtain ⟨U, hxU, ⟨split⟩⟩ := Scheme.Modules.exists_local_splitting hS
      (f x)
  let e : Scheme.Modules.overRestriction U ⋙ localPullback f U ≅
      Scheme.Modules.pullback f ⋙ Scheme.Modules.overRestriction (f
          ⁻¹ᵁ U) :=
    pullbackOverIso f U
  exact ⟨f ⁻¹ᵁ U, hxU,
    ⟨(split.map (localPullback f U)).ofIso (S.mapNatIso e)⟩⟩

/-- Monomorphisms transfer along actual natural isomorphisms. -/
theorem mono_map_of_natIso {C D : Type*} [Category* C] [Category* D]
    {F G : C ⥤ D} (e : F ≅ G) {M N : C} (p : M ⟶ N) [Mono (F.map p)] :
    Mono (G.map p) := by
  have h : Mono (e.inv.app M ≫ F.map p ≫ e.hom.app N) := inferInstance
  have hp : e.inv.app M ≫ F.map p ≫ e.hom.app N = G.map p := by
    rw [e.hom.naturality p]
    simp
  exact hp ▸ h

theorem mono_of_stalk_mono {M N : X.Modules} (p : M ⟶ N)
    (hp : ∀ x : X, Mono ((Scheme.Modules.stalkFunctor X x).map p)) :
        Mono p := by
  apply (SheafOfModules.toSheaf X.ringCatSheaf).mono_of_mono_map
  have : ∀ x : X,
      Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((SheafOfModules.toSheaf X.ringCatSheaf).map p).hom) := hp
  exact TopCat.Presheaf.mono_of_stalk_mono _

/-- A monomorphism on one neighborhood of every point is globally a monomorphism. -/
theorem mono_of_local_mono {M N : X.Modules} (p : M ⟶ N)
    (hp : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Mono ((Scheme.Modules.overRestriction U).map p)) : Mono p := by
  apply mono_of_stalk_mono p
  intro x
  obtain ⟨U, hxU, hU⟩ := hp x
  have := hU
  let e : Scheme.Modules.overRestriction U ⋙ (Scheme.Modules.overEquiv
      U).functor ≅
      Scheme.Modules.restrictFunctor U.ι := Scheme.Modules.overFunctorEquiv U
  have : Mono (((Scheme.Modules.overRestriction U) ⋙
      (Scheme.Modules.overEquiv U).functor).map p) :=
    Functor.map_mono (Scheme.Modules.overEquiv U).functor
      ((Scheme.Modules.overRestriction U).map p)
  have : Mono ((Scheme.Modules.restrictFunctor U.ι).map p) := mono_map_of_natIso e p
  let u : U.toScheme := ⟨x, hxU⟩
  let e' : Scheme.Modules.restrictFunctor U.ι ⋙
      Scheme.Modules.stalkFunctor U.toScheme u ≅
      Scheme.Modules.stalkFunctor X x :=
          Scheme.Modules.restrictStalkNatIso U.ι u
  have : Mono ((Scheme.Modules.restrictFunctor U.ι ⋙
      Scheme.Modules.stalkFunctor U.toScheme u).map p) :=
    Functor.map_mono (Scheme.Modules.stalkFunctor U.toScheme u)
      ((Scheme.Modules.restrictFunctor U.ι).map p)
  exact mono_map_of_natIso e' p

/-- The actual pullback of a short exact sequence with finite locally free quotient
is short exact. No flatness or global splitting is assumed. -/
theorem pullback_shortExact {S : ShortComplex Y.Modules} (hS : S.ShortExact)
    [Scheme.Modules.IsFiniteLocallyFree Y S.X₃] (f : X ⟶ Y) :
    (S.map (Scheme.Modules.pullback f)).ShortExact :=
  Scheme.Modules.shortExact_pullback f hS

/- Actual vector-bundle pullback delegates to the native LocallyFree.Pullback provider. -/
end AlgebraicGeometry.Scheme.Modules.Pullback
