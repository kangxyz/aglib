/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pushforward
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Support
public import Aglib.AlgebraicGeometry.Modules.Pullback.FlatMorphism
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Aglib.AlgebraicGeometry.Modules.Support
public import Aglib.AlgebraicGeometry.Modules.Exact
public import Aglib.AlgebraicGeometry.Modules.Stalk.Basic
public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.Property
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeProperty
public import Aglib.CategoryTheory.SmallModel.Abelian
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.AlgebraicGeometry.Modules.Coherent.FinitePresentation
public import Aglib.AlgebraicGeometry.Modules.FinitePresentation.Locality
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Pullback
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.FinitePresentation
public import Aglib.CategoryTheory.ExactCategory.MatrixDeflation
public import Aglib.CategoryTheory.ExactCategory.Basic
public import Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.Finite.GeneralPushforward
public import Aglib.AlgebraicGeometry.Modules.Coherent.Pullback
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Pullback
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pullback
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Pullback
public import Aglib.CategoryTheory.SmallModel.Functor
public import Aglib.CategoryTheory.SmallModel.Functoriality
public import Aglib.AlgebraicGeometry.Modules.Coherent.Support.StalkFiltration
public import Aglib.AlgebraicGeometry.Morphisms.Flat.AffineStalk

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Modules.Support.FinitePushforward` at R5
revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`3cfa3afbd1e3ce7c3305e9cb8a8d7d8479de5bbd77f032b2674d1b5713009121`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.Modules
  (isZero_iff_stalks moduleStalk openBaseChange pullbackModuleStalkIso stalkFunctor support
      supportedAway supportedAway_iff_stalks supportedAway_iff_support_disjoint)
open _root_.AlgebraicGeometry.Scheme.Modules.Coherent (coherentExactPullback coherentPullback)
open _root_.AlgebraicGeometry.Scheme.Modules.QuasiCoherent (FiniteTypeSheaves
    finiteTypeSheavesToModules finiteType_support_isClosed)
open AlgebraicGeometry.Scheme.Modules.Coherent.Support
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Modules.Coherent.Support
universe u

/-- The module stalk and its underlying additive stalk detect the same zero
objects, independently of finiteness. -/
lemma moduleStalk_zero_iff {X : Scheme.{u}} (M : X.Modules) (x : X) :
    IsZero ((moduleStalk X x).obj M) ↔ IsZero ((stalkFunctor X x).obj M) := by
  rw [ModuleCat.isZero_iff_subsingleton, AddCommGrpCat.isZero_iff_subsingleton]
  rfl

/-- Pullback is zero if every point of the source avoids the original support.
This follows from the actual module-stalk extension-of-scalars comparison. -/
theorem pullback_isZero_of_support {Z X : Scheme.{u}} (f : Z ⟶ X) (M : X.Modules)
    (h : ∀ z : Z, f z ∉ support M) : IsZero ((Scheme.Modules.pullback f).obj M) := by
  apply (isZero_iff_stalks _).mpr
  intro z
  have hz : IsZero ((moduleStalk X (f z)).obj M) :=
    (moduleStalk_zero_iff M (f z)).mpr (not_not.mp (h z))
  have ht := (ModuleCat.extendScalars (f.stalkMap z).hom).map_isZero hz
  have hs : IsZero ((moduleStalk Z z).obj ((Scheme.Modules.pullback f).obj M)) :=
    ht.of_iso ((pullbackModuleStalkIso f z).app M)
  exact (moduleStalk_zero_iff _ z).mp hs

/-- Actual finite direct image has support contained in the image of the
original coherent support. The image is closed because a finite morphism is
closed; actual open base change proves vanishing on its complement. -/
theorem coherentPushforward_support_subset_image {Z X : Scheme.{u}}
    [IsLocallyNoetherian Z] [IsLocallyNoetherian X] (h : Z ⟶ X) [IsFinite h]
    (M : FiniteTypeSheaves Z) :
    support ((Scheme.Modules.QuasiCoherent.finiteTypePushforward
        h).obj M).obj ⊆ h '' support M.obj := by
  let U : X.Opens := ⟨(h '' support M.obj)ᶜ,
    (h.isClosedMap _ (finiteType_support_isClosed M)).isOpen_compl⟩
  let a : U.toScheme ⟶ X := U.ι
  let p := CategoryTheory.Limits.pullback.fst h a
  let q := CategoryTheory.Limits.pullback.snd h a
  have hpa : ∀ z : (CategoryTheory.Limits.pullback h a : Scheme), h (p z) = a (q z) := by
    intro z
    exact congrArg (fun k : CategoryTheory.Limits.pullback h a ⟶ X ↦ k z)
      (CategoryTheory.Limits.pullback.condition (f := h) (g := a))
  have hz : IsZero ((Scheme.Modules.restrictFunctor p).obj M.obj) := by
    apply (supportedAway_iff_stalks p M.obj).mpr
    intro z
    apply not_not.mp
    intro hm
    have ha : a (q z) ∉ h '' support M.obj := (q z).property
    exact ha ⟨p z, hm, hpa z⟩
  have hz' := (Scheme.Modules.pushforward q).map_isZero hz
  have hs : supportedAway a
      ((Scheme.Modules.QuasiCoherent.finiteTypePushforward h).obj M).obj :=
    hz'.of_iso ((openBaseChange h a).app M.obj)
  have hd := (supportedAway_iff_support_disjoint a _).mp hs
  rw [Set.disjoint_left, Scheme.Opens.range_ι] at hd
  intro x hx
  by_contra hn
  exact hd hx hn

/-- A useful actual stalk-CategoryTheory.Limits.pullback zero criterion for finite direct image:
no supported source point may specialize after its image to the target point. -/
theorem coherentPushforward_stalkPullback_isZero {Z X : Scheme.{u}}
    [IsLocallyNoetherian Z] [IsLocallyNoetherian X] (h : Z ⟶ X) [IsFinite h]
    (M : FiniteTypeSheaves Z) (x : X)
    (hx : ∀ y ∈ support M.obj, ¬ h y ⤳ x) :
    IsZero ((coherentPullback (X.fromSpecStalk x)).obj
      ((Scheme.Modules.QuasiCoherent.finiteTypePushforward h).obj M)) := by
  apply IsZero.of_full_of_faithful_of_isZero (finiteTypeSheavesToModules _) _
  apply pullback_isZero_of_support
  intro z hz
  obtain ⟨y, hy, heq⟩ := coherentPushforward_support_subset_image h M hz
  have hg : (X.fromSpecStalk x) z ⤳ x := by
    have hr : (X.fromSpecStalk x) z ∈ Set.range (X.fromSpecStalk x) := Set.mem_range_self z
    rwa [Scheme.range_fromSpecStalk] at hr
  exact hx y hy (heq ▸ hg)

/-- Vanishing after a flat CategoryTheory.Limits.pullback forces vanishing of the original stalk
at the image of a source point, by faithful flatness of a flat local stalk map. -/
theorem stalk_isZero_of_flat_pullback {Z X : Scheme.{u}} (f : Z ⟶ X) [Flat f]
    (M : X.Modules) (hM : IsZero ((Scheme.Modules.pullback f).obj M)) (z : Z) :
    IsZero ((stalkFunctor X (f z)).obj M) := by
  let φ : X.presheaf.stalk (f z) →+* Z.presheaf.stalk z := (f.stalkMap z).hom
  have hφ : φ.FaithfullyFlat := by
    change (f.stalkMap z).hom.FaithfullyFlat
    algebraize [(f.stalkMap z).hom]
    exact @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap f z) (f.toLRSHom.prop z)
  have := ModuleCat.reflectsIsomorphisms_extendScalars_of_faithfullyFlat hφ
  let N := (moduleStalk X (f z)).obj M
  have hz := (moduleStalk Z z).map_isZero hM
  have ht : IsZero ((ModuleCat.extendScalars φ).obj N) :=
    hz.of_iso ((pullbackModuleStalkIso f z).app M).symm
  have : IsIso ((ModuleCat.extendScalars φ).map (0 : N ⟶ N)) := ht.isIso ht _
  have : IsIso (0 : N ⟶ N) := isIso_of_reflects_iso _ (ModuleCat.extendScalars φ)
  exact (moduleStalk_zero_iff M (f z)).mp
    ((isIsoZero_iff_source_target_isZero N N).mp inferInstance).1

/-- The literal finite pushforward transported to the same upper SmallModel
that defines the actual support filtration. -/
def smallPushforward {Z X : Scheme.{u}} [IsLocallyNoetherian Z]
    [IsLocallyNoetherian X] (h : Z ⟶ X) [IsFinite h] :
    _root_.CategoryTheory.ExactCategory.ExactFunctor
        (_root_.CategoryTheory.ExactCategory.abelianExactStructure (Coh Z))
      (_root_.CategoryTheory.ExactCategory.abelianExactStructure (Coh X)) :=
  _root_.CategoryTheory.SmallModel.mapAbelianExactFunctor
    (Scheme.Modules.Coherent.Pushforward.Finite.coherentPushforwardExact h)

/-- Original coherent vanishing transfers through the canonical SmallModel
composition comparison, with no chosen replacement sheaf. -/
theorem smallPushforward_stalkPullback_isZero {Z X : Scheme.{u}}
    [IsLocallyNoetherian Z] [IsLocallyNoetherian X] (h : Z ⟶ X) [IsFinite h]
    (M : Coh Z) (x : X)
    (hz : IsZero ((coherentPullback (X.fromSpecStalk x)).obj
      ((Scheme.Modules.QuasiCoherent.finiteTypePushforward h).obj
        ((equivSmallModel.{u + 1} (FiniteTypeSheaves Z)).inverse.obj M)))) :
    (stalkPullback X x).toFunctor.kernel ((smallPushforward h).toFunctor.obj M) := by
  let : Flat (X.fromSpecStalk x) := Scheme.fromSpecStalk_flat X x
  have he := _root_.CategoryTheory.ExactCategory.ExactFunctor.smallModelCompIso.{u + 1}
    (Scheme.Modules.Coherent.Pushforward.Finite.coherentPushforwardExact h)
        (coherentExactPullback (X.fromSpecStalk x))
  have hsmall : IsZero
      (((Scheme.Modules.Coherent.Pushforward.Finite.coherentPushforwardExact h).comp
      (coherentExactPullback (X.fromSpecStalk x))).smallModel.toFunctor.obj M) :=
    (equivSmallModel.{u + 1} (FiniteTypeSheaves (Spec (X.presheaf.stalk x)))).functor.map_isZero hz
  exact hsmall.of_iso (he.app M).symm

end AlgebraicGeometry.Scheme.Modules.Coherent.Support
