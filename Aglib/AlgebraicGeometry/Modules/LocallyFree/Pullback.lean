/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Locality
public import Aglib.AlgebraicGeometry.Modules.Support
public import Aglib.AlgebraicGeometry.Modules.Pullback.Free
/-!
# Pullback of genuine vector bundles

Pullback along an arbitrary scheme morphism preserves finite local bases.
The local comparison is built from the actual geometric pullback composition
isomorphisms and the identification of open restriction with pullback.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.ExactCategory
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules
variable {X Y : Scheme.{u}}

/-- A basis over the slice site of an open gives the corresponding finite
free trivialization over the actual open subscheme. -/
def restrictBasisIso (M : Y.Modules) (U : Y.Opens)
    (G : (M.over U).GeneratingSections) [IsIso G.π] :
    SheafOfModules.free (R := U.toScheme.ringCatSheaf) G.I ≅ M.restrict U.ι :=
  SheafOfModules.mapFreeIso (Scheme.Modules.overEquiv U).functor G.I
      (U.sheafOfModulesEquivOverUnit Y.ringCatSheaf).symm ≪≫
    (Scheme.Modules.overEquiv U).functor.mapIso (asIso G.π) ≪≫
    (Scheme.Modules.overFunctorEquiv U).app M

/-- Arbitrary geometric pullback preserves finite local freeness. The local
bases are pulled back on inverse-image opens and retain their finite ranks. -/
instance finiteLocallyFree_pullback (f : X ⟶ Y) (M : Y.Modules)
    [hM : IsFiniteLocallyFree Y M] :
    IsFiniteLocallyFree X ((Scheme.Modules.pullback f).obj M) := by
  obtain ⟨q, hq, hf⟩ := hM.exists_localBasis
  have hcover : TopologicalSpace.IsOpenCover q.X :=
    (Opens.coversTop_iff Y q.X).mp q.coversTop
  apply finiteLocallyFree_of_openCover _ (fun i => f ⁻¹ᵁ q.X i)
    (hcover.comap f.base.hom)
  intro i
  let := (hf.isFiniteType i).finite
  let e : SheafOfModules.free (R := (f ⁻¹ᵁ q.X i).toScheme.ringCatSheaf)
      (q.generators i).I ≅
      ((Scheme.Modules.pullback f).obj M).restrict (f ⁻¹ᵁ q.X i).ι :=
    (pullbackFreeIso (f ∣_ q.X i) (q.generators i).I).symm ≪≫
      (Scheme.Modules.pullback (f ∣_ q.X i)).mapIso
        (restrictBasisIso M (q.X i) (q.generators i)) ≪≫
      ((pullbackRestrictIso f (q.X i)).app M).symm
  exact finiteLocallyFree_of_iso e

/-- Monomorphisms of module sheaves can be checked on a neighborhood of
every point. This form is convenient for locally split sequences. -/
theorem mono_of_locally_mono {M N : X.Modules} (p : M ⟶ N)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Mono ((Scheme.Modules.restrictFunctor U.ι).map p)) : Mono p := by
  apply Preadditive.mono_of_isZero_kernel
  apply (isZero_iff_stalks _).mpr
  intro x
  obtain ⟨U, hx, hmono⟩ := h x
  have hK : supportedAway U.ι (kernel p) :=
    (isZero_kernel_of_mono ((Scheme.Modules.restrictFunctor U.ι).map p)).of_iso
      (PreservesKernel.iso (Scheme.Modules.restrictFunctor U.ι) p)
  exact (supportedAway_iff_stalks U.ι (kernel p)).mp hK ⟨x, hx⟩

/-- Arbitrary geometric pullback preserves short exact sequences with finite
locally free quotient. Only the local splittings are pulled back; no ambient
left exactness or global splitting is assumed. -/
theorem shortExact_pullback (f : X ⟶ Y) {S : ShortComplex Y.Modules}
    (hS : S.ShortExact) [IsFiniteLocallyFree Y S.X₃] :
    (S.map (Scheme.Modules.pullback f)).ShortExact := by
  have hmono : Mono ((Scheme.Modules.pullback f).map S.f) := by
    apply mono_of_locally_mono
    intro x
    obtain ⟨U, hx, ⟨s⟩⟩ := exists_local_splitting hS (f x)
    have : (Scheme.Modules.overEquiv U).functor.Additive := by
      let := preservesBinaryBiproducts_of_preservesBinaryProducts
        (Scheme.Modules.overEquiv U).functor
      exact Functor.additive_of_preservesBinaryBiproducts _
    have : (SheafOfModules.overFunctor.{u} Y.ringCatSheaf U).Additive :=
      overRestriction_additive U
    let sU : (S.map (Scheme.Modules.restrictFunctor U.ι)).Splitting :=
      (s.map (Scheme.Modules.overEquiv U).functor).ofIso
        (S.mapNatIso (Scheme.Modules.overFunctorEquiv U))
    let sV : ((S.map (Scheme.Modules.pullback f)).map
        (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι)).Splitting :=
      (sU.map (Scheme.Modules.pullback (f ∣_ U))).ofIso
        (S.mapNatIso (pullbackRestrictIso f U).symm)
    exact ⟨f ⁻¹ᵁ U, hx, sV.shortExact.mono_f⟩
  have hr := (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi
    (Scheme.Modules.pullback f)).mp inferInstance S hS
  exact { exact := hr.1, mono_f := hmono, epi_g := hr.2 }

/-- Pullback on actual vector bundles, with the same underlying module
pullback as mathlib's geometric construction. -/
def vectorBundlePullback (f : X ⟶ Y) : FiniteLocallyFree Y ⥤ FiniteLocallyFree X :=
  (finiteLocallyFree X).lift
    ((finiteLocallyFree Y).ι ⋙ Scheme.Modules.pullback f)
    (fun M => finiteLocallyFree_pullback f M.obj)

/-- Forgetting finite local freeness recovers actual sheaf pullback. -/
@[simp]
theorem vectorBundlePullback_comp_forget (f : X ⟶ Y) :
    vectorBundlePullback f ⋙ (finiteLocallyFree X).ι =
      (finiteLocallyFree Y).ι ⋙ Scheme.Modules.pullback f := rfl

instance vectorBundlePullback_additive (f : X ⟶ Y) :
    (vectorBundlePullback f).Additive := by
  dsimp [vectorBundlePullback]
  infer_instance

/-- Arbitrary pullback is exact on the genuine vector-bundle exact
structures, by local splitting of their ambient short exact sequences. -/
def vectorBundleExactPullback (f : X ⟶ Y) :
    ExactFunctor (vectorBundleExactStructure Y) (vectorBundleExactStructure X) where
  toFunctor := vectorBundlePullback f
  map_conflation S hS := by
    change ((S.map (finiteLocallyFree Y).ι).map
      (Scheme.Modules.pullback f)).ShortExact
    have : IsFiniteLocallyFree Y (S.map (finiteLocallyFree Y).ι).X₃ := S.X₃.property
    exact shortExact_pullback f hS

/-- The geometric identity comparison lifts to the actual bundle pullback. -/
def vectorBundlePullbackIdIso (X : Scheme.{u}) :
    vectorBundlePullback (𝟙 X) ≅ 𝟭 (FiniteLocallyFree X) :=
  Functor.fullyFaithfulCancelRight (finiteLocallyFree X).ι
    (Functor.isoWhiskerLeft (finiteLocallyFree X).ι (Scheme.Modules.pullbackId X))

/-- The geometric composition comparison lifts to actual vector bundles. -/
def vectorBundlePullbackCompIso {Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    vectorBundlePullback (f ≫ g) ≅ vectorBundlePullback g ⋙ vectorBundlePullback f :=
  Functor.fullyFaithfulCancelRight (finiteLocallyFree X).ι
    (Functor.isoWhiskerLeft (finiteLocallyFree Z).ι (Scheme.Modules.pullbackComp f g).symm)

/-- Actual bundle pullback agrees with the already-constructed open
restriction functor. -/
def vectorBundleRestrictIsoPullback (j : X ⟶ Y) [IsOpenImmersion j] :
    vectorBundleRestrict j ≅ vectorBundlePullback j :=
  Functor.fullyFaithfulCancelRight (finiteLocallyFree X).ι
    (Functor.isoWhiskerLeft (finiteLocallyFree Y).ι
      (Scheme.Modules.restrictFunctorIsoPullback j))

end AlgebraicGeometry.Scheme.Modules
