/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Exact
public import Aglib.AlgebraicGeometry.Modules.FinitePresentation.Transport
/-!
# Actual open restriction of vector bundles

Local bases are transported by the continuous-site pushforward implementing
geometric open restriction. The index types are unchanged, so freeness and
finiteness survive. The resulting functor is exact for the inherited
vector-bundle exact structures.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u w w' t t'
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.ExactCategory
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules

section General
variable {C : Type w} [Category.{w'} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  {D : Type t} [Category.{t'} D] {K : GrothendieckTopology D}
  {S : Sheaf K RingCat.{u}}
  [∀ U, HasSheafify (J.over U) AddCommGrpCat.{u}]
  [∀ U, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U, HasSheafify (K.over U) AddCommGrpCat.{u}]
  [∀ U, (K.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  (G : D ⥤ C) [G.IsContinuous K J] [G.IsCocontinuous K J]
  (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj R)
  (η : (SheafOfModules.pushforward φ).obj (SheafOfModules.unit R) ≅ SheafOfModules.unit S)
  [G.IsLeftAdjoint] [IsIso φ]
  [∀ U, (Over.post (X := U) G).IsContinuous (K.over U) (J.over (G.obj U))]
  [HasPullbacks C] [HasPullbacks D]

/-- Transport a local basis by a continuous, cocontinuous left adjoint on
sites which carries the structure sheaf isomorphically to the target one. -/
def pushforwardLocalBasis {M : SheafOfModules.{u} R}
    (q : SheafOfModules.LocalGeneratorsData M) [q.IsLocallyFreeData] :
    SheafOfModules.LocalGeneratorsData ((SheafOfModules.pushforward φ).obj M) :=
  (q.quasiCoherentData.pushforward G φ η
    (localBasisPushforward_preservesColimits G φ)).localGeneratorsData

instance pushforwardLocalBasis_isLocallyFreeData {M : SheafOfModules.{u} R}
    (q : SheafOfModules.LocalGeneratorsData M) [q.IsLocallyFreeData] :
    (pushforwardLocalBasis G φ η q).IsLocallyFreeData where
  isIso i := by
    dsimp [pushforwardLocalBasis, SheafOfModules.QuasicoherentData.localGeneratorsData,
      SheafOfModules.QuasicoherentData.pushforward]
    rw [SheafOfModules.Presentation.map_π_eq]
    dsimp only [SheafOfModules.LocalGeneratorsData.quasiCoherentData]
    infer_instance

instance pushforwardLocalBasis_isFiniteType {M : SheafOfModules.{u} R}
    (q : SheafOfModules.LocalGeneratorsData M) [q.IsLocallyFreeData] [hq : q.IsFiniteType] :
    (pushforwardLocalBasis G φ η q).IsFiniteType where
  isFiniteType i := by
    let := hq.isFiniteType i.2.1
    constructor
    change Finite (q.generators i.2.1).I
    infer_instance

end General

/-- Actual geometric open restriction preserves finite local freeness. -/
instance finiteLocallyFree_restrict {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : X.Modules) [hM : IsFiniteLocallyFree X M] :
    IsFiniteLocallyFree U ((Scheme.Modules.restrictFunctor j).obj M) := by
  let α : U.presheaf ⟶ j.opensFunctor.op ⋙ X.presheaf := { app V := (j.appIso V.unop).inv }
  have hα : IsIso α := NatIso.isIso_of_isIso_app _
  let φ : U.ringCatSheaf ⟶
      (j.opensFunctor.sheafPushforwardContinuous _ _ _).obj X.ringCatSheaf :=
    ⟨Functor.whiskerRight α (forget₂ CommRingCat RingCat)⟩
  have : IsIso φ := by
    rw [← isIso_iff_of_reflects_iso _ (ObjectProperty.ι _)]
    dsimp [φ]
    infer_instance
  obtain ⟨q, hq, hf⟩ := hM.exists_localBasis
  exact ⟨pushforwardLocalBasis j.opensFunctor φ (Scheme.Modules.restrictUnitIso j) q,
    inferInstance, inferInstance⟩

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Open restriction on actual finite locally free module sheaves. -/
def vectorBundleRestrict : FiniteLocallyFree X ⥤ FiniteLocallyFree U :=
  (finiteLocallyFree U).lift
    ((finiteLocallyFree X).ι ⋙ Scheme.Modules.restrictFunctor j)
    (fun M => finiteLocallyFree_restrict j M.obj)

/-- The underlying functor is exactly geometric sheaf restriction. -/
@[simp]
theorem vectorBundleRestrict_comp_forget :
    vectorBundleRestrict j ⋙ (finiteLocallyFree U).ι =
      (finiteLocallyFree X).ι ⋙ Scheme.Modules.restrictFunctor j := rfl

instance vectorBundleRestrict_additive : (vectorBundleRestrict j).Additive := by
  dsimp [vectorBundleRestrict]
  infer_instance

/-- Actual open restriction is exact for the inherited vector-bundle
structures, because ambient sheaf restriction is exact. -/
def vectorBundleExactRestrict :
    ExactFunctor (vectorBundleExactStructure X) (vectorBundleExactStructure U) where
  toFunctor := vectorBundleRestrict j
  map_conflation S hS := by
    change ((S.map (finiteLocallyFree X).ι).map
      (Scheme.Modules.restrictFunctor j)).ShortExact
    exact hS.map_of_exact _

end AlgebraicGeometry.Scheme.Modules
