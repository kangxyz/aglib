/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.Modules.Pseudofunctor
public import Aglib.AlgebraicGeometry.Picard.Comparison.Endomorphisms
public import Aglib.AlgebraicGeometry.Picard.FrameTensor
public import Aglib.AlgebraicGeometry.Modules.Invertible.DualTensorEquivalence
public import Aglib.AlgebraicGeometry.Modules.Tensor.Symmetry
public import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Sites.Descent.IsPrestack

/-!
# Actual semilinear lifts of line bundles

The group of lifts is the automorphism group of the actual module sheaf in
the native pullback fibered category. A lift fixing global functions commutes
with every vertical automorphism. Consequently it commutes with every lift
whose underlying scheme automorphism is one of its powers.

The current consumer is the diagonal argument for the multiplication pairing.
No commutator identity for a Weil pairing is assumed here.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Pseudofunctor CategoryTheory.Functor Opposite Bicategory
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.Invertible.TranslationLift

universe u

/-- The total category of module sheaves over schemes for the pullback pseudofunctor;
a morphism over `f : X ⟶ Y` is a module map from the source module to `f`-pullback
of the target module. -/
abbrev Total := CoGrothendieck Scheme.Modules.pullbackPseudofunctor.{u}

/-- A line bundle regarded as its actual module in the pullback fibered category. -/
abbrev bundleObject {X : Scheme.{u}} (L : LineBundle X) : Total := ⟨X, L.val⟩

/-- Actual semilinear automorphisms, with composition inherited from pullback coherence. -/
abbrev Lift {X : Scheme.{u}} (L : LineBundle X) := Aut (bundleObject L)

/-- The scheme automorphism covered by an actual line-bundle lift. -/
def baseHom {X : Scheme.{u}} (L : LineBundle X) : Lift L →* Aut X :=
  Functor.mapAut (bundleObject L) (CoGrothendieck.forget Scheme.Modules.pullbackPseudofunctor)

/-- Multiplication by a global function, viewed over the identity scheme map. -/
def scalarEnd {X : Scheme.{u}} (L : LineBundle X) (r : Γ(X, ⊤)) : End (bundleObject L) :=
  (CoGrothendieck.ι Scheme.Modules.pullbackPseudofunctor X).map
    (Scheme.Modules.globalScalarEndomorphism X L.val r)

/-- Every vertical endomorphism of an actual line bundle is a global scalar. -/
theorem vertical_eq_scalar {X : Scheme.{u}} (L : LineBundle X)
    (b : End (bundleObject L)) (hb : b.base = 𝟙 X) :
    ∃ r : Γ(X, ⊤), b = scalarEnd L r := by
  rcases b with ⟨b, φ⟩
  change b = 𝟙 X at hb
  subst b
  obtain ⟨r, hr⟩ := Scheme.Modules.exists_eq_globalScalarEndomorphism_of_isLocallyRankOne
    L.property (φ ≫ (Scheme.Modules.pullbackId X).hom.app L.val)
  refine ⟨r, CoGrothendieck.Hom.ext _ _ rfl ?_⟩
  change φ = (Scheme.Modules.globalScalarEndomorphism X L.val r ≫
    (Scheme.Modules.pullbackId X).inv.app L.val) ≫ 𝟙 _
  rw [← hr]
  simp only [Category.assoc, Iso.hom_inv_id_app]
  exact (Category.comp_id φ).symm

/-- Scalar multiplication is natural for an actual semilinear morphism when
its underlying scheme map fixes the displayed scalar. -/
theorem scalarEnd_commute {X : Scheme.{u}} (L : LineBundle X)
    (a : End (bundleObject L)) (r : Γ(X, ⊤)) (hr : a.base.appTop r = r) :
    a ≫ scalarEnd L r = scalarEnd L r ≫ a := by
  have hi : a ≫ 𝟙 (bundleObject L) = 𝟙 (bundleObject L) ≫ a := by
    rw [Category.comp_id, Category.id_comp]
  have hn : a.fiber ≫ Scheme.Modules.globalScalarEndomorphism X
      ((Scheme.Modules.pullback a.base).obj L.val) r =
      Scheme.Modules.globalScalarEndomorphism X L.val r ≫ a.fiber :=
    (Scheme.Modules.globalScalarCenter X r).naturality a.fiber
  have hp := Scheme.Modules.pullback_map_globalScalarEndomorphism a.base L.val r
  rw [hr] at hp
  apply CoGrothendieck.Hom.ext _ _ (by
    change a.base ≫ 𝟙 X = 𝟙 X ≫ a.base
    rw [Category.comp_id, Category.id_comp])
  dsimp only [scalarEnd, CoGrothendieck.ι]
  simp only [CoGrothendieck.categoryStruct_comp_fiber,
    CoGrothendieck.categoryStruct_comp_base, Functor.map_comp, Category.assoc]
  erw [hp, reassoc_of% hn]
  simpa only [CoGrothendieck.categoryStruct_comp_fiber,
    CoGrothendieck.categoryStruct_id_fiber, CoGrothendieck.categoryStruct_id_base,
    Category.assoc] using congrArg
      (fun t => Scheme.Modules.globalScalarEndomorphism X L.val r ≫ t)
      (CoGrothendieck.Hom.congr hi)

/-- The kernel of the map from actual lifts to scheme automorphisms is central
relative to a lift that fixes the original global functions. -/
theorem commute_vertical {X : Scheme.{u}} (L : LineBundle X) (a b : Lift L)
    (ha : ∀ r : Γ(X, ⊤), a.hom.base.appTop r = r)
    (hb : baseHom L b = 1) : Commute a b := by
  have hb' : b.hom.base = 𝟙 X := congrArg Iso.hom hb
  obtain ⟨r, hr⟩ := vertical_eq_scalar L b.hom hb'
  apply Iso.ext
  change b.hom ≫ a.hom = a.hom ≫ b.hom
  rw [hr]
  exact (scalarEnd_commute L a.hom r (ha r)).symm

/-- Power comparison for actual line-bundle lifts. Its hypothesis concerns
only their underlying scheme maps, not a pairing or a commutator scalar. -/
theorem commute_of_base_eq_pow {X : Scheme.{u}} (L : LineBundle X)
    (a b : Lift L) (n : ℕ)
    (ha : ∀ r : Γ(X, ⊤), a.hom.base.appTop r = r)
    (hb : baseHom L b = baseHom L a ^ n) : Commute a b := by
  have hc : baseHom L (b * (a ^ n)⁻¹) = 1 := by
    rw [map_mul, _root_.map_inv, map_pow, hb, mul_inv_cancel]
  have h := (commute_vertical L a (b * (a ^ n)⁻¹) ha hc).mul_right
    (Commute.self_pow a n)
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using h

/-- A pullback isomorphism over a scheme automorphism gives an actual lift. -/
def ofIso {X : Scheme.{u}} (L : LineBundle X) (f : X ≅ X)
    (e : L.val ≅ (Scheme.Modules.pullback f.hom).obj L.val) : Lift L := by
  let c := CoGrothendieck.cartesianLift
    (F := Scheme.Modules.pullbackPseudofunctor) L.val f.hom
  let : IsStronglyCartesian (CoGrothendieck.forget Scheme.Modules.pullbackPseudofunctor)
      f.hom c := CoGrothendieck.isStronglyCartesian_homCartesianLift
        (F := Scheme.Modules.pullbackPseudofunctor) L.val f.hom
  let : IsIso c := IsStronglyCartesian.isIso_of_base_isIso
    (CoGrothendieck.forget Scheme.Modules.pullbackPseudofunctor) f.hom c
  exact (CoGrothendieck.ι Scheme.Modules.pullbackPseudofunctor X).mapIso e ≪≫ asIso c

/-- The constructed lift covers precisely the given scheme automorphism. -/
theorem ofIso_base {X : Scheme.{u}} (L : LineBundle X) (f : X ≅ X)
    (e : L.val ≅ (Scheme.Modules.pullback f.hom).obj L.val) :
    baseHom L (ofIso L f e) = f := by
  apply Iso.ext
  change (𝟙 X) ≫ f.hom = f.hom
  exact Category.id_comp _


open Scheme.Modules PowerPullback
open MonoidalCategory

/-- Tensor cancellation by an actual frame, retaining the unframed line bundle. -/
def cancelFrame {X Y : Scheme.{u}} (p : X ⟶ Y) (R M : LineBundle Y)
    (s : (pullback p).obj R.val ≅ SheafOfModules.unit X.ringCatSheaf) :
    (pullback p).obj (tensorLineBundle Y R M).val ≅ (pullback p).obj M.val :=
  PullbackTensor.Local.pullbackLineBundleTensorIso p R M ≪≫
    tensorSheafIso X s (Iso.refl _) ≪≫ tensorSheafLeftUnit X _

@[simp] theorem cancelFrame_hom {X Y : Scheme.{u}} (p : X ⟶ Y) (R M : LineBundle Y)
    (s : (pullback p).obj R.val ≅ SheafOfModules.unit X.ringCatSheaf) :
    (cancelFrame p R M s).hom = pullbackTensorMap p R.val M.val ≫
      tensorSheafMap X s.hom (𝟙 ((pullback p).obj M.val)) ≫
        (tensorSheafLeftUnit X ((pullback p).obj M.val)).hom := rfl

/-- Tensoring by an invertible module cannot identify two different frames. -/
theorem cancelFrame_injective {X Y : Scheme.{u}} (p : X ⟶ Y) (R M : LineBundle Y) :
    Function.Injective (cancelFrame p R M) := by
  let N := pullbackLineBundle p M
  let : (moduleTensorLeftFunctor X N.val).Faithful :=
    (lineBundleDualTensorEquivalence X N).fullyFaithfulInverse.faithful
  let : (moduleTensorRightFunctor X N.val).Faithful :=
    Functor.Faithful.of_iso (moduleTensorRightLeftIso X N.val).symm
  intro s t h
  apply Iso.ext
  apply (moduleTensorRightFunctor X N.val).map_injective
  apply (cancel_epi (PullbackTensor.Local.pullbackLineBundleTensorIso p R M).hom).mp
  apply (cancel_mono (tensorSheafLeftUnit X N.val).hom).mp
  exact congrArg Iso.hom h

set_option maxHeartbeats 400000 in
-- Elaboration compares nested native tensor, pullback, and unit comparisons;
-- the default 200000 budget is exhausted by those object identifications.
/-- The tensor-cancellation map commutes with actual frame pullback.
This is the nontrivial coherence step connecting frame transport to lifts. -/
theorem cancelFrame_pullback {X Y Z : Scheme.{u}} (p : Y ⟶ X) (R M : LineBundle X)
    (q : Z ⟶ X) (f : Z ⟶ Y) (w : f ≫ p = q)
    (s : (pullback p).obj R.val ≅ SheafOfModules.unit Y.ringCatSheaf) :
    ((pullbackCongr w).app (tensorLineBundle X R M).val).symm ≪≫
        ((pullbackComp f p).app (tensorLineBundle X R M).val).symm ≪≫
        (pullback f).mapIso (cancelFrame p R M s) ≪≫
        (pullbackComp f p).app M.val ≪≫ (pullbackCongr w).app M.val =
      cancelFrame q R M (FrameTensor.pullFrame R p q f w s) := by
  subst q
  apply Iso.ext
  change (𝟙 _) ≫ (pullbackComp f p).inv.app (tensorLineBundle X R M).val ≫
      (pullback f).map (cancelFrame p R M s).hom ≫
      (pullbackComp f p).hom.app M.val ≫ (𝟙 _) =
    pullbackTensorMap (f ≫ p) R.val M.val ≫
      tensorSheafMap Z
        ((𝟙 _) ≫ (pullbackComp f p).inv.app R.val ≫
          (pullback f).map s.hom ≫ (pullbackUnitIso f).hom)
        (𝟙 _) ≫ (tensorSheafLeftUnit Z _).hom
  simp only [Category.id_comp, Category.comp_id, cancelFrame_hom,
    Functor.map_comp, Category.assoc]
  rw [← pullbackTensorMap_leftUnit f ((pullback p).obj M.val)]
  simp only [Category.assoc]
  erw [pullbackTensorMap_naturality_assoc f s.hom (𝟙 ((pullback p).obj M.val))]
  have hc := congrArg (fun k => k ≫
      tensorSheafMap Z ((pullback f).map s.hom)
        ((pullback f).map (𝟙 ((pullback p).obj M.val))) ≫
      tensorSheafMap Z (pullbackUnitIso f).hom
        (𝟙 ((pullback f).obj ((pullback p).obj M.val))) ≫
      (tensorSheafLeftUnit Z ((pullback f).obj ((pullback p).obj M.val))).hom ≫
        (pullbackComp f p).hom.app M.val)
    (pullbackTensorMap_comp f p R.val M.val)
  simp only [Category.assoc] at hc
  refine hc.trans ?_
  erw [← UnitPower.tensorSheafLeftUnit_naturality Z ((pullbackComp f p).hom.app M.val)]
  simp only [tensorSheafMap_comp_assoc, Category.comp_id]
  erw [(pullback f).map_id ((pullback p).obj M.val)]
  simp only [Category.id_comp, Iso.inv_hom_id_app]
open CategoryTheory.Functor

/-- If an isomorphism followed by a lift is a downstairs map, the commutation
of that lift with a deck lift forces equivariance of the original isomorphism.
The proof is the actual Cartesian uniqueness property of pullback. -/
theorem equivariant_of_commuting_lift
    {C S : Type*} [Category* C] [Category* S] (π : C ⥤ S)
    {V N W Z : C} (p : π.obj N ⟶ π.obj W) (cN : N ⟶ W)
    [π.IsStronglyCartesian p cN]
    (H : V ≅ N) (A : Aut N) (B : Aut N) (D : Aut V)
    (cV : V ⟶ Z) (e : Z ⟶ W)
    (hfactor : H.hom ≫ A.hom ≫ cN = cV ≫ e)
    (hN : B.hom ≫ cN = cN) (hV : D.hom ≫ cV = cV)
    (hcomm : Commute A B)
    (hbase : π.map (D.hom ≫ H.hom ≫ A.hom) =
      π.map (H.hom ≫ B.hom ≫ A.hom)) :
    D.hom ≫ H.hom = H.hom ≫ B.hom := by
  apply (cancel_mono A.hom).mp
  simp only [Category.assoc]
  let g := π.map (D.hom ≫ H.hom ≫ A.hom)
  let : π.IsHomLift g (D.hom ≫ H.hom ≫ A.hom) := IsHomLift.map π _
  let : π.IsHomLift g (H.hom ≫ B.hom ≫ A.hom) := by
    change π.IsHomLift (π.map (D.hom ≫ H.hom ≫ A.hom)) (H.hom ≫ B.hom ≫ A.hom)
    exact Eq.mpr (congrArg (fun t => π.IsHomLift t (H.hom ≫ B.hom ≫ A.hom)) hbase)
      (IsHomLift.map π (H.hom ≫ B.hom ≫ A.hom))
  apply IsStronglyCartesian.ext π p cN g
  have hc : B.hom ≫ A.hom = A.hom ≫ B.hom := congrArg Iso.hom hcomm.eq
  simp only [Category.assoc]
  erw [← Category.assoc B.hom A.hom cN, hc, Category.assoc, hN]
  simp only [hfactor, ← Category.assoc, hV]



namespace ActualPullback

/-- The functor from the total category of module sheaves to schemes, retaining the
underlying scheme of each object and the base map of each semilinear morphism. -/
abbrev projectionFunctor : Total ⥤ Scheme.{u} :=
  CoGrothendieck.forget Scheme.Modules.pullbackPseudofunctor

/-- The original Cartesian arrow realizing module pullback. -/
abbrev projection {X Y : Scheme.{u}} (p : X ⟶ Y) (M : LineBundle Y) :
    bundleObject (pullbackLineBundle p M) ⟶ bundleObject M :=
  CoGrothendieck.cartesianLift (F := Scheme.Modules.pullbackPseudofunctor) M.val p

instance projection_cartesian {X Y : Scheme.{u}} (p : X ⟶ Y) (M : LineBundle Y) :
    projectionFunctor.IsStronglyCartesian p (projection p M) :=
  CoGrothendieck.isStronglyCartesian_homCartesianLift
    (F := Scheme.Modules.pullbackPseudofunctor) M.val p

/-- A module isomorphism over an actual scheme isomorphism. -/
def isoOver {X Y : Scheme.{u}} (L : LineBundle X) (M : LineBundle Y) (f : X ≅ Y)
    (e : L.val ≅ (pullback f.hom).obj M.val) : bundleObject L ≅ bundleObject M := by
  let c := projection f.hom M
  let : IsIso c := IsStronglyCartesian.isIso_of_base_isIso projectionFunctor f.hom c
  exact (CoGrothendieck.ι Scheme.Modules.pullbackPseudofunctor X).mapIso e ≪≫ asIso c

theorem isoOver_base {X Y : Scheme.{u}} (L : LineBundle X) (M : LineBundle Y)
    (f : X ≅ Y) (e : L.val ≅ (pullback f.hom).obj M.val) :
    projectionFunctor.map (isoOver L M f e).hom = f.hom := by
  change (𝟙 X) ≫ f.hom = f.hom
  exact Category.id_comp _

/-- Canonical deck action, defined by the actual Cartesian universal property. -/
def canonicalDeck {X Y : Scheme.{u}} (p : X ⟶ Y) (M : LineBundle Y)
    (d : Aut X) (hd : d.hom ≫ p = p) : Lift (pullbackLineBundle p M) :=
  IsStronglyCartesian.domainIsoOfBaseIso projectionFunctor (g := d) hd.symm
    (projection p M) (projection p M)

theorem canonicalDeck_base {X Y : Scheme.{u}} (p : X ⟶ Y) (M : LineBundle Y)
    (d : Aut X) (hd : d.hom ≫ p = p) :
    baseHom (pullbackLineBundle p M) (canonicalDeck p M d hd) = d := by
  apply Iso.ext
  let : projectionFunctor.IsHomLift d.hom (canonicalDeck p M d hd).hom := by
    unfold canonicalDeck
    infer_instance
  exact (IsHomLift.eq_of_isHomLift projectionFunctor
    (a := bundleObject (pullbackLineBundle p M))
    (b := bundleObject (pullbackLineBundle p M)) d.hom
    (canonicalDeck p M d hd).hom).symm

@[reassoc] theorem canonicalDeck_projection {X Y : Scheme.{u}}
    (p : X ⟶ Y) (M : LineBundle Y) (d : Aut X) (hd : d.hom ≫ p = p) :
    (canonicalDeck p M d hd).hom ≫ projection p M = projection p M :=
  IsStronglyCartesian.fac projectionFunctor p (projection p M) hd.symm (projection p M)

/-- The actual lift induced by a ratio frame, defined through Cartesian
projection maps so that their factorization is retained by construction. -/
def frameLift {X Y : Scheme.{u}} (p : X ⟶ Y) (R M : LineBundle Y)
    (a : Aut X) (b : Y ≅ Y) (w : a.hom ≫ p = p ≫ b.hom)
    (e : (tensorLineBundle Y R M).val ≅ (pullback b.hom).obj M.val)
    (s : (pullback p).obj R.val ≅ SheafOfModules.unit X.ringCatSheaf) :
    Lift (pullbackLineBundle p M) := by
  let H := (CoGrothendieck.ι Scheme.Modules.pullbackPseudofunctor X).mapIso
    (cancelFrame p R M s)
  let down := isoOver (tensorLineBundle Y R M) M b e
  let : projectionFunctor.IsHomLift b.hom down.hom := by
    rw [← isoOver_base (tensorLineBundle Y R M) M b e]
    infer_instance
  let : projectionFunctor.IsStronglyCartesian b.hom down.hom :=
    IsStronglyCartesian.of_iso projectionFunctor b.hom down
  let T := IsStronglyCartesian.domainIsoOfBaseIso projectionFunctor (g := a) w.symm
    (projection p M) (projection p (tensorLineBundle Y R M) ≫ down.hom)
  exact H.symm ≪≫ T



end ActualPullback

namespace ActualPullback

/-- The frame-defined lift retains its actual source automorphism. -/
theorem frameLift_base {X Y : Scheme.{u}} (p : X ⟶ Y) (R M : LineBundle Y)
    (a : Aut X) (b : Y ≅ Y) (w : a.hom ≫ p = p ≫ b.hom)
    (e : (tensorLineBundle Y R M).val ≅ (pullback b.hom).obj M.val)
    (s : (pullback p).obj R.val ≅ SheafOfModules.unit X.ringCatSheaf) :
    baseHom (pullbackLineBundle p M) (frameLift p R M a b w e s) = a := by
  apply Iso.ext
  change projectionFunctor.map (frameLift p R M a b w e s).hom = a.hom
  dsimp only [frameLift, Iso.trans_hom, Iso.symm_hom]
  erw [Functor.map_comp]
  change (𝟙 X) ≫ _ = a.hom
  erw [Category.id_comp]
  exact (IsHomLift.eq_of_isHomLift projectionFunctor
    (a := bundleObject (pullbackLineBundle p (tensorLineBundle Y R M)))
    (b := bundleObject (pullbackLineBundle p M)) a.hom _).symm

/-- The actual factorization defining the frame lift. -/
theorem frameLift_factor {X Y : Scheme.{u}} (p : X ⟶ Y) (R M : LineBundle Y)
    (a : Aut X) (b : Y ≅ Y) (w : a.hom ≫ p = p ≫ b.hom)
    (e : (tensorLineBundle Y R M).val ≅ (pullback b.hom).obj M.val)
    (s : (pullback p).obj R.val ≅ SheafOfModules.unit X.ringCatSheaf) :
    ((CoGrothendieck.ι pullbackPseudofunctor X).mapIso (cancelFrame p R M s)).hom ≫
      (frameLift p R M a b w e s).hom ≫ projection p M =
      projection p (tensorLineBundle Y R M) ≫
        (isoOver (tensorLineBundle Y R M) M b e).hom := by
  let down := isoOver (tensorLineBundle Y R M) M b e
  let : projectionFunctor.IsHomLift b.hom down.hom := by
    rw [← isoOver_base (tensorLineBundle Y R M) M b e]
    infer_instance
  let : projectionFunctor.IsStronglyCartesian b.hom down.hom :=
    IsStronglyCartesian.of_iso projectionFunctor b.hom down
  dsimp only [frameLift, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc]
  erw [Iso.hom_inv_id_assoc]
  exact IsStronglyCartesian.fac projectionFunctor p (projection p M) w.symm
    (projection p (tensorLineBundle Y R M) ≫ down.hom)

end ActualPullback
open CategoryTheory.Functor Pseudofunctor.LocallyDiscreteOpToCat

namespace ActualPullback

/-- The coherent deck morphism in an arbitrary native pullback pseudofunctor. -/
def pullbackDeckMorphism {C : Type*} [Category* C]
    (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat) {X Y : C} (p : X ⟶ Y)
    (M : F.obj (.mk (op Y))) (d : X ⟶ X) (hd : d ≫ p = p) :
    End (CoGrothendieck.domainCartesianLift (F := F) M p) where
  base := d
  fiber := (F.mapComp' p.op.toLoc d.op.toLoc p.op.toLoc
    (by exact congrArg (fun q : X ⟶ Y => q.op.toLoc) hd)).hom.toNatTrans.app M

/-- The explicit deck morphism preserves the original Cartesian projection. -/
theorem pullbackDeckMorphism_projection {C : Type*} [Category* C]
    (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat) {X Y : C} (p : X ⟶ Y)
    (M : F.obj (.mk (op Y))) (d : X ⟶ X) (hd : d ≫ p = p) :
    pullbackDeckMorphism F p M d hd ≫ CoGrothendieck.cartesianLift M p =
      CoGrothendieck.cartesianLift M p := by
  apply CoGrothendieck.Hom.ext _ _ hd
  simp [pullbackDeckMorphism, CoGrothendieck.cartesianLift,
    Pseudofunctor.mapComp', PrelaxFunctor.map₂_eqToHom]

/-- Native Hom restriction is conjugation by the coherent deck morphisms. -/
theorem pullbackDeckMorphism_hom {C : Type*} [Category* C]
    (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat) {X Y : C} (p : X ⟶ Y)
    (M N : F.obj (.mk (op Y))) (d : X ⟶ X) (hd : d ≫ p = p)
    (φ : (F.map p.op.toLoc).toFunctor.obj M ⟶ (F.map p.op.toLoc).toFunctor.obj N) :
    pullbackDeckMorphism F p M d hd ≫ (CoGrothendieck.ι F X).map φ =
      (CoGrothendieck.ι F X).map (pullHom φ d p p hd hd) ≫
        pullbackDeckMorphism F p N d hd := by
  apply CoGrothendieck.Hom.ext _ _ (by simp [pullbackDeckMorphism, CoGrothendieck.ι])
  simp [pullbackDeckMorphism, CoGrothendieck.ι, pullHom,
    F.mapComp_id_right_inv_app, F.mapComp_id_left_inv_app,
    Strict.leftUnitor_eqToIso, Strict.rightUnitor_eqToIso,
    PrelaxFunctor.map₂_eqToHom, ← NatTrans.naturality_assoc,
    ← Functor.map_comp_assoc, ← Cat.Hom₂.comp_app]

/-- The explicit coherent module map underlying the canonical deck lift. -/
abbrev nativeDeck {X Y : Scheme.{u}} (p : X ⟶ Y) (M : LineBundle Y)
    (d : X ⟶ X) (hd : d ≫ p = p) : End (bundleObject (pullbackLineBundle p M)) :=
  pullbackDeckMorphism pullbackPseudofunctor p M.val d hd

@[reassoc] theorem nativeDeck_projection {X Y : Scheme.{u}}
    (p : X ⟶ Y) (M : LineBundle Y) (d : X ⟶ X) (hd : d ≫ p = p) :
    nativeDeck p M d hd ≫ projection p M = projection p M :=
  pullbackDeckMorphism_projection pullbackPseudofunctor p M.val d hd

theorem canonicalDeck_hom {X Y : Scheme.{u}} (p : X ⟶ Y)
    (M : LineBundle Y) (d : Aut X) (hd : d.hom ≫ p = p) :
    (canonicalDeck p M d hd).hom = nativeDeck p M d.hom hd := by
  symm
  let : projectionFunctor.IsHomLift d.hom (nativeDeck p M d.hom hd) :=
    IsHomLift.map projectionFunctor (nativeDeck p M d.hom hd)
  apply IsStronglyCartesian.map_uniq projectionFunctor p (projection p M) hd.symm
  exact nativeDeck_projection p M d.hom hd

/-- The native Hom restriction is the literal action of canonical deck lifts. -/
theorem deck_pullHom {X Y : Scheme.{u}} (p : X ⟶ Y)
    (R M : LineBundle Y) (d : Aut X) (hd : d.hom ≫ p = p)
    (φ : (pullback p).obj R.val ⟶ (pullback p).obj M.val) :
    (canonicalDeck p R d hd).hom ≫
        (CoGrothendieck.ι pullbackPseudofunctor X).map φ =
      (CoGrothendieck.ι pullbackPseudofunctor X).map
        (pullHom (F := pullbackPseudofunctor) φ d.hom p p hd hd) ≫
        (canonicalDeck p M d hd).hom := by
  rw [canonicalDeck_hom, canonicalDeck_hom]
  exact pullbackDeckMorphism_hom pullbackPseudofunctor p R.val M.val d.hom hd φ

/-- The vertical inclusion retains every actual module morphism. -/
theorem verticalMap_injective {X : Scheme.{u}} {M N : X.Modules} :
    Function.Injective ((CoGrothendieck.ι pullbackPseudofunctor X).map :
      (M ⟶ N) → _) := by
  intro φ ψ h
  apply (cancel_mono ((pullbackPseudofunctor.mapId (.mk (op X))).inv.toNatTrans.app N)).mp
  simpa [CoGrothendieck.ι] using CoGrothendieck.Hom.congr h

end ActualPullback
open Pseudofunctor.LocallyDiscreteOpToCat

/-- Reversing equality of actual scheme maps reverses the native pullback comparison. -/
theorem pullbackCongr_symm_hom {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : f = g) (M : Y.Modules) :
    (pullbackCongr h.symm).hom.app M = (pullbackCongr h).inv.app M := by
  cases h
  rfl

/-- The tensor comparison is exactly the native Hom restriction. -/
theorem cancelFrame_pullHom {X Y : Scheme.{u}} (p : X ⟶ Y) (R M : LineBundle Y)
    (d : X ⟶ X) (hd : d ≫ p = p)
    (s : (pullback p).obj R.val ≅ SheafOfModules.unit X.ringCatSheaf) :
    pullHom (F := pullbackPseudofunctor) (cancelFrame p R M s).hom d p p hd hd =
      (cancelFrame p R M (FrameTensor.pullFrame R p p d hd s)).hom := by
  have h := congrArg Iso.hom (cancelFrame_pullback p R M p d hd s)
  dsimp only [pullHom]
  simp only [pullbackPseudofunctor_map_toFunctor]
  erw [pullbackPseudofunctor_mapComp'_hom_app p d p hd (tensorLineBundle Y R M).val,
    pullbackPseudofunctor_mapComp'_inv_app p d p hd M.val]
  rw [pullbackCongr_symm_hom hd (tensorLineBundle Y R M).val]
  simpa only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom, Category.assoc] using h

/-- A frame of an actual translation ratio is fixed by a deck translation
which is a power of its source lift. This statement contains no pairing
alternation or reciprocity premise. -/
theorem frame_fixed_of_deck_power {X Y : Scheme.{u}} (p : X ⟶ Y)
    (R M : LineBundle Y) (a : Aut X) (b : Y ≅ Y)
    (w : a.hom ≫ p = p ≫ b.hom)
    (e : (tensorLineBundle Y R M).val ≅ (pullback b.hom).obj M.val)
    (s : (pullback p).obj R.val ≅ SheafOfModules.unit X.ringCatSheaf)
    (d : Aut X) (hd : d.hom ≫ p = p) (n : ℕ) (hpow : d = a ^ n)
    (ha : ∀ r : Γ(X, ⊤), a.hom.appTop r = r) :
    FrameTensor.pullFrame R p p d.hom hd s = s := by
  let N := pullbackLineBundle p M
  let V := pullbackLineBundle p (tensorLineBundle Y R M)
  let A := ActualPullback.frameLift p R M a b w e s
  let B := ActualPullback.canonicalDeck p M d hd
  let D := ActualPullback.canonicalDeck p (tensorLineBundle Y R M) d hd
  let H := (CoGrothendieck.ι pullbackPseudofunctor X).mapIso (cancelFrame p R M s)
  let down := ActualPullback.isoOver (tensorLineBundle Y R M) M b e
  have hA : baseHom N A = a := ActualPullback.frameLift_base p R M a b w e s
  have hB : baseHom N B = d := ActualPullback.canonicalDeck_base p M d hd
  have hD : baseHom V D = d := ActualPullback.canonicalDeck_base p _ d hd
  have hAb : A.hom.base = a.hom := congrArg Iso.hom hA
  have hBb : B.hom.base = d.hom := congrArg Iso.hom hB
  have hDb : D.hom.base = d.hom := congrArg Iso.hom hD
  have hH : H.hom.base = 𝟙 X := rfl
  have hcomm : Commute A B := commute_of_base_eq_pow N A B n
    (fun r => by rw [hAb]; exact ha r) (by rw [hA, hB]; exact hpow)
  have heq : D.hom ≫ H.hom = H.hom ≫ B.hom :=
    equivariant_of_commuting_lift ActualPullback.projectionFunctor
      (V := bundleObject V) (N := bundleObject N) (W := bundleObject M)
      (Z := bundleObject (tensorLineBundle Y R M)) p (ActualPullback.projection p M) H A B D
      (ActualPullback.projection p (tensorLineBundle Y R M)) down.hom
      (ActualPullback.frameLift_factor p R M a b w e s)
      (ActualPullback.canonicalDeck_projection p M d hd)
      (ActualPullback.canonicalDeck_projection p (tensorLineBundle Y R M) d hd)
      hcomm (by
        change (D.hom ≫ H.hom ≫ A.hom).base = (H.hom ≫ B.hom ≫ A.hom).base
        simpa only [CoGrothendieck.categoryStruct_comp_base, hDb, hBb, hAb, hH] using
          (show d.hom ≫ (𝟙 X) ≫ a.hom = (𝟙 X) ≫ d.hom ≫ a.hom by simp))
  have hh : pullHom (F := pullbackPseudofunctor) (cancelFrame p R M s).hom
      d.hom p p hd hd = (cancelFrame p R M s).hom := by
    apply ActualPullback.verticalMap_injective
    apply (cancel_mono B.hom).mp
    rw [← ActualPullback.deck_pullHom p (tensorLineBundle Y R M) M d hd]
    exact heq
  apply cancelFrame_injective p R M
  apply Iso.ext
  rw [← cancelFrame_pullHom]
  exact hh

end AlgebraicGeometry.Scheme.Modules.Invertible.TranslationLift
