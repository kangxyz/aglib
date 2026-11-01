/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.PointPurity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.FiniteClosedSupport
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.UnderlyingComposition
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Finite point-support sources and their original sum map

The source is the direct image of the native module unit on the existing
finite residue-field coproduct. Its original unit arrow is identified with
the lift of the original point-unit arrows before taking Ext.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open GroupCohomology.Kummer.Coefficients

universe u wM wA v h v' h'

namespace CategoryTheory.Limits

/-- An original biproduct projection becomes invertible when every other
summand has zero image. No replacement of the chosen biproduct is used. -/
theorem isIso_map_biproduct_π_of_isZero
    {A : Type v} [Category.{h} A] [Preadditive A]
    {B : Type v'} [Category.{h'} B] [Preadditive B]
    (F : A ⥤ B) [F.Additive] {ι : Type*} [Finite ι]
    (M : ι → A) [HasBiproduct M] (x : ι)
    (hz : ∀ y, y ≠ x → IsZero (F.obj (M y))) :
    IsIso (F.map (biproduct.π M x)) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have ht : F.map (biproduct.π M x) ≫ F.map (biproduct.ι M x) = 𝟙 _ := by
    have H := congrArg F.map (IsBilimit.total (biproduct.isBilimit M))
    rw [F.map_sum, F.map_id] at H
    rw [Finset.sum_eq_single x] at H
    · simpa only [F.map_comp] using H
    · intro y _ hy
      rw [F.map_comp, (hz y hy).eq_zero_of_tgt (F.map (biproduct.π M y)), zero_comp]
    · simp
  exact ⟨⟨F.map (biproduct.ι M x), ht, by
    rw [← F.map_comp, biproduct.ι_π_self, F.map_id]⟩⟩

end CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- The original finite-biproduct comparison keeps its original projection,
with independent index and coefficient universes. -/
@[reassoc]
theorem mapBiproduct_hom_π
    {A : Type v} [Category.{h} A] [Preadditive A]
    {B : Type v'} [Category.{h'} B] [Preadditive B]
    (F : A ⥤ B) [F.Additive] {ι : Type*} (M : ι → A)
    [HasBiproduct M] [PreservesBiproduct M F] (x : ι) :
    (F.mapBiproduct M).hom ≫ biproduct.π (F.obj ∘ M) x = F.map (biproduct.π M x) := by
  rw [mapBiproduct_hom]
  exact biproduct.lift_π (f := F.obj ∘ M) (fun j => F.map (biproduct.π M j)) x

/-- The original mapped biproduct source, together with its whole projection laws.
The given arrows and their proved equations are retained as the output projections. -/
def mapBiproductSourceIsoWitness
    {A : Type v} [Category.{h} A] [Preadditive A]
    {B : Type v'} [Category.{h'} B] [Preadditive B]
    (F : A ⥤ B) [F.Additive] {ι : Type*} (M : ι → A)
    [HasBiproduct M] [PreservesBiproduct M F] (U : A) (e : U ≅ ⨁ M)
    (P : ι → B) [HasBiproduct P] (a : ∀ x, F.obj (M x) ≅ P x)
    (p : ∀ x, U ⟶ M x) (hp : ∀ x, e.hom ≫ biproduct.π M x = p x)
    (q : ∀ x, F.obj U ⟶ P x) (hq : ∀ x, q x = F.map (p x) ≫ (a x).hom) :
    {E : F.obj U ≅ ⨁ P // ∀ x, E.hom ≫ biproduct.π P x = q x} := by
  refine ⟨F.mapIso e ≪≫ F.mapBiproduct M ≪≫ biproduct.mapIso a, ?_⟩
  intro x
  simp only [Iso.trans_hom, Functor.mapIso_hom, biproduct.mapIso_hom,
    Category.assoc, biproduct.map_π, mapBiproduct_hom_π_assoc]
  rw [← F.map_comp_assoc, hp x]
  exact (hq x).symm

end CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard
  Abelian.hasFiniteBiproducts

section ClosedCover

variable {ι : Type u} [Finite ι] {Z : Scheme.{u}} {Y : ι → Scheme.{u}}
  (a : ∀ x, Y x ⟶ Z) (n : ℕ)

/-- The actual unit-to-component arrow on a finite disjoint closed cover. -/
def moduleClosedCoverUnitMap :
    moduleUnit Z (ULift.{u + 1} (ZMod n)) ⟶
      ⨁ fun x => (moduleDirectImage (a x) (ULift.{u + 1} (ZMod n))).obj
        (moduleUnit (Y x) (ULift.{u + 1} (ZMod n))) :=
  biproduct.lift fun x => modulePointUnitMap (a x) n

@[reassoc (attr := simp)]
theorem moduleClosedCoverUnitMap_π (x : ι) :
    moduleClosedCoverUnitMap a n ≫ biproduct.π _ x = modulePointUnitMap (a x) n :=
  biproduct.lift_π _ _

variable [∀ x, IsClosedImmersion (a x)]

/-- The ORIGINAL unit map is an isomorphism for a finite disjoint closed cover.
This is a whole module statement, including the empty-cover case. -/
theorem moduleClosedCoverUnitMap_isIso
    (hcover : ∀ z : Z, ∃ (x : ι) (y : Y x), a x y = z)
    (hdisjoint : ∀ x y, x ≠ y → Disjoint (Set.range (a x)) (Set.range (a y))) :
    IsIso (moduleClosedCoverUnitMap a n) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let Λ := ULift.{u + 1} (ZMod n)
  let Q := SheafOfModules.toSheaf (constantRing Z Λ)
  suffices h : IsIso (Q.map (moduleClosedCoverUnitMap a n)) by
    let := h
    exact isIso_of_reflects_iso (moduleClosedCoverUnitMap a n) Q
  rw [(StalkUniverse.originalStalks_jointlyReflectIsomorphisms (𝟙 Z)).isIso_iff]
  intro t
  let η := FibrewiseClosed.geometricPoint t.val
  let : PreservesFiniteLimits ((pointSmallEtale η).sheafFiber
      (A := AddCommGrpCat.{u + 1})) :=
    preservesFiniteLimits_of_natIso (StalkUniverse.sheafFiberIso η)
  let : ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})).Additive :=
    Functor.additive_of_preserves_binary_products _
  let F := Q ⋙ (pointSmallEtale η).sheafFiber
  obtain ⟨x, y, hy⟩ := hcover (η default)
  obtain ⟨ζ, hζ⟩ := exists_closedImmersion_pointLift (a x) η ⟨y, hy⟩
  have hp : IsIso (F.map (modulePointUnitMap (a x) n)) := by
    let : IsIso (F.map ((moduleInverseImageAdjunction (a x) Λ).unit.app
        (moduleUnit Z Λ))) :=
      moduleClosed_unit_underlying_stalk_isIso (a x) Λ ζ η hζ (moduleUnit Z Λ)
    dsimp only [modulePointUnitMap]
    rw [F.map_comp]
    infer_instance
  have hz (z : ι) (hz : z ≠ x) :
      IsZero (F.obj ((moduleDirectImage (a z) Λ).obj (moduleUnit (Y z) Λ))) := by
    apply isZero_closedDirectImage_stalk_of_no_lift (a z) η
      (fun ξ hξ => ?_) ((SheafOfModules.toSheaf (constantRing (Y z) Λ)).obj
        (moduleUnit (Y z) Λ))
    have hm : η default ∈ Set.range (a z) :=
      ⟨ξ default, congrArg (fun k => k default) hξ⟩
    exact Set.disjoint_left.mp (hdisjoint z x hz) hm ⟨y, hy⟩
  have : IsIso (F.map (biproduct.π
      (fun x => (moduleDirectImage (a x) Λ).obj (moduleUnit (Y x) Λ)) x)) :=
    isIso_map_biproduct_π_of_isZero F _ x hz
  have H : IsIso (F.map (moduleClosedCoverUnitMap a n) ≫
      F.map (biproduct.π _ x)) := by
    rw [← F.map_comp, moduleClosedCoverUnitMap_π]
    exact hp
  exact (isIso_comp_right_iff _ _).mp H

/-- The finite closed-cover decomposition with the actual original projections. -/
def moduleClosedCoverUnitIso
    (hcover : ∀ z : Z, ∃ (x : ι) (y : Y x), a x y = z)
    (hdisjoint : ∀ x y, x ≠ y → Disjoint (Set.range (a x)) (Set.range (a y))) :
    moduleUnit Z (ULift.{u + 1} (ZMod n)) ≅
      ⨁ fun x => (moduleDirectImage (a x) (ULift.{u + 1} (ZMod n))).obj
        (moduleUnit (Y x) (ULift.{u + 1} (ZMod n))) :=
  letI := moduleClosedCoverUnitMap_isIso a n hcover hdisjoint
  asIso (moduleClosedCoverUnitMap a n)

end ClosedCover

section UnitComposition

variable {X S T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S) (n : ℕ)

private theorem moduleUnitInverseImageIso_underlying_left :
    (moduleInverseImageUnderlyingIso (ULift.{u + 1} (ZMod n)) f).inv.app
        (moduleUnit X (ULift.{u + 1} (ZMod n))) ≫
      (SheafOfModules.toSheaf (constantRing S (ULift.{u + 1} (ZMod n)))).map
        (moduleUnitInverseImageIso f n).hom =
      (inverseImage f).map (moduleUnitUnderlyingIso X (ULift.{u + 1} (ZMod n))).inv ≫
        (inverseImageConstantIso f).hom.app (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))) ≫
          (moduleUnitUnderlyingIso S (ULift.{u + 1} (ZMod n))).hom := by
  rw [moduleUnitInverseImageIso_underlying]
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

/-- The selected native unit transports compose as whole module arrows. -/
@[reassoc]
theorem moduleUnitInverseImageIso_comp :
    (moduleInverseImageCompIso (ULift.{u + 1} (ZMod n)) f g).hom.app
        (moduleUnit X (ULift.{u + 1} (ZMod n))) ≫
      (moduleInverseImage g (ULift.{u + 1} (ZMod n))).map (moduleUnitInverseImageIso f n).hom ≫
        (moduleUnitInverseImageIso g n).hom = (moduleUnitInverseImageIso (g ≫ f) n).hom := by
  let Λ := ULift.{u + 1} (ZMod n)
  let Q := SheafOfModules.toSheaf (constantRing T Λ)
  apply Q.map_injective
  simp only [CategoryTheory.Functor.map_comp]
  apply (cancel_epi ((moduleInverseImageUnderlyingIso Λ (g ≫ f)).inv.app
    (moduleUnit X Λ))).mp
  have hc := moduleInverseImageUnderlyingIso_inv_comp Λ f g (moduleUnit X Λ)
  have hg := (moduleInverseImageUnderlyingIso Λ g).inv.naturality
    (moduleUnitInverseImageIso f n).hom
  simp only [CategoryTheory.Functor.comp_map] at hg
  calc
    _ = (inverseImageComp f g).hom.app
          ((SheafOfModules.toSheaf (constantRing X Λ)).obj (moduleUnit X Λ)) ≫
        (inverseImage g).map ((moduleInverseImageUnderlyingIso Λ f).inv.app
          (moduleUnit X Λ)) ≫
        (inverseImage g).map
          ((SheafOfModules.toSheaf (constantRing S Λ)).map (moduleUnitInverseImageIso f n).hom) ≫
        (moduleInverseImageUnderlyingIso Λ g).inv.app (moduleUnit S Λ) ≫
          Q.map (moduleUnitInverseImageIso g n).hom := by
      rw [← Category.assoc, ← Category.assoc, ← hc]
      simp only [Category.assoc]
      rw [← reassoc_of% hg]
    _ = (inverseImageComp f g).hom.app
          ((SheafOfModules.toSheaf (constantRing X Λ)).obj (moduleUnit X Λ)) ≫
        (inverseImage g).map ((inverseImage f).map (moduleUnitUnderlyingIso X Λ).inv) ≫
        (inverseImage g).map ((inverseImageConstantIso f).hom.app (AddCommGrpCat.of Λ)) ≫
        (inverseImageConstantIso g).hom.app (AddCommGrpCat.of Λ) ≫
          (moduleUnitUnderlyingIso T Λ).hom := by
      rw [← CategoryTheory.Functor.map_comp_assoc, moduleUnitInverseImageIso_underlying_left,
        moduleUnitInverseImageIso_underlying_left]
      simp only [CategoryTheory.Functor.map_comp, Category.assoc]
      rw [← (inverseImage g).map_comp_assoc (moduleUnitUnderlyingIso S Λ).hom
        (moduleUnitUnderlyingIso S Λ).inv, Iso.hom_inv_id,
        CategoryTheory.Functor.map_id, Category.id_comp]
    _ = (inverseImage (g ≫ f)).map (moduleUnitUnderlyingIso X Λ).inv ≫
        (inverseImageConstantIso (g ≫ f)).hom.app (AddCommGrpCat.of Λ) ≫
          (moduleUnitUnderlyingIso T Λ).hom := by
      have hn := (inverseImageComp f g).hom.naturality (moduleUnitUnderlyingIso X Λ).inv
      simp only [CategoryTheory.Functor.comp_map] at hn
      rw [← reassoc_of% hn, reassoc_of% (inverseImageComp_constant f g (AddCommGrpCat.of Λ))]
    _ = _ := (moduleUnitInverseImageIso_underlying_left (g ≫ f) n).symm

/-- Original point-unit arrows compose through the specified native direct-image iso. -/
@[reassoc]
theorem modulePointUnitMap_comp :
    modulePointUnitMap f n ≫
      (moduleDirectImage f (ULift.{u + 1} (ZMod n))).map (modulePointUnitMap g n) ≫
        (moduleDirectImageCompIso (ULift.{u + 1} (ZMod n)) f g).inv.app
          (moduleUnit T (ULift.{u + 1} (ZMod n))) = modulePointUnitMap (g ≫ f) n := by
  let Λ := ULift.{u + 1} (ZMod n)
  have hu := moduleInverseImageCompIso_unit Λ f g (moduleUnit X Λ)
  have hn := (moduleInverseImageAdjunction g Λ).unit.naturality
    (moduleUnitInverseImageIso f n).hom
  have ht := (moduleDirectImageCompIso Λ f g).inv.naturality
    ((moduleInverseImage g Λ).map (moduleUnitInverseImageIso f n).hom ≫
      (moduleUnitInverseImageIso g n).hom)
  simp only [Functor.id_map, CategoryTheory.Functor.comp_map] at hn
  simp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.map_comp, Category.assoc] at ht
  simp only [Adjunction.comp_unit_app] at hu
  simp only [modulePointUnitMap, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← (moduleDirectImage f Λ).map_comp_assoc, hn, CategoryTheory.Functor.map_comp_assoc]
  rw [ht]
  rw [← Category.assoc, ← hu]
  simp only [Category.assoc]
  have he := (moduleDirectImageCompIso Λ f g).hom_inv_id_app
    ((moduleInverseImage g Λ).obj ((moduleInverseImage f Λ).obj (moduleUnit X Λ)))
  erw [reassoc_of% he]
  simpa only [(moduleDirectImage (g ≫ f) Λ).map_comp, Category.assoc] using
    congrArg (fun b => (moduleInverseImageAdjunction (g ≫ f) Λ).unit.app (moduleUnit X Λ) ≫
      (moduleDirectImage (g ≫ f) Λ).map b) (moduleUnitInverseImageIso_comp f g n)

end UnitComposition

/-- Equality transport of the actual supporting morphism preserves its original unit. -/
theorem modulePointUnitMap_eqToHom {Z X : Scheme.{u}} (n : ℕ) {f g : Z ⟶ X} (h : f = g) :
    modulePointUnitMap f n ≫
        eqToHom (congrArg (fun a : Z ⟶ X =>
          (moduleDirectImage a (ULift.{u + 1} (ZMod n))).obj
            (moduleUnit Z (ULift.{u + 1} (ZMod n)))) h) =
      modulePointUnitMap g n := by
  subst g
  simp only [eqToHom_refl, Category.comp_id]

/-- The actual unit projection for two composable supporting morphisms. -/
def modulePointUnitProjection {X S T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S) (n : ℕ) :
    (moduleDirectImage f (ULift.{u + 1} (ZMod n))).obj
        (moduleUnit S (ULift.{u + 1} (ZMod n))) ⟶
      (moduleDirectImage (g ≫ f) (ULift.{u + 1} (ZMod n))).obj
        (moduleUnit T (ULift.{u + 1} (ZMod n))) :=
  (moduleDirectImage f (ULift.{u + 1} (ZMod n))).map (modulePointUnitMap g n) ≫
    (moduleDirectImageCompIso (ULift.{u + 1} (ZMod n)) f g).inv.app
      (moduleUnit T (ULift.{u + 1} (ZMod n)))

/-- The original projection composition law before native source specialization. -/
theorem modulePointUnitProjection_unit {X S T : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) (n : ℕ) :
    modulePointUnitMap f n ≫ modulePointUnitProjection f g n =
      modulePointUnitMap (g ≫ f) n := modulePointUnitMap_comp f g n

/-- The original whole direct-image comparison, followed by the supporting-map equality. -/
def modulePointUnitProjectionIso {X S T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S)
    (a : T ⟶ X) (h : g ≫ f = a) (n : ℕ) :
    (moduleDirectImage f (ULift.{u + 1} (ZMod n))).obj
        ((moduleDirectImage g (ULift.{u + 1} (ZMod n))).obj
          (moduleUnit T (ULift.{u + 1} (ZMod n)))) ≅
      (moduleDirectImage a (ULift.{u + 1} (ZMod n))).obj
        (moduleUnit T (ULift.{u + 1} (ZMod n))) :=
  ((moduleDirectImageCompIso (ULift.{u + 1} (ZMod n)) f g).app
    (moduleUnit T (ULift.{u + 1} (ZMod n)))).symm ≪≫
      eqToIso (congrArg (fun b : T ⟶ X =>
        (moduleDirectImage b (ULift.{u + 1} (ZMod n))).obj
          (moduleUnit T (ULift.{u + 1} (ZMod n)))) h)

/-- The whole coefficient comparison keeps the actual composition and equality arrows. -/
theorem modulePointUnitProjectionIso_hom {X S T : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) (a : T ⟶ X) (h : g ≫ f = a) (n : ℕ) :
    (modulePointUnitProjectionIso f g a h n).hom =
      (moduleDirectImageCompIso (ULift.{u + 1} (ZMod n)) f g).inv.app
          (moduleUnit T (ULift.{u + 1} (ZMod n))) ≫
        eqToHom (congrArg (fun b : T ⟶ X =>
          (moduleDirectImage b (ULift.{u + 1} (ZMod n))).obj
            (moduleUnit T (ULift.{u + 1} (ZMod n)))) h) := rfl

/-- The SAME projection through its original whole coefficient comparison. -/
def modulePointUnitProjectionOfEq {X S T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S)
    (a : T ⟶ X) (h : g ≫ f = a) (n : ℕ) :
    (moduleDirectImage f (ULift.{u + 1} (ZMod n))).obj
        (moduleUnit S (ULift.{u + 1} (ZMod n))) ⟶
      (moduleDirectImage a (ULift.{u + 1} (ZMod n))).obj
        (moduleUnit T (ULift.{u + 1} (ZMod n))) :=
  (moduleDirectImage f (ULift.{u + 1} (ZMod n))).map (modulePointUnitMap g n) ≫
    (modulePointUnitProjectionIso f g a h n).hom

/-- The whole original comparison retains the literal composition/equality map. -/
theorem modulePointUnitProjectionOfEq_original {X S T : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) (a : T ⟶ X) (h : g ≫ f = a) (n : ℕ) :
    modulePointUnitProjectionOfEq f g a h n =
      modulePointUnitProjection f g n ≫ eqToHom (congrArg (fun b : T ⟶ X =>
        (moduleDirectImage b (ULift.{u + 1} (ZMod n))).obj
          (moduleUnit T (ULift.{u + 1} (ZMod n)))) h) := by
  rw [modulePointUnitProjectionOfEq, modulePointUnitProjectionIso_hom,
    modulePointUnitProjection]
  exact (Category.assoc _ _ _).symm

/-- Equality-transport coherence for the whole original projection and unit. -/
theorem modulePointUnitProjectionOfEq_unit {X S T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S)
    (a : T ⟶ X) (h : g ≫ f = a) (n : ℕ) :
    modulePointUnitMap f n ≫ modulePointUnitProjectionOfEq f g a h n =
      modulePointUnitMap a n := by
  rw [modulePointUnitProjectionOfEq_original, ← Category.assoc, modulePointUnitProjection_unit]
  exact modulePointUnitMap_eqToHom n h

section SigmaSource

variable {ι : Type u} (Y : ι → Scheme.{u}) {X : Scheme.{u}}
  (a : ∀ x, Y x ⟶ X) (n : ℕ)

/-- The single native type of the original coproduct projection family and
its operational laws, shared by the constructor and every thin instance. -/
structure ModuleSigmaPointProjectionFamily where
  /-- The original projections from the pushed-forward coproduct unit. -/
  projection : ∀ x,
    (moduleDirectImage (Sigma.desc a) (ULift.{u + 1} (ZMod n))).obj
        (moduleUnit (∐ Y) (ULift.{u + 1} (ZMod n))) ⟶
      (moduleDirectImage (a x) (ULift.{u + 1} (ZMod n))).obj
        (moduleUnit (Y x) (ULift.{u + 1} (ZMod n)))
  formula : ∀ x, projection x =
    (moduleDirectImage (Sigma.desc a) (ULift.{u + 1} (ZMod n))).map
        (modulePointUnitMap (Sigma.ι Y x) n) ≫
      (modulePointUnitProjectionIso (Sigma.desc a) (Sigma.ι Y x) (a x)
        (Sigma.ι_comp_desc a x) n).hom
  unit : ∀ x, modulePointUnitMap (Sigma.desc a) n ≫ projection x = modulePointUnitMap (a x) n

/-- Construct the original maps and ALL laws before residue-field specialization.
No law is supplied as an input to this native constructor. -/
def moduleSigmaPointProjectionFamily : ModuleSigmaPointProjectionFamily Y a n where
  projection x := modulePointUnitProjectionOfEq (Sigma.desc a) (Sigma.ι Y x) (a x)
    (Sigma.ι_comp_desc a x) n
  formula _ := rfl
  unit x := modulePointUnitProjectionOfEq_unit (Sigma.desc a) (Sigma.ι Y x) (a x)
    (Sigma.ι_comp_desc a x) n

variable [Finite ι]

/-- The original source iso with its projection/unit laws. This is an output
of the complete construction, with the SAME projection family as a parameter. -/
structure ModuleSigmaPointSourceDecomposition (p : ModuleSigmaPointProjectionFamily Y a n) where
  /-- The original direct-image and finite-biproduct comparison. -/
  iso : (moduleDirectImage (Sigma.desc a) (ULift.{u + 1} (ZMod n))).obj
      (moduleUnit (∐ Y) (ULift.{u + 1} (ZMod n))) ≅
    ⨁ fun x => (moduleDirectImage (a x) (ULift.{u + 1} (ZMod n))).obj
      (moduleUnit (Y x) (ULift.{u + 1} (ZMod n)))
  projection : ∀ x, iso.hom ≫ biproduct.π _ x = p.projection x
  unit : modulePointUnitMap (Sigma.desc a) n ≫ iso.hom =
    biproduct.lift (fun x => modulePointUnitMap (a x) n)

variable [∀ x, IsClosedImmersion (Sigma.ι Y x)]

/-- The complete original coproduct-unit source construction and ALL whole
projection/unit laws, over variable schemes and maps. -/
def moduleSigmaPointSourceIsoWitness :
    ModuleSigmaPointSourceDecomposition Y a n (moduleSigmaPointProjectionFamily Y a n) := by
  let Λ := ULift.{u + 1} (ZMod n)
  let e := moduleClosedCoverUnitIso (fun x => Sigma.ι Y x) n
    (fun z => by
      obtain ⟨⟨x, y⟩, rfl⟩ := (sigmaMk Y).surjective z
      exact ⟨x, y, (sigmaMk_mk Y x y).symm⟩)
    (fun x y hxy => TopologicalSpace.Opens.coe_disjoint.mpr (disjoint_opensRange_sigmaι Y x y hxy))
  let F := moduleDirectImage (Sigma.desc a) Λ
  let M := fun x => (moduleDirectImage (Sigma.ι Y x) Λ).obj (moduleUnit (Y x) Λ)
  let : F.IsRightAdjoint := (moduleInverseImageAdjunction (Sigma.desc a) Λ).isRightAdjoint
  let : PreservesBiproduct M F := preservesBiproduct_of_preservesProduct _
  let E := F.mapBiproductSourceIsoWitness M (moduleUnit (∐ Y) Λ) e
    (fun x => (moduleDirectImage (a x) Λ).obj (moduleUnit (Y x) Λ))
    (fun x => modulePointUnitProjectionIso (Sigma.desc a) (Sigma.ι Y x) (a x)
      (Sigma.ι_comp_desc a x) n)
    (fun x => modulePointUnitMap (Sigma.ι Y x) n)
    (fun x => moduleClosedCoverUnitMap_π (fun x => Sigma.ι Y x) n x)
    (moduleSigmaPointProjectionFamily Y a n).projection
    (moduleSigmaPointProjectionFamily Y a n).formula
  refine ⟨E.val, E.property, ?_⟩
  apply biproduct.hom_ext
  intro x
  rw [Category.assoc, E.property x, (moduleSigmaPointProjectionFamily Y a n).unit x,
    biproduct.lift_π]

end SigmaSource

section FiniteSource

open Curves.FiniteClosedSupport

variable (X : Scheme.{u}) (D : Set X) (n : ℕ)

/-- The actual module unit on the existing residue-field coproduct, pushed to X. -/
abbrev moduleFinitePointSource : ModuleSheaf X (ULift.{u + 1} (ZMod n)) :=
  (moduleDirectImage (inclusion X D) (ULift.{u + 1} (ZMod n))).obj
    (moduleUnit (pointScheme X D) (ULift.{u + 1} (ZMod n)))

/-- The SAME whole family construction, at the original residue-field maps. -/
def moduleFinitePointProjectionFamily :
    ModuleSigmaPointProjectionFamily (fun x : D => Spec (X.residueField x.val))
      (fun x : D => X.fromSpecResidueField x.val) n :=
  moduleSigmaPointProjectionFamily (fun x : D => Spec (X.residueField x.val))
    (fun x : D => X.fromSpecResidueField x.val) n

/-- The canonical projection out of the original supported module source. -/
def moduleFinitePointProjection (x : D) :
    moduleFinitePointSource X D n ⟶
      (moduleDirectImage (X.fromSpecResidueField x.val) (ULift.{u + 1} (ZMod n))).obj
        (moduleUnit (Spec (X.residueField x.val)) (ULift.{u + 1} (ZMod n))) :=
  (moduleFinitePointProjectionFamily X D n).projection x

/-- The original unit law from the SAME whole family, before Ext. -/
@[reassoc]
theorem moduleFinitePointProjection_unit (x : D) :
    modulePointUnitMap (inclusion X D) n ≫ moduleFinitePointProjection X D n x =
      modulePointUnitMap (X.fromSpecResidueField x.val) n :=
  (moduleFinitePointProjectionFamily X D n).unit x

variable [Finite D] (hclosed : ∀ x ∈ D, IsClosed ({x} : Set X))

include hclosed in
/-- Each original component is closed, as are its composite and the support inclusion. -/
theorem moduleFinitePointComponent_closed (x : D) :
    IsClosedImmersion (Sigma.ι (fun x : D => Spec (X.residueField x.val)) x) := by
  let := inclusion_isClosedImmersion X D (Set.toFinite D) hclosed
  let : IsClosedImmersion (X.fromSpecResidueField x.val) :=
    isClosed_singleton_iff_isClosedImmersion.mp (hclosed x.val x.property)
  have : IsClosedImmersion
      (Sigma.ι (fun x : D => Spec (X.residueField x.val)) x ≫ inclusion X D) := by
    rw [component_inclusion]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (inclusion X D)

/-- The complete original coproduct construction at the SAME finite point model. -/
def moduleFinitePointSourceIsoWitness :
    ModuleSigmaPointSourceDecomposition (fun x : D => Spec (X.residueField x.val))
      (fun x : D => X.fromSpecResidueField x.val) n (moduleFinitePointProjectionFamily X D n) := by
  let Y := fun x : D => Spec (X.residueField x.val)
  let : ∀ x : D, IsClosedImmersion (Sigma.ι Y x) :=
    moduleFinitePointComponent_closed X D hclosed
  exact moduleSigmaPointSourceIsoWitness Y (fun x : D => X.fromSpecResidueField x.val) n

/-- The original source is the finite biproduct of the original point units,
through the SAME complete construction. Empty D is included. -/
def moduleFinitePointSourceIso :
    moduleFinitePointSource X D n ≅
      ⨁ fun x : D =>
        (moduleDirectImage (X.fromSpecResidueField x.val) (ULift.{u + 1} (ZMod n))).obj
          (moduleUnit (Spec (X.residueField x.val)) (ULift.{u + 1} (ZMod n))) :=
  (moduleFinitePointSourceIsoWitness X D n hclosed).iso

/-- The whole source iso has the original projections from its SAME construction. -/
@[reassoc (attr := simp)]
theorem moduleFinitePointSourceIso_hom_π (x : D) :
    (moduleFinitePointSourceIso X D n hclosed).hom ≫ biproduct.π _ x =
      moduleFinitePointProjection X D n x :=
  (moduleFinitePointSourceIsoWitness X D n hclosed).projection x

/-- The ORIGINAL supported unit becomes the lift of the original point-unit
arrows as a whole module map, before applying any cohomology functor. -/
theorem moduleFinitePointSourceIso_unit :
    modulePointUnitMap (inclusion X D) n ≫ (moduleFinitePointSourceIso X D n hclosed).hom =
      biproduct.lift (fun x : D => modulePointUnitMap (X.fromSpecResidueField x.val) n) :=
  (moduleFinitePointSourceIsoWitness X D n hclosed).unit

/-- Scalar forgetting preserves the WHOLE original finite-source unit triangle. -/
theorem moduleFinitePointSourceIso_underlying_unit :
    (SheafOfModules.toSheaf (constantRing X (ULift.{u + 1} (ZMod n)))).map
        (modulePointUnitMap (inclusion X D) n) ≫
      (SheafOfModules.toSheaf (constantRing X (ULift.{u + 1} (ZMod n)))).map
        (moduleFinitePointSourceIso X D n hclosed).hom =
      (SheafOfModules.toSheaf (constantRing X (ULift.{u + 1} (ZMod n)))).map
        (biproduct.lift (fun x : D => modulePointUnitMap (X.fromSpecResidueField x.val) n)) := by
  let Q := SheafOfModules.toSheaf (constantRing X (ULift.{u + 1} (ZMod n)))
  exact (Q.map_comp _ _).symm.trans
    (congrArg Q.map (moduleFinitePointSourceIso_unit X D n hclosed))

end FiniteSource

section FiniteExt

open Curves.FiniteClosedSupport

variable (X : Scheme.{u}) (D : Set X) [Finite D] (n : ℕ)
  (hclosed : ∀ x ∈ D, IsClosed ({x} : Set X))
  [HasExt.{wM} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]

/-- The finite index instance shared by the original Ext reconstruction sums. -/
local instance finiteExtFintype : Fintype D := Fintype.ofFinite D

/-- All-degree Ext decomposition of the ACTUAL supported module source,
through its original source iso and the native finite-biproduct comparison. -/
def moduleFinitePointExtAddEquiv
    (N : ModuleSheaf X (ULift.{u + 1} (ZMod n))) (q : ℕ) :
    Ext.{wM} (moduleFinitePointSource X D n) N q ≃+
      ∀ x : D, Ext.{wM}
        ((moduleDirectImage (X.fromSpecResidueField x.val) (ULift.{u + 1} (ZMod n))).obj
          (moduleUnit (Spec (X.residueField x.val)) (ULift.{u + 1} (ZMod n)))) N q :=
  (by
    let e : Ext.{wM} (moduleFinitePointSource X D n) N q ≃+
        Ext.{wM} (⨁ fun x : D =>
          (moduleDirectImage (X.fromSpecResidueField x.val) (ULift.{u + 1} (ZMod n))).obj
            (moduleUnit (Spec (X.residueField x.val)) (ULift.{u + 1} (ZMod n)))) N q :=
      (((extFunctor q).mapIso (moduleFinitePointSourceIso X D n hclosed).symm.op).app N)
        |>.addCommGroupIsoToAddEquiv
    exact e.trans (Ext.biproductAddEquiv (biproduct.isBilimit _) N q))

/-- Coordinates use the actual injections obtained from the original source iso. -/
theorem moduleFinitePointExtAddEquiv_apply
    (N : ModuleSheaf X (ULift.{u + 1} (ZMod n))) (q : ℕ)
    (e : Ext.{wM} (moduleFinitePointSource X D n) N q) (x : D) :
    moduleFinitePointExtAddEquiv X D n hclosed N q e x =
      (Ext.mk₀ (biproduct.ι _ x ≫ (moduleFinitePointSourceIso X D n hclosed).inv)).comp
        e (zero_add q) := by
  change (Ext.mk₀ (biproduct.ι _ x)).comp
    ((Ext.mk₀ (moduleFinitePointSourceIso X D n hclosed).inv).comp e (zero_add q))
      (zero_add q) = _
  rw [Ext.mk₀_comp_mk₀_assoc]

/-- Reconstruction is the sum of precompositions by the ORIGINAL supported projections. -/
theorem moduleFinitePointExtAddEquiv_symm_apply
    (N : ModuleSheaf X (ULift.{u + 1} (ZMod n))) (q : ℕ)
    (e : ∀ x : D, Ext.{wM}
      ((moduleDirectImage (X.fromSpecResidueField x.val) (ULift.{u + 1} (ZMod n))).obj
        (moduleUnit (Spec (X.residueField x.val)) (ULift.{u + 1} (ZMod n)))) N q) :
    (moduleFinitePointExtAddEquiv X D n hclosed N q).symm e =
      ∑ x : D, (Ext.mk₀ (moduleFinitePointProjection X D n x)).comp (e x) (zero_add q) := by
  change (Ext.mk₀ (moduleFinitePointSourceIso X D n hclosed).hom).comp
    (∑ x : D, (Ext.mk₀ (biproduct.π _ x)).comp (e x) (zero_add q)) (zero_add q) = _
  rw [Ext.comp_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Ext.mk₀_comp_mk₀_assoc, moduleFinitePointSourceIso_hom_π]

/-- The whole decomposition commutes with each original coefficient morphism. -/
theorem moduleFinitePointExtAddEquiv_naturality
    {N N' : ModuleSheaf X (ULift.{u + 1} (ZMod n))} (b : N ⟶ N') (q : ℕ)
    (e : Ext.{wM} (moduleFinitePointSource X D n) N q) :
    moduleFinitePointExtAddEquiv X D n hclosed N' q
        (e.comp (Ext.mk₀ b) (add_zero q)) =
      fun x => (moduleFinitePointExtAddEquiv X D n hclosed N q e x).comp
        (Ext.mk₀ b) (add_zero q) := by
  funext x
  rw [moduleFinitePointExtAddEquiv_apply, moduleFinitePointExtAddEquiv_apply]
  exact (Ext.comp_assoc_of_third_deg_zero _ _ _ (zero_add q)).symm

variable [HasExt.{wA} (AbelianSheaf.{u, u + 1} X)]

omit [Finite D] hclosed in
/-- The original finite-support forgetting map restricts to the original point map. -/
theorem moduleFinitePointProjection_extToCohomology (q : ℕ) (x : D)
    (e : Ext.{wM}
      ((moduleDirectImage (X.fromSpecResidueField x.val) (ULift.{u + 1} (ZMod n))).obj
        (moduleUnit (Spec (X.residueField x.val)) (ULift.{u + 1} (ZMod n))))
      (moduleRootsOfUnity X n) q) :
    modulePointExtToCohomology (inclusion X D) n q
        ((Ext.mk₀ (moduleFinitePointProjection X D n x)).comp e (zero_add q)) =
      modulePointExtToCohomology (X.fromSpecResidueField x.val) n q e := by
  rw [modulePointExtToCohomology_apply, modulePointExtToCohomology_apply,
    Ext.mk₀_comp_mk₀_assoc, moduleFinitePointProjection_unit]

/-- Actual support forgetting is the SUM of the actual original point operators. -/
theorem moduleFinitePointExtToCohomology_sum (q : ℕ)
    (e : Ext.{wM} (moduleFinitePointSource X D n) (moduleRootsOfUnity X n) q) :
    modulePointExtToCohomology (inclusion X D) n q e =
      ∑ x : D, modulePointExtToCohomology (X.fromSpecResidueField x.val) n q
        (moduleFinitePointExtAddEquiv X D n hclosed (moduleRootsOfUnity X n) q e x) := by
  have H := (moduleFinitePointExtAddEquiv X D n hclosed
    (moduleRootsOfUnity X n) q).symm_apply_apply e
  rw [moduleFinitePointExtAddEquiv_symm_apply] at H
  calc
    _ = modulePointExtToCohomology (inclusion X D) n q
        (∑ x : D, (Ext.mk₀ (moduleFinitePointProjection X D n x)).comp
          (moduleFinitePointExtAddEquiv X D n hclosed (moduleRootsOfUnity X n) q e x)
          (zero_add q)) := congrArg _ H.symm
    _ = _ := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro x _
      exact moduleFinitePointProjection_extToCohomology X D n q x _

/-- The SUM law as an equality of the original whole additive operators. -/
theorem moduleFinitePointExtToCohomology_eq_sum (q : ℕ) :
    modulePointExtToCohomology (inclusion X D) n q =
      ∑ x : D, (modulePointExtToCohomology (X.fromSpecResidueField x.val) n q).comp
        ((Pi.evalAddMonoidHom _ x).comp
          (moduleFinitePointExtAddEquiv X D n hclosed
            (moduleRootsOfUnity X n) q).toAddMonoidHom) := by
  ext e
  simpa only [AddMonoidHom.finsetSum_apply, AddMonoidHom.comp_apply,
    Pi.evalAddMonoidHom_apply, AddEquiv.coe_toAddMonoidHom]
    using moduleFinitePointExtToCohomology_sum X D n hclosed q e

end FiniteExt

section ProperFinite

open Curves.FiniteClosedSupport

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.OverField.FScheme k}
  (hC : Scheme.OverField.Curve.Properties C) (D : Set C.left) [Finite D]
  (hclosed : ∀ x ∈ D, IsClosed ({x} : Set C.left))
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
  [HasExt.{wM} (ModuleSheaf C.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wA} (AbelianSheaf.{u, u + 1} C.left)]

/-- The finite index instance shared by the original proper trace sums. -/
local instance properFiniteFintype : Fintype D := Fintype.ofFinite D

/-- Original point purity gives coordinates on the ACTUAL finite supported source.
There is no nonemptiness hypothesis and no new pointwise generator choice. -/
def moduleFinitePointPurityAddEquiv :
    Ext.{wM} (moduleFinitePointSource C.left D n) (moduleRootsOfUnity C.left n) 2 ≃+
      (D → ZMod n) := by
  let : ∀ x : D, IsClosedImmersion (C.left.fromSpecResidueField x.val) := fun x =>
    isClosed_singleton_iff_isClosedImmersion.mp (hclosed x.val x.property)
  exact (moduleFinitePointExtAddEquiv C.left D n hclosed (moduleRootsOfUnity C.left n) 2).trans
    (AddEquiv.piCongrRight fun x : D => modulePointPurityAddEquiv hC
      ⟨x.val, hclosed x.val x.property⟩ (C.left.fromSpecResidueField x.val)
      (C.left.range_fromSpecResidueField x.val) n hn hunit
      (modulePoint_globalLevelInvertible n hunit))

/-- Proper trace of the ORIGINAL finite support-forgetting map is SUM of coordinates. -/
theorem moduleFinitePointPurityAddEquiv_trace
    (e : Ext.{wM} (moduleFinitePointSource C.left D n) (moduleRootsOfUnity C.left n) 2) :
    Curves.traceAddEquiv hC n hn hunit (modulePoint_globalLevelInvertible n hunit)
        (modulePointExtToCohomology (inclusion C.left D) n 2 e) =
      ∑ x : D, moduleFinitePointPurityAddEquiv hC D hclosed n hn hunit e x := by
  rw [moduleFinitePointExtToCohomology_sum C.left D n hclosed, map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rfl

/-- Reindexing the same finite coordinates preserves the original trace sum. -/
theorem moduleFinitePointPurityAddEquiv_trace_reindex
    {ι : Type*} [Fintype ι] (r : ι ≃ D)
    (e : Ext.{wM} (moduleFinitePointSource C.left D n) (moduleRootsOfUnity C.left n) 2) :
    Curves.traceAddEquiv hC n hn hunit (modulePoint_globalLevelInvertible n hunit)
        (modulePointExtToCohomology (inclusion C.left D) n 2 e) =
      ∑ x : ι, moduleFinitePointPurityAddEquiv hC D hclosed n hn hunit e (r x) := by
  rw [moduleFinitePointPurityAddEquiv_trace]
  exact (r.sum_comp _).symm

include hC hclosed hn hunit in
/-- Finite supported Ext vanishes in every degree other than two. The same
original Ext world is used throughout, and empty support is allowed. -/
theorem moduleFinitePointExt_subsingleton (q : ℕ) (hq : q ≠ 2) :
    Subsingleton (Ext.{wM} (moduleFinitePointSource C.left D n)
      (moduleRootsOfUnity C.left n) q) := by
  let : ∀ x : D, IsClosedImmersion (C.left.fromSpecResidueField x.val) := fun x =>
    isClosed_singleton_iff_isClosedImmersion.mp (hclosed x.val x.property)
  let : ∀ x : D, Subsingleton (Ext.{wM}
      ((moduleDirectImage (C.left.fromSpecResidueField x.val) (ULift.{u + 1} (ZMod n))).obj
        (moduleUnit (Spec (C.left.residueField x.val)) (ULift.{u + 1} (ZMod n))))
      (moduleRootsOfUnity C.left n) q) := fun x => by
    have hi := C.left.range_fromSpecResidueField x.val
    let z : Scheme.ClosedPoint C.left := ⟨x.val, hclosed x.val x.property⟩
    rcases q with _ | (_ | q)
    · exact modulePointExt_zero_subsingleton hC z _ hi n hn hunit
        (modulePoint_globalLevelInvertible n hunit)
    · exact modulePointExt_one_subsingleton hC z _ hi n hn hunit
        (modulePoint_globalLevelInvertible n hunit)
    · exact modulePointExt_high_subsingleton hC z _ hi n hn hunit
        (modulePoint_globalLevelInvertible n hunit) _ (by omega)
  exact (moduleFinitePointExtAddEquiv C.left D n hclosed
    (moduleRootsOfUnity C.left n) q).injective.subsingleton

end ProperFinite

end AlgebraicGeometry.Scheme.EtaleCohomology
