/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.FiniteSetRepresentation
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.CoefficientRepresentation
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.FiniteTrivialization
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GaloisInstances
public import Aglib.CategoryTheory.Adjunction.MonicProducts
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-! # Finite constant cogenerators for finite locally constant coefficients

On a connected scheme, the actual finite-etale Galois-category construction
produces a finite surjective cover trivializing an actual finite locally
constant abelian sheaf. Faithfully flat scheme pullback detects its represented
sections. Consequently the original inverse-image adjunction unit, followed by
the direct image of the constructed trivialization, is a monomorphism into the
pushforward of an actual finite constant sheaf.

No normality, Noetherianity, quasi-compactness or condition on coefficient order
is required. This is the locally constant case; extending coefficients from
locally closed strata is a separate construction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators

universe u

attribute [local instance] hasSheafifyLarge

private theorem mono_unit_of_mono_rightTarget
    {C D : Type*} [Category* C] [Category* D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) {F : C} {M : D} (α : F ⟶ R.obj M) [Mono α] :
    Mono (adj.unit.app F) := by
  exact Adjunction.mono_unit_app_of_mono_rightTarget adj α

/-- The original represented-section map, regarded as a map of actual sheaves.
Its component sends an original scheme section to its scheme-theoretic pullback. -/
def representedSectionPullback {X Y : Scheme.{u}} (f : Y ⟶ X)
    (H : Grp (Over X)) [IsCommMonObj H.X] :
    representedSheaf H ⟶ (directImage f).obj (representedSheaf (baseChangedGroup f H)) :=
  ObjectProperty.homMk (representedBaseChangeUnit f H)

/-- The underlying presheaf map is literally the original scheme pullback map. -/
theorem representedSectionPullback_hom {X Y : Scheme.{u}} (f : Y ⟶ X)
    (H : Grp (Over X)) [IsCommMonObj H.X] :
    (representedSectionPullback f H).hom = representedBaseChangeUnit f H := rfl

/-- Faithfully flat scheme pullback detects all original represented sections. -/
theorem mono_representedSectionPullback {X Y : Scheme.{u}} (f : Y ⟶ X)
    [Flat f] [Surjective f] (H : Grp (Over X)) [IsCommMonObj H.X] :
    Mono (representedSectionPullback f H) := by
  have (Z : Scheme.{u}) (g : Z ⟶ X) : Epi (pullback.fst g f) :=
    Flat.epi_of_flat_of_surjective _
  have : (Over.pullback f).Faithful := inferInstance
  apply (sheafToPresheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).mono_of_mono_map
  change Mono (representedBaseChangeUnit f H)
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro U
  apply (AddCommGrpCat.mono_iff_injective _).mpr
  intro a b hab
  apply ULift.ext
  apply Additive.toMul.injective
  apply (Over.pullback f).map_injective
  exact congrArg (fun t => t.down.toMul) hab

/-- The literal adjunction unit is monic on every finite locally constant sheaf
under any faithfully flat scheme morphism. -/
theorem mono_unit_of_finiteLocallyConstant {X Y : Scheme.{u}} (f : Y ⟶ X)
    [Flat f] [Surjective f] (F : AbelianSheaf.{u, u + 1} X)
    (hF : IsFiniteLocallyConstant F) : Mono ((inverseImageAdjunction f).unit.app F) := by
  let r := CoefficientRepresentation.ofFiniteLocallyConstant F (stacks03RV X) hF
  have : IsCommMonObj r.group.X := r.commutative
  have : Mono (representedSectionPullback f r.group) :=
    mono_representedSectionPullback f r.group
  exact mono_unit_of_mono_rightTarget (inverseImageAdjunction f)
    (r.iso.inv ≫ representedSectionPullback f r.group)

/-- Actual finite-etale trivialization data, constructed below from finite local
constancy on a connected scheme. -/
structure FiniteEtaleTrivialization {X : Scheme.{u}} (F : AbelianSheaf.{u, u + 1} X) where
  /-- The actual finite etale cover of the original scheme. -/
  cover : Scheme.FiniteEtale X
  /-- The original structure morphism is surjective. -/
  surjective : Surjective cover.obj.hom
  /-- The value in the native abelian-sheaf universe. -/
  value : AddCommGrpCat.{u + 1}
  /-- The constant value is a finite abelian group. -/
  finite_value : Finite value
  /-- The original inverse image is isomorphic to the actual constant sheaf. -/
  iso : (inverseImage cover.obj.hom).obj F ≅
    (constantSheaf (Scheme.smallEtaleTopology cover.obj.left) AddCommGrpCat.{u + 1}).obj value

/-- Finite local constancy produces an actual finite-etale surjective
trivializing cover, using the native geometric fibre and Galois dictionaries. -/
def finiteEtaleTrivialization {X : Scheme.{u}} [ConnectedSpace X]
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsFiniteLocallyConstant F) :
    FiniteEtaleTrivialization F := by
  let x : X := Classical.choice (inferInstance : Nonempty X)
  let s := Scheme.FiniteEtale.algebraicClosureResiduePoint X x
  let r := CoefficientRepresentation.ofFiniteLocallyConstant F (stacks03RV X) hF
  have : IsFinite r.group.X.hom := r.finite
  have : Etale r.group.X.hom := r.etale
  have : IsCommMonObj r.group.X := r.commutative
  let t := finiteSplittingCover s r.group
  exact {
    cover := t.cover
    surjective := ⟨t.surjective⟩
    value := t.localValue
    finite_value := t.finite_localValue
    iso := (inverseImage t.cover.obj.hom).mapIso r.iso.symm ≪≫ t.localTrivializationIso }

namespace FiniteEtaleTrivialization

variable {X : Scheme.{u}} {F : AbelianSheaf.{u, u + 1} X}

/-- The actual embedding candidate is the original adjunction unit followed by
the direct image of the constructed finite constant trivialization. -/
def embedding (t : FiniteEtaleTrivialization F) :
    F ⟶ (directImage t.cover.obj.hom).obj
      ((constantSheaf (Scheme.smallEtaleTopology t.cover.obj.left)
        AddCommGrpCat.{u + 1}).obj t.value) :=
  (inverseImageAdjunction t.cover.obj.hom).unit.app F ≫
    (directImage t.cover.obj.hom).map t.iso.hom

/-- The embedding uses the literal original adjunction map and trivialization. -/
theorem embedding_eq (t : FiniteEtaleTrivialization F) :
    t.embedding = (inverseImageAdjunction t.cover.obj.hom).unit.app F ≫
      (directImage t.cover.obj.hom).map t.iso.hom := rfl

/-- The constructed map to the finite constant pushforward is a monomorphism. -/
theorem mono_embedding (t : FiniteEtaleTrivialization F)
    (hF : IsFiniteLocallyConstant F) : Mono t.embedding := by
  have : Etale t.cover.obj.hom := t.cover.property.2
  have : Surjective t.cover.obj.hom := t.surjective
  have : Mono ((inverseImageAdjunction t.cover.obj.hom).unit.app F) :=
    mono_unit_of_finiteLocallyConstant t.cover.obj.hom F hF
  change Mono (_ ≫ _)
  infer_instance

end FiniteEtaleTrivialization

/-- A finite locally constant abelian sheaf on any connected scheme embeds
monomorphically into a finite pushforward of an actual finite constant sheaf.
The finite cover and coefficient are produced, not assumed. -/
theorem exists_finite_constant_embedding {X : Scheme.{u}} [ConnectedSpace X]
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsFiniteLocallyConstant F) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X) (A : AddCommGrpCat.{u + 1}),
      IsFinite f ∧ Etale f ∧ Surjective f ∧ Finite A ∧
      ∃ α : F ⟶ (directImage f).obj
        ((constantSheaf (Scheme.smallEtaleTopology Y) AddCommGrpCat.{u + 1}).obj A), Mono α := by
  let t := finiteEtaleTrivialization F hF
  exact ⟨t.cover.obj.left, t.cover.obj.hom, t.value, t.cover.property.1,
    t.cover.property.2, t.surjective, t.finite_value, t.embedding, t.mono_embedding hF⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators
