/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.LocallyConstant
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.GenericDetection.Represented

/-! # Dominant pullback detects finite locally constant coefficients

Over an integral scheme, the original pullback along any dominant morphism
detects maps into a finite locally constant abelian sheaf. The represented
proof uses reduced etale tests and the actual dominant pullback projection.
The resulting monomorphism is the original inverse-image adjunction unit.
No normality, Noetherianity, flatness or field identification is required.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators

universe u

attribute [local instance] hasSheafifyLarge

/-- A morphism whose original image contains the generic point of an integral
scheme is dominant. -/
theorem isDominant_of_genericPoint_mem_range {X Y : Scheme.{u}} [IsIntegral X]
    (f : Y ⟶ X) (hf : genericPoint X ∈ Set.range f) : IsDominant f := by
  constructor
  rw [denseRange_iff_closure_range, ← Set.univ_subset_iff]
  rw [← (genericPoint_spec X).def]
  exact closure_mono (Set.singleton_subset_iff.mpr hf)

/-- Original pullback along a dominant morphism detects separated-target
scheme morphisms from every etale test over an integral base. -/
theorem dominantPullbackHom_injective {X Y : Scheme.{u}} [IsIntegral X]
    (f : Y ⟶ X) [IsDominant f] (U Z : Over X)
    [Etale U.hom] [IsSeparated Z.hom] :
    Function.Injective (fun h : U ⟶ Z => (Over.pullback f).map h) := by
  have : GeometricallyReduced U.hom := Etale.geometricallyReduced U.hom
  have : Finite (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  have : IsReduced U.left :=
    GeometricallyReduced.isReduced_of_flat_of_finite_irreducibleComponents U.hom
  have : IsDominant (pullback.fst U.hom f) := by
    constructor
    change Dense (Set.range (pullback.fst U.hom f))
    rw [Scheme.Pullback.range_fst]
    exact f.denseRange.preimage U.hom.isOpenMap
  intro a b hab
  apply Over.OverMorphism.ext
  apply ext_of_isDominant_of_isSeparated Z.hom
    ((Over.w a).trans (Over.w b).symm) (pullback.fst U.hom f)
  have h := congrArg (fun k => k.left ≫ pullback.fst Z.hom f) hab
  simpa only [Over.pullback_map_left, pullback.lift_fst] using h

/-- The actual represented-section map along a dominant morphism is monic
for every separated represented abelian coefficient over an integral base. -/
theorem mono_representedSectionPullback_of_isDominant
    {X Y : Scheme.{u}} [IsIntegral X] (f : Y ⟶ X) [IsDominant f]
    (H : Grp (Over X)) [IsCommMonObj H.X] [IsSeparated H.X.hom] :
    Mono (representedSectionPullback f H) := by
  apply (sheafToPresheaf (Scheme.smallEtaleTopology X)
    AddCommGrpCat.{u + 1}).mono_of_mono_map
  change Mono (representedBaseChangeUnit f H)
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro U
  apply (AddCommGrpCat.mono_iff_injective _).mpr
  have : Etale ((Scheme.Etale.forget X).obj U.unop).hom := U.unop.prop
  intro a b hab
  apply ULift.ext
  apply Additive.toMul.injective
  apply dominantPullbackHom_injective f ((Scheme.Etale.forget X).obj U.unop) H.X
  exact congrArg (fun t => t.down.toMul) hab

private theorem mono_unit_of_mono_target
    {C D : Type*} [Category* C] [Category* D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) {F : C} {M : D} (a : F ⟶ R.obj M) [Mono a] :
    Mono (adj.unit.app F) := by
  have h : adj.unit.app F ≫ R.map ((adj.homEquiv F M).symm a) = a :=
    (adj.homEquiv F M).apply_symm_apply a
  exact mono_of_mono_fac h

/-- The literal dominant adjunction unit is monic for every finite locally
constant abelian sheaf over an integral scheme. -/
theorem mono_unit_of_finiteLocallyConstant_of_isDominant
    {X Y : Scheme.{u}} [IsIntegral X] (f : Y ⟶ X) [IsDominant f]
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsFiniteLocallyConstant F) :
    Mono ((inverseImageAdjunction f).unit.app F) := by
  let r := CoefficientRepresentation.ofFiniteLocallyConstant F (stacks03RV X) hF
  have : IsFinite r.group.X.hom := r.finite
  have : IsCommMonObj r.group.X := r.commutative
  have : Mono (representedSectionPullback f r.group) :=
    mono_representedSectionPullback_of_isDominant f r.group
  exact mono_unit_of_mono_target (inverseImageAdjunction f)
    (r.iso.inv ≫ representedSectionPullback f r.group)

/-- Original dominant inverse image detects equality of maps into the given
finite locally constant coefficient, without a residue-field comparison. -/
theorem inverseImage_map_injective_of_finiteLocallyConstant_of_isDominant
    {X Y : Scheme.{u}} [IsIntegral X] (f : Y ⟶ X) [IsDominant f]
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsFiniteLocallyConstant F)
    (G : AbelianSheaf.{u, u + 1} X) :
    Function.Injective (fun a : G ⟶ F => (inverseImage f).map a) := by
  have : Mono ((inverseImageAdjunction f).unit.app F) :=
    mono_unit_of_finiteLocallyConstant_of_isDominant f F hF
  intro a b hab
  apply (cancel_mono ((inverseImageAdjunction f).unit.app F)).mp
  calc
    a ≫ (inverseImageAdjunction f).unit.app F =
        (inverseImageAdjunction f).unit.app G ≫
          (directImage f).map ((inverseImage f).map a) :=
      (inverseImageAdjunction f).unit.naturality a
    _ = (inverseImageAdjunction f).unit.app G ≫
        (directImage f).map ((inverseImage f).map b) :=
      congrArg (fun k => (inverseImageAdjunction f).unit.app G ≫ (directImage f).map k) hab
    _ = b ≫ (inverseImageAdjunction f).unit.app F :=
      ((inverseImageAdjunction f).unit.naturality b).symm

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators
