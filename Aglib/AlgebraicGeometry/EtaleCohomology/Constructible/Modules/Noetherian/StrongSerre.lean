/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.Noetherian.GenericImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.Noetherian.DominantDetection
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.GenericLocalConstancy
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ClosureConstructible
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.Pullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteStratification.GenericProperty
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.DominantDetection
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.ModuleFieldConservative
public import Aglib.CategoryTheory.Abelian.SubobjectComparison
public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic

/-! # Strong Serre closure of native constructible modules

The original generic stalk is captured by a native constructible stage.
Weak closure supplies its coimage; dominant detection into a locally constant
quotient identifies that coimage with the original subsheaf on a generic open.
Finite partition induction proves strong closure on Noetherian schemes over
a left Noetherian ring, without commutativity or finite additive carriers.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u

variable (R : Type (u + 1)) [Ring R] [IsNoetherianRing R]

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

local instance strongSerreHasFiniteLimits : HasFiniteLimits (ModuleCat.{u + 1} R) where
  out _ _ _ := ModuleCat.hasLimitsOfShape.{0, 0, u + 1, u + 1}

local instance strongSerreHasLimits : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} R) :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}

/-- An arbitrary subsheaf of a constructible coefficient on an integral
Noetherian affine scheme is finite locally constant on a genuine nonempty
open. The constructible approximation is produced, not assumed. -/
theorem exists_nonempty_finiteTypeLocallyConstant_open_of_mono
    {X : Scheme.{u}} [IsNoetherian X] [IsAffine X] [IsIntegral X]
    {F G : ModuleSheaf R X} (f : F ⟶ G) [Mono f]
    (hG : IsConstructible G) :
    ∃ (S : Scheme.{u}) (j : S ⟶ X), IsOpenImmersion j ∧ Nonempty S ∧
      IsFiniteTypeLocallyConstant ((moduleInverseImage R j).obj F) := by
  let Ω := FibrewiseClosed.pointField (genericPoint X)
  let η : Spec (.of Ω) ⟶ X := FibrewiseClosed.geometricPoint (genericPoint X)
  have hηpoint : η default = genericPoint X :=
    FibrewiseClosed.geometricPoint_apply _ _
  have : IsDominant η := FiniteCogenerators.isDominant_of_genericPoint_mem_range η
    ⟨default, hηpoint⟩
  obtain ⟨P, q, hP, hq⟩ := exists_constructible_geometricStalk_epi_of_mono R f hG η
  let H := Abelian.coimage (q ≫ f)
  let a : H ⟶ F := Abelian.coimageSubobjectComparison q f
  have : Mono a := inferInstanceAs (Mono (Abelian.coimageSubobjectComparison q f))
  have hH : IsConstructible H :=
    isConstructible_cokernel (kernel.ι (q ≫ f))
      (isConstructible_kernel (q ≫ f) hP hG) hP
  let T := (pointSmallEtale η).sheafFiber (A := (ModuleCat.{u + 1} R))
  let : LocallySmall.{u} X.Etale := inferInstance
  let : HasFilteredColimitsOfSize.{u, u} (ModuleCat.{u + 1} R) :=
    hasFilteredColimitsOfSize_of_univLE.{u, u, u + 1, u + 1}
  let : AB5OfSize.{u, u} (ModuleCat.{u + 1} R) :=
    AB5OfSize_of_univLE.{u, u, u + 1, u + 1} _
  let : PreservesFiniteLimits T := inferInstanceAs
    (PreservesFiniteLimits ((pointSmallEtale η).sheafFiber (A := (ModuleCat.{u + 1} R))))
  let : T.PreservesMonomorphisms := inferInstance
  have : Epi (T.map q) := hq
  have hTa : IsIso (T.map a) := Abelian.isIso_map_coimageSubobjectComparison q f T
  have hηa : IsIso ((moduleInverseImage R η).map a) := by
    have hcomp : IsIso (((pointSmallEtale (𝟙 (Spec (.of Ω)) ≫ η)).sheafFiber
        (A := ModuleCat.{u + 1} R)).map a) := by
      rw [Category.id_comp]
      exact hTa
    have : IsIso (((pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber
        (A := ModuleCat.{u + 1} R)).map
        ((moduleInverseImage R η).map a)) :=
      (NatIso.isIso_map_iff (geometricModuleStalkInverseImageIso η (𝟙 _) R) a).mp hcomp
    exact isIso_of_field_moduleGeometricStalk R Ω (𝟙 _) ((moduleInverseImage R η).map a)
  let b := a ≫ f
  let Q := cokernel b
  have hQ : IsConstructible Q := isConstructible_cokernel b hH hG
  let δ : F ⟶ Q := f ≫ cokernel.π b
  have hηδ : (moduleInverseImage R η).map δ = 0 := by
    apply (cancel_epi ((moduleInverseImage R η).map a)).mp
    rw [← Functor.map_comp]
    change (moduleInverseImage R η).map (a ≫ f ≫ cokernel.π b) = _
    rw [← Category.assoc, cokernel.condition, Functor.map_zero, comp_zero]
  obtain ⟨S, j, hSaff, hj, _, hSint, hQloc⟩ :=
    exists_dense_affine_open_isFiniteTypeLocallyConstant Q hQ
  have : IsAffine S := hSaff
  have : IsIntegral S := hSint
  have hS : Nonempty S := inferInstance
  have : IsOpenImmersion j := hj
  have : Nonempty S := hS
  have : IsIntegral S := isIntegral_of_isOpenImmersion j
  have : NoetherianSpace S := j.isOpenEmbedding.isInducing.noetherianSpace
  have : IsLocallyNoetherian S := isLocallyNoetherian_of_isOpenImmersion j
  have : IsNoetherian S := ⟨⟩
  have hηrange : η default ∈ Set.range j := by
    rw [hηpoint]
    apply ((genericPoint_spec X).mem_open_set_iff j.isOpenEmbedding.isOpen_range).mpr
    obtain ⟨s⟩ := hS
    exact ⟨j s, Set.mem_univ _, ⟨s, rfl⟩⟩
  obtain ⟨ζ, hζ⟩ := exists_fieldPoint_lift_of_mem_range j η hηrange
  have : IsDominant (ζ ≫ j) := by rw [hζ]; infer_instance
  have : IsDominant ζ := IsDominant.of_comp_of_isOpenImmersion ζ j
  let L := moduleInverseImage R j
  let : L.IsLeftAdjoint := (moduleImageAdjunction R j).isLeftAdjoint
  have hζδ : (moduleInverseImage R ζ).map (L.map δ) = 0 := by
    have hz : (moduleInverseImage R (ζ ≫ j)).map δ = 0 := by rw [hζ]; exact hηδ
    apply (cancel_epi ((moduleInverseImageComp R j ζ).hom.app F)).mp
    change (moduleInverseImageComp R j ζ).hom.app F ≫
      (moduleInverseImage R j ⋙ moduleInverseImage R ζ).map δ = _
    rw [← (moduleInverseImageComp R j ζ).hom.naturality, hz, zero_comp, comp_zero]
  have hδ : L.map δ = 0 :=
    (inverseImage_map_injective_of_isFiniteTypeLocallyConstant_of_isDominant
      R ζ (L.obj Q) hQloc (L.obj F)) (by simpa only [Functor.map_zero] using hζδ)
  have hzero : L.map f ≫ cokernel.π (L.map a ≫ L.map f) = 0 := by
    rw [← L.map_comp]
    change L.map f ≫ cokernel.π (L.map b) = 0
    rw [← PreservesCokernel.π_iso_hom L b, ← Category.assoc, ← L.map_comp]
    change L.map δ ≫ _ = 0
    rw [hδ, zero_comp]
  have : IsIso (L.map a) := Abelian.isIso_of_comp_cokernel_zero (L.map a) (L.map f) hzero
  have hHpull : IsConstructible (L.obj H) := isConstructible_pullback j hH
  obtain ⟨W, k, _, hk, _, hWint, hHloc⟩ :=
    exists_dense_affine_open_isFiniteTypeLocallyConstant (L.obj H) hHpull
  have : IsIntegral W := hWint
  have hW : Nonempty W := inferInstance
  have : IsOpenImmersion k := hk
  refine ⟨W, k ≫ j, inferInstance, hW, ?_⟩
  apply (isFiniteTypeLocallyConstant_iff_of_iso ((moduleInverseImageComp R j k).app F)).mpr
  exact (isFiniteTypeLocallyConstant_iff_of_iso
    ((moduleInverseImage R k).mapIso (asIso (L.map a)))).mp hHloc

/-- Every original subobject of a constructible finite-type module sheaf on a
Noetherian scheme is constructible. -/
theorem isConstructible_of_mono_of_noetherian
    {X : Scheme.{u}} [IsNoetherian X]
    {F G : ModuleSheaf R X} (f : F ⟶ G) [Mono f]
    (hG : IsConstructible G) : IsConstructible F := by
  obtain ⟨p, hp⟩ := exists_finitePartition_of_generic_open
    (fun {Y} i => IsFiniteTypeLocallyConstant ((moduleInverseImage R i).obj F)) (by
      intro Y _ _ _ i _
      obtain ⟨S, j, hj, hS, hloc⟩ := exists_nonempty_finiteTypeLocallyConstant_open_of_mono R
        ((moduleInverseImage R i).map f) (isConstructible_pullback i hG)
      exact ⟨S, j, hj, hS,
        (isFiniteTypeLocallyConstant_iff_of_iso ((moduleInverseImageComp R i j).app F)).mpr hloc⟩)
  let t : ConstructiblePartition F :=
    { toFiniteLocallyClosedPartition := p, locally_constant := hp }
  intro U
  have : IsAffine U.1.toScheme := U.property
  exact ⟨t.baseChange U.1.ι⟩

/-- Every original quotient of a constructible finite-type module sheaf on a
Noetherian scheme is constructible. -/
theorem isConstructible_of_epi_of_noetherian
    {X : Scheme.{u}} [IsNoetherian X]
    {F G : ModuleSheaf R X} (f : F ⟶ G) [Epi f]
    (hF : IsConstructible F) : IsConstructible G := by
  have hK := isConstructible_of_mono_of_noetherian R (kernel.ι f) hF
  have hC := isConstructible_cokernel (kernel.ι f) hK hF
  exact (isConstructible_iff_of_iso (asIso (Abelian.factorThruCoimage f))).mp hC

/-- Native strong subobject closure, with the Noetherian base hypothesis. -/
instance isConstructible_closedUnderSubobjects_of_noetherian
    (X : Scheme.{u}) [IsNoetherian X] :
    ObjectProperty.IsClosedUnderSubobjects (IsConstructible (R := R) (X := X)) where
  prop_of_mono f _ h := isConstructible_of_mono_of_noetherian R f h

/-- Native strong quotient closure, with the Noetherian base hypothesis. -/
instance isConstructible_closedUnderQuotients_of_noetherian
    (X : Scheme.{u}) [IsNoetherian X] :
    ObjectProperty.IsClosedUnderQuotients (IsConstructible (R := R) (X := X)) where
  prop_of_epi f _ h := isConstructible_of_epi_of_noetherian R f h

/-- Original finite-type module constructibility is a strong Serre class on a
Noetherian scheme, combining the proved strong closure with weak extensions. -/
instance isConstructible_isSerreClass_of_noetherian
    (X : Scheme.{u}) [IsNoetherian X] :
    ObjectProperty.IsSerreClass (IsConstructible (R := R) (X := X)) where
  toContainsZero := inferInstance
  toIsClosedUnderSubobjects := inferInstance
  toIsClosedUnderQuotients := inferInstance
  toIsClosedUnderExtensions := inferInstance

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
