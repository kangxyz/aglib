/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Noetherian.GenericImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Closure
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Basic.PullbackQcqs
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Basic.GenericLocallyConstant
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteStratification.GenericProperty
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.DominantDetection
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.FieldConservative
public import Aglib.CategoryTheory.Abelian.SubobjectComparison
public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic

/-! # Strong Serre closure on a Noetherian scheme

An actual constructible stage captures the finite generic stalk of an
arbitrary subsheaf. Its coimage inside the known constructible target is
constructible by weak closure. The quotient target is locally constant on
a genuine generic open, where its original dominant unit detects equality.
Thus the subsheaf agrees there with that same coimage. Noetherian induction
then produces an actual finite partition of the original subsheaf.

This is the finite abelian case of Stacks, Tag 09BH. No claim about arbitrary
qcqs bases or modules over non-Noetherian coefficient rings is made.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible

universe u

attribute [local instance] hasSheafifyLarge

/-- An arbitrary subsheaf of a constructible coefficient on an integral
Noetherian affine scheme is finite locally constant on a genuine nonempty
open. The constructible approximation is produced, not assumed. -/
theorem exists_nonempty_finiteLocallyConstant_open_of_mono
    {X : Scheme.{u}} [IsNoetherian X] [IsAffine X] [IsIntegral X]
    {F G : AbelianSheaf.{u, u + 1} X} (f : F ⟶ G) [Mono f]
    (hG : IsConstructible G) :
    ∃ (S : Scheme.{u}) (j : S ⟶ X), IsOpenImmersion j ∧ Nonempty S ∧
      IsFiniteLocallyConstant ((inverseImage j).obj F) := by
  let Ω := FibrewiseClosed.pointField (genericPoint X)
  let η : Spec (.of Ω) ⟶ X := FibrewiseClosed.geometricPoint (genericPoint X)
  have hηpoint : η default = genericPoint X :=
    FibrewiseClosed.geometricPoint_apply _ _
  have : IsDominant η := FiniteCogenerators.isDominant_of_genericPoint_mem_range η
    ⟨default, hηpoint⟩
  obtain ⟨P, q, hP, hq⟩ := exists_constructible_geometricStalk_epi_of_mono f hG η
  let H := Abelian.coimage (q ≫ f)
  let a : H ⟶ F := Abelian.coimageSubobjectComparison q f
  have : Mono a := inferInstanceAs (Mono (Abelian.coimageSubobjectComparison q f))
  have hH : IsConstructible H :=
    isConstructible_cokernel (kernel.ι (q ≫ f))
      (isConstructible_kernel (q ≫ f) hP hG) hP
  let T := (pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})
  let : LocallySmall.{u} X.Etale := inferInstance
  let : HasFilteredColimitsOfSize.{u, u} AddCommGrpCat.{u + 1} :=
    hasFilteredColimitsOfSize_of_univLE.{u, u, u + 1, u + 1}
  let : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} :=
    AB5OfSize_of_univLE.{u, u, u + 1, u + 1} _
  let : PreservesFiniteLimits T := inferInstanceAs
    (PreservesFiniteLimits ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})))
  let : T.PreservesMonomorphisms := inferInstance
  have : Epi (T.map q) := hq
  have hTa : IsIso (T.map a) := Abelian.isIso_map_coimageSubobjectComparison q f T
  have hηa : IsIso ((inverseImage η).map a) := by
    have hcomp : IsIso ((pointSmallEtale (𝟙 (Spec (.of Ω)) ≫ η)).sheafFiber.map a) := by
      rw [Category.id_comp]
      exact hTa
    have : IsIso ((pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber.map
        ((inverseImage η).map a)) :=
      (NatIso.isIso_map_iff (StalkInverseImage.stalkUnitNatIso η (𝟙 _)) a).mp hcomp
    exact isIso_of_field_geometricStalk Ω (𝟙 _) ((inverseImage η).map a)
  let b := a ≫ f
  let Q := cokernel b
  have hQ : IsConstructible Q := isConstructible_cokernel b hH hG
  let δ : F ⟶ Q := f ≫ cokernel.π b
  have hηδ : (inverseImage η).map δ = 0 := by
    apply (cancel_epi ((inverseImage η).map a)).mp
    rw [← Functor.map_comp]
    change (inverseImage η).map (a ≫ f ≫ cokernel.π b) = _
    rw [← Category.assoc, cokernel.condition, Functor.map_zero, comp_zero]
  obtain ⟨S, j, hj, hS, hQloc⟩ := exists_nonempty_finiteLocallyConstant_open hQ
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
  let L := inverseImage j
  have hζδ : (inverseImage ζ).map (L.map δ) = 0 := by
    have hz : (inverseImage (ζ ≫ j)).map δ = 0 := by rw [hζ]; exact hηδ
    apply (cancel_epi ((inverseImageComp j ζ).hom.app F)).mp
    change (inverseImageComp j ζ).hom.app F ≫
      (inverseImage j ⋙ inverseImage ζ).map δ = _
    rw [← (inverseImageComp j ζ).hom.naturality, hz, zero_comp, comp_zero]
  have hδ : L.map δ = 0 :=
    (FiniteCogenerators.inverseImage_map_injective_of_finiteLocallyConstant_of_isDominant
      ζ (L.obj Q) hQloc (L.obj F)) (by simpa only [Functor.map_zero] using hζδ)
  have hzero : L.map f ≫ cokernel.π (L.map a ≫ L.map f) = 0 := by
    rw [← L.map_comp]
    change L.map f ≫ cokernel.π (L.map b) = 0
    rw [← PreservesCokernel.π_iso_hom L b, ← Category.assoc, ← L.map_comp]
    change L.map δ ≫ _ = 0
    rw [hδ, zero_comp]
  have : IsIso (L.map a) := Abelian.isIso_of_comp_cokernel_zero (L.map a) (L.map f) hzero
  have hHpull : IsConstructible (L.obj H) := isConstructible_pullback_of_qcqs j hH
  obtain ⟨tH⟩ := nonempty_constructiblePartition_of_qcqs hHpull
  obtain ⟨W, k, hk, hW, hHloc⟩ := exists_nonempty_finiteLocallyConstant_open_of_partition tH
  have : IsOpenImmersion k := hk
  refine ⟨W, k ≫ j, inferInstance, hW, ?_⟩
  apply (isFiniteLocallyConstant_iff_of_iso ((inverseImageComp j k).app F)).mpr
  exact (isFiniteLocallyConstant_iff_of_iso
    ((inverseImage k).mapIso (asIso (L.map a)))).mp hHloc

/-- Every original subobject of a constructible finite abelian sheaf on a
Noetherian scheme is constructible. -/
theorem isConstructible_of_mono_of_noetherian
    {X : Scheme.{u}} [IsNoetherian X]
    {F G : AbelianSheaf.{u, u + 1} X} (f : F ⟶ G) [Mono f]
    (hG : IsConstructible G) : IsConstructible F := by
  obtain ⟨p, hp⟩ := exists_finitePartition_of_generic_open
    (fun {Y} i => IsFiniteLocallyConstant ((inverseImage i).obj F)) (by
      intro Y _ _ _ i _
      obtain ⟨S, j, hj, hS, hloc⟩ := exists_nonempty_finiteLocallyConstant_open_of_mono
        ((inverseImage i).map f) (isConstructible_pullback_of_qcqs i hG)
      exact ⟨S, j, hj, hS,
        (isFiniteLocallyConstant_iff_of_iso ((inverseImageComp i j).app F)).mpr hloc⟩)
  exact isConstructible_of_partition { toFiniteLocallyClosedPartition := p, locally_constant := hp }

/-- Every original quotient of a constructible finite abelian sheaf on a
Noetherian scheme is constructible. -/
theorem isConstructible_of_epi_of_noetherian
    {X : Scheme.{u}} [IsNoetherian X]
    {F G : AbelianSheaf.{u, u + 1} X} (f : F ⟶ G) [Epi f]
    (hF : IsConstructible F) : IsConstructible G := by
  have hK := isConstructible_of_mono_of_noetherian (kernel.ι f) hF
  have hC := isConstructible_cokernel (kernel.ι f) hK hF
  exact (isConstructible_iff_of_iso (asIso (Abelian.factorThruCoimage f))).mp hC

/-- Native strong subobject closure, with the Noetherian base hypothesis. -/
instance isConstructible_closedUnderSubobjects_of_noetherian
    (X : Scheme.{u}) [IsNoetherian X] :
    ObjectProperty.IsClosedUnderSubobjects (IsConstructible (X := X)) where
  prop_of_mono f _ h := isConstructible_of_mono_of_noetherian f h

/-- Native strong quotient closure, with the Noetherian base hypothesis. -/
instance isConstructible_closedUnderQuotients_of_noetherian
    (X : Scheme.{u}) [IsNoetherian X] :
    ObjectProperty.IsClosedUnderQuotients (IsConstructible (X := X)) where
  prop_of_epi f _ h := isConstructible_of_epi_of_noetherian f h

/-- Original finite abelian constructibility is a strong Serre class on a
Noetherian scheme, combining the proved strong closure with weak extensions. -/
instance isConstructible_isSerreClass_of_noetherian
    (X : Scheme.{u}) [IsNoetherian X] :
    ObjectProperty.IsSerreClass (IsConstructible (X := X)) where
  toContainsZero := inferInstance
  toIsClosedUnderSubobjects := inferInstance
  toIsClosedUnderQuotients := inferInstance
  toIsClosedUnderExtensions := inferInstance

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible
