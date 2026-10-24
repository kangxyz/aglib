/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Proper.MaximalModel
public import Aglib.AlgebraicGeometry.Cohomology.Proper.DerivedStructure
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Proper.Coherent
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Restriction
public import Aglib.AlgebraicGeometry.Cohomology.Affine.PushforwardAcyclicity
public import Aglib.AlgebraicGeometry.Cohomology.Support.Finite
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.QuasiCoherent
public import Aglib.AlgebraicGeometry.Surfaces.Birational.IsomorphismLocus
public import Aglib.AlgebraicGeometry.Dimension.OpenCover
public import Aglib.AlgebraicGeometry.Blowup.AffineLiftingCover
public import Aglib.RingTheory.Nagata.FiniteTypeSurface

/-!
# Vanishing of the original first higher image above a maximal model

For a complete normal local surface with a uniform original H1 bound,
the actual maximal model has vanishing original R1 for every further normal
proper birational modification. Actual affine chart maps and GF2 derive the
source dimension bound. Complete-base cohomology then supplies H2 vanishing.

The native original-unit Leray sequence identifies its first map with the
original structural H1 map. Its surjectivity kills the actual global R1
sections. The actual finite closed isomorphism complement, original open
higher-image comparison, affine acyclicity and stalk detection kill R1 itself.
No local replacement, rationality or resolution conclusion is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Blowup
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

section OriginalCharts

variable {A : CommRingCat.{u}} {W : Scheme.{u}} (f : W ⟶ Spec A)

local instance [IsDomain A] : Nonempty (⊤ : (Spec A).Opens) :=
  ⟨⟨genericPoint (Spec A), trivial⟩⟩

private theorem originalChart_finiteType [LocallyOfFiniteType f]
    (U : W.Opens) (hU : IsAffineOpen U) : (affineBaseMap f U).FiniteType :=
  (f.finiteType_appLE (isAffineOpen_top _) hU le_top).comp
    (RingHom.FiniteType.of_surjective (Scheme.ΓSpecIso A).inv.hom
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).inv).2)

private theorem originalChart_injective [IsDomain A] [IsIntegral W]
    [IsDominant f] [QuasiCompact f] (U : W.Opens) [Nonempty U] :
    Function.Injective (affineBaseMap f U) := by
  let : IsSchemeTheoreticallyDominant f := IsSchemeTheoreticallyDominant.of_isDominant f
  exact (AlgebraicGeometry.map_injective_of_isIntegral W (homOfLE (le_top : U ≤ ⊤))).comp
    ((f.app_injective ⊤).comp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).inv).1)

private theorem originalChart_germ [IsDomain A] [IsIntegral W] [IsDominant f]
    (U : W.Opens) [Nonempty U] :
    CommRingCat.ofHom (affineBaseMap f U) ≫ W.germToFunctionField U =
      (Scheme.ΓSpecIso A).inv ≫ (Spec A).germToFunctionField ⊤ ≫
        CommRingCat.ofHom (Scheme.functionFieldMap f) := by
  let : Nonempty (⊤ : W.Opens) := ⟨⟨genericPoint W, trivial⟩⟩
  have hg : genericPoint W ∈ U :=
    ((genericPoint_spec W).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have hres : W.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫
      W.germToFunctionField U = W.germToFunctionField ⊤ :=
    W.presheaf.germ_res (homOfLE (le_top : U ≤ ⊤)) (genericPoint W) hg
  rw [Scheme.functionFieldMap_germ]
  change (Scheme.ΓSpecIso A).inv ≫ f.appTop ≫
      W.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ W.germToFunctionField U =
    (Scheme.ΓSpecIso A).inv ≫ f.appTop ≫ W.germToFunctionField ⊤
  rw [hres]

private theorem originalChart_germ_apply [IsDomain A] [IsIntegral W] [IsDominant f]
    (U : W.Opens) [Nonempty U] (r : A) :
    W.germToFunctionField U (affineBaseMap f U r) =
      Scheme.functionFieldMap f (algebraMap A (Spec A).functionField r) :=
  congrArg (fun k : A ⟶ W.functionField ↦ k r) (originalChart_germ f U)

private theorem originalChart_isAlgebraic [IsDomain A] [IsIntegral W] [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)))
    (U : W.Opens) [Nonempty U] :
    letI := (affineBaseMap f U).toAlgebra
    Algebra.IsAlgebraic A Γ(W, U) := by
  let := (affineBaseMap f U).toAlgebra
  let := hff
  refine ⟨fun z ↦ ?_⟩
  obtain ⟨q, hq⟩ := (ConcreteCategory.bijective_of_isIso
    (CommRingCat.ofHom (Scheme.functionFieldMap f))).2 (W.germToFunctionField U z)
  obtain ⟨c, d, hd', hcd⟩ := IsFractionRing.div_surjective A q
  have hd0 : d ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hd'
  have hdF : Scheme.functionFieldMap f (algebraMap A (Spec A).functionField d) ≠ 0 := by
    apply (map_ne_zero (Scheme.functionFieldMap f)).mpr
    exact (map_ne_zero_iff _ (IsFractionRing.injective A (Spec A).functionField)).mpr hd0
  have hrat : Scheme.functionFieldMap f (algebraMap A (Spec A).functionField c) /
      Scheme.functionFieldMap f (algebraMap A (Spec A).functionField d) =
        W.germToFunctionField U z := by
    rw [← map_div₀, hcd]
    exact hq
  have hrel : affineBaseMap f U d * z = affineBaseMap f U c := by
    apply W.germToFunctionField_injective U
    rw [map_mul, originalChart_germ_apply, originalChart_germ_apply]
    exact (mul_comm _ _).trans ((div_eq_iff hdF).mp hrat).symm
  refine ⟨Polynomial.C d * Polynomial.X - Polynomial.C c, ?_, ?_⟩
  · intro hp
    apply hd0
    have hc := congrArg (fun p : Polynomial A ↦ p.coeff 1) hp
    simpa using hc
  · change Polynomial.aeval z (Polynomial.C d * Polynomial.X - Polynomial.C c) = 0
    simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
      RingHom.algebraMap_toAlgebra, sub_eq_zero]
    exact hrel

private theorem originalChart_dimension [IsDomain A] [IsIntegral W]
    [IsDominant f] [QuasiCompact f] [LocallyOfFiniteType f]
    (hA : IsNagataRing.{u, 0} A) (hd : ringKrullDim A ≤ 2)
    (hff : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)))
    (U : W.Opens) (hU : IsAffineOpen U) [Nonempty U] : ringKrullDim Γ(W, U) ≤ 2 := by
  let := (affineBaseMap f U).toAlgebra
  let : Algebra.FiniteType A Γ(W, U) := originalChart_finiteType f U hU
  let : Algebra.IsAlgebraic A Γ(W, U) := originalChart_isAlgebraic f hff U
  exact hA.ringKrullDim_le_two_of_finiteType_isAlgebraic hd (originalChart_injective f U)

end OriginalCharts

private theorem actualModel_dimension_of_nagata
    {A : CommRingCat.{u}} [IsDomain A] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec A) [IsProper f] [IsDominant f]
    (hA : IsNagataRing.{u, 0} A) (hd : ringKrullDim A ≤ 2)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f))) :
    topologicalKrullDim X ≤ 2 := by
  let C : X.OpenCover := Scheme.Cover.mkOfCovers X.affineOpens
    (fun U ↦ U.1.toScheme) (fun U ↦ U.1.ι) (by
      intro x
      obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
        (show x ∈ (⊤ : X.Opens) from trivial)
      exact ⟨⟨U, hU⟩, ⟨⟨x, hx⟩, rfl⟩⟩) (fun _ ↦ inferInstance)
  apply Scheme.topologicalKrullDim_le_of_openCover C 2
  intro U
  change topologicalKrullDim U.1 ≤ 2
  by_cases hne : Nonempty U.1
  · let := hne
    calc
      _ = topologicalKrullDim (Spec Γ(X, U.1)) :=
        IsHomeomorph.topologicalKrullDim_eq _ U.2.isoSpec.hom.homeomorph.isHomeomorph
      _ = ringKrullDim Γ(X, U.1) :=
        PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
      _ ≤ 2 := originalChart_dimension f hA hd hff U.1 U.2
  · let : IsEmpty U.1 := ⟨fun x ↦ hne ⟨x⟩⟩
    exact (topologicalKrullDim_zero_of_discreteTopology U.1).trans (by norm_num)

/-- The actual proper birational model has dimension at most two, derived
from the original complete local surface and its actual chart maps. -/
theorem actualModel_dimension_of_complete_surface
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of A))
    [IsProper f] [IsDominant f] (hd : ringKrullDim A = 2)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f))) :
    topologicalKrullDim X ≤ 2 := by
  let : Ring.KrullDimLE 2 A := Ring.krullDimLE_iff.mpr hd.le
  exact actualModel_dimension_of_nagata f
    (IsNagataRing.of_complete_local_dimLE_two A) hd.le hff

/-- H2 of the original structure sheaf vanishes on the actual model.
The actual source dimension is derived, not supplied by the caller. -/
theorem original_model_H2_subsingleton_of_complete_surface
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of A))
    [IsProper f] [IsDominant f] (hd : ringKrullDim A = 2)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f))) :
    Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf X (FiniteTraceCoordinates.structureModule X)) 2) :=
  subsingleton_moduleCohomology_of_complete_surface_modification A f hd
    (actualModel_dimension_of_complete_surface A f hd hff)
    (FiniteTraceCoordinates.structureModule X) (affineLocallyFiniteType_unit X) 2 (by decide)

private theorem higherDirectImage_one_support_subset_compl
    {X Y : Scheme.{u}} (g : Y ⟶ X) (M : Y.Modules) [M.IsQuasicoherent]
    (U : X.Opens) [IsIso (g ∣_ U)] :
    Scheme.Modules.support (((Scheme.Modules.pushforward g).rightDerived 1).obj M) ⊆
      (U : Set X)ᶜ := by
  let N := (Scheme.Modules.restrictFunctor (g ⁻¹ᵁ U).ι).obj M
  let : N.IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor (g ⁻¹ᵁ U).ι M
  have hz : IsZero (((Scheme.Modules.pushforward (g ∣_ U)).rightDerived 1).obj N) :=
    Scheme.Modules.isZero_rightDerived_pushforward_succ (g ∣_ U) N 0
  have hres : IsZero ((Scheme.Modules.restrictFunctor U.ι).obj
      (((Scheme.Modules.pushforward g).rightDerived 1).obj M)) :=
    hz.of_iso ((Scheme.Modules.higherDirectImageRestrictionIso g U 1).app M)
  have haway : Scheme.Modules.supportedAway U.ι
      (((Scheme.Modules.pushforward g).rightDerived 1).obj M) := by
    rw [Scheme.Modules.supportedAway_iff]
    exact hres
  have hd := (Scheme.Modules.supportedAway_iff_support_disjoint U.ι
    (((Scheme.Modules.pushforward g).rightDerived 1).obj M)).mp haway
  intro x hx hxU
  exact Set.disjoint_left.mp hd hx ⟨⟨x, hxU⟩, rfl⟩

/-- The original R1 is coherent and supported on an actual finite set of
closed target points, derived from the original isomorphism locus. -/
theorem original_R1_coherent_finite_closed_support
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsNoetherian X]
    (g : Y ⟶ X) [IsProper g] [IsDominant g]
    (hX : NormalStalks X) (hdX : topologicalKrullDim X ≤ 2)
    (hgf : IsIso (CommRingCat.ofHom (functionFieldMap g))) :
    let R1 := ((Scheme.Modules.pushforward g).rightDerived 1).obj
      (FiniteTraceCoordinates.structureModule Y)
    affineLocallyFiniteType X R1 ∧
      ∃ C : Set X, C.Finite ∧ (∀ x ∈ C, IsClosed ({x} : Set X)) ∧
        Scheme.Modules.support R1 ⊆ C := by
  let M := FiniteTraceCoordinates.structureModule Y
  let : M.IsQuasicoherent := Scheme.Modules.isQuasicoherent_unit Y
  have hcoh := Scheme.Modules.moduleHigherDirectImage_coherent_of_proper g M
    (affineLocallyFiniteType_unit Y) 1
  obtain ⟨U, hU, hfin, hclosed⟩ :=
    Scheme.exists_isIso_restrict_finite_closed_complement_of_isProper_birational
      g hgf hX hdX
  let : IsIso (g ∣_ U) := hU
  refine ⟨hcoh, (U : Set X)ᶜ, hfin, ?_, ?_⟩
  · exact fun x hx ↦ hclosed x hx
  · exact higherDirectImage_one_support_subset_compl g M U

private theorem module_isZero_of_finite_closed_support_of_sections_subsingleton
    {A : Type u} [CommRing A] (X : Scheme.{u}) (α : A →+* Γ(X, ⊤))
    (M : X.Modules) (C : Set X) (hC : C.Finite)
    (hclosed : ∀ x ∈ C, IsClosed ({x} : Set X))
    (hsupp : Scheme.Modules.support M ⊆ C)
    (hΓ : Subsingleton ((moduleGlobalSectionsFunctorOfHom X α).obj M)) :
    IsZero M := by
  classical
  let : Fintype C := hC.fintype
  let e : C ≃ Fin (Fintype.card C) := Fintype.equivFin C
  let p : Fin (Fintype.card C) → X := fun i ↦ (e.symm i : X)
  have hp : Function.Injective p := by
    intro i j hij
    apply e.symm.injective
    exact Subtype.ext hij
  have hpclosed (i : Fin (Fintype.card C)) : IsClosed ({p i} : Set X) :=
    hclosed _ (e.symm i).property
  have hrange : Set.range p = C := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (e.symm i).property
    · intro hx
      refine ⟨e ⟨x, hx⟩, ?_⟩
      simp only [p, Equiv.symm_apply_apply]
  have haway (x : X) (hx : x ∉ Set.range p) :
      IsZero ((additiveStalkFunctor X x).obj (moduleAddSheaf X M)) := by
    change IsZero ((Scheme.Modules.stalkFunctor X x).obj M)
    by_contra hz
    exact hx (hrange.symm ▸ hsupp hz)
  let : Subsingleton (M.val.obj (op ⊤)) := hΓ
  let := moduleCohomologyModuleOfHom X α M 0
  let : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X M) 0) :=
    (moduleH0EquivOfHom X α M).injective.subsingleton
  let E := finiteClosedSupportH0Equiv X p hp hpclosed (moduleAddSheaf X M) haway
  have hprod : Subsingleton (∀ i, (Scheme.Modules.stalkFunctor X (p i)).obj M) :=
    E.symm.injective.subsingleton
  apply (Scheme.Modules.isZero_iff_stalks M).mpr
  intro x
  by_cases hx : x ∈ Set.range p
  · obtain ⟨i, rfl⟩ := hx
    let : Subsingleton ((Scheme.Modules.stalkFunctor X (p i)).obj M) := by
      let : ∀ j, Nonempty ((Scheme.Modules.stalkFunctor X (p j)).obj M) := fun _ ↦ ⟨0⟩
      have hev : Function.Surjective
          (fun s : ∀ j, (Scheme.Modules.stalkFunctor X (p j)).obj M ↦ s i) :=
        Function.surjective_eval i
      constructor
      intro a b
      obtain ⟨sa, hsa⟩ := hev a
      obtain ⟨sb, hsb⟩ := hev b
      exact hsa.symm.trans ((congrFun (hprod.elim sa sb) i).trans hsb)
    exact AddCommGrpCat.isZero_of_subsingleton _
  · exact haway x hx

/-- The actual original Leray edge has zero target when the original H1
map is surjective; complete-base H2 vanishing is derived from the source data. -/
theorem original_R1_sections_subsingleton_of_H1_surjective
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Spec (.of A)) [IsProper f] [IsDominant f]
    (hd : ringKrullDim A = 2)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (g : Y ⟶ X) [IsProper g] [IsDominant g] (hX : NormalStalks X)
    (hgf : IsIso (CommRingCat.ofHom (functionFieldMap g)))
    (hH1 : Function.Surjective (moduleCohomologyMapAlongLinear g
      (FiniteTraceCoordinates.structureScalar f)
      (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom) 1)) :
    Subsingleton ((moduleGlobalSectionsFunctorOfHom X
      (FiniteTraceCoordinates.structureScalar f)).obj
        (((Scheme.Modules.pushforward g).rightDerived 1).obj
          (FiniteTraceCoordinates.structureModule Y))) := by
  let α := FiniteTraceCoordinates.structureScalar f
  have hseq := moduleBirationalLeray_exact_of_complete_surface X f hd
    (actualModel_dimension_of_complete_surface A f hd hff) g hX hgf
  change Function.Injective (moduleBirationalLerayMap X α g hX hgf) ∧
    Function.Exact (moduleBirationalLerayMap X α g hX hgf)
      (moduleBirationalLerayEdge X α g hX hgf) ∧
    Function.Surjective (moduleBirationalLerayEdge X α g hX hgf) at hseq
  have hsurj : Function.Surjective (moduleBirationalLerayMap X α g hX hgf) := by
    rw [moduleBirationalLerayMap_eq_moduleCohomologyMapAlongLinear]
    exact hH1
  have hz (z : (moduleGlobalSectionsFunctorOfHom X α).obj
      (((Scheme.Modules.pushforward g).rightDerived 1).obj
        (FiniteTraceCoordinates.structureModule Y))) : z = 0 := by
    obtain ⟨y, rfl⟩ := hseq.2.2 z
    obtain ⟨x, rfl⟩ := hsurj y
    exact hseq.2.1.apply_apply_eq_zero x
  exact ⟨fun x y ↦ (hz x).trans (hz y).symm⟩

/-- The actual first higher direct image vanishes above a complete surface
model when its original H1 map is surjective. No R1 or support premise is supplied. -/
theorem original_R1_isZero_of_H1_surjective
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Spec (.of A)) [IsProper f] [IsDominant f]
    (hd : ringKrullDim A = 2)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (g : Y ⟶ X) [IsProper g] [IsDominant g] (hX : NormalStalks X)
    (hgf : IsIso (CommRingCat.ofHom (functionFieldMap g)))
    (hH1 : Function.Surjective (moduleCohomologyMapAlongLinear g
      (FiniteTraceCoordinates.structureScalar f)
      (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom) 1)) :
    IsZero (((Scheme.Modules.pushforward g).rightDerived 1).obj
      (FiniteTraceCoordinates.structureModule Y)) := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian f }
  obtain ⟨_, C, hC, hclosed, hsupp⟩ := original_R1_coherent_finite_closed_support
    g hX (actualModel_dimension_of_complete_surface A f hd hff) hgf
  exact module_isZero_of_finite_closed_support_of_sections_subsingleton X
    (FiniteTraceCoordinates.structureScalar f)
    (((Scheme.Modules.pushforward g).rightDerived 1).obj
      (FiniteTraceCoordinates.structureModule Y))
    C hC hclosed hsupp
    (original_R1_sections_subsingleton_of_H1_surjective A f hd hff g hX hgf hH1)

/-- The actual maximal model over a complete normal local surface has
vanishing original R1 for every normal proper birational modification.
This is a global higher-image assertion, with no local-replacement conclusion. -/
theorem exists_normal_model_original_R1_vanishing
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hd : ringKrullDim A = 2) (hbound : NormalModificationH1Bounded A) :
    ∃ (X : Scheme.{u}) (hX : IsIntegral X),
      letI := hX
      ∃ (f : X ⟶ Spec (.of A)) (hf : IsProper f) (hdom : IsDominant f),
        letI := hf
        letI := hdom
        NormalStalks X ∧ IsIso (CommRingCat.ofHom (functionFieldMap f)) ∧
          ∀ (Y : Scheme.{u}) [IsIntegral Y] (g : Y ⟶ X)
            [IsProper g] [IsDominant g],
            NormalStalks Y → IsIso (CommRingCat.ofHom (functionFieldMap g)) →
              IsZero (((Scheme.Modules.pushforward g).rightDerived 1).obj
                (FiniteTraceCoordinates.structureModule Y)) := by
  obtain ⟨_, X, hX, rest⟩ := exists_maximal_normalModification A hbound
  let : IsIntegral X := hX
  obtain ⟨f, hf, hdom, rest⟩ := rest
  let : IsProper f := hf
  let : IsDominant f := hdom
  obtain ⟨hXN, hff, _, _, hstable⟩ := rest
  refine ⟨X, hX, f, hf, hdom, hXN, hff, ?_⟩
  intro Y hY g hg hdg hYN hgf
  exact original_R1_isZero_of_H1_surjective A f hd hff g hXN hgf
    (hstable Y g hYN hgf).2

end AlgebraicGeometry.Scheme.Cohomology


