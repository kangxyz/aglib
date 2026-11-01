/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.StalkFinite
public import Aglib.AlgebraicGeometry.Modules.Coherent.Support.StalkStrata
public import Aglib.AlgebraicGeometry.Modules.Linear
public import Aglib.AlgebraicGeometry.Modules.Stalk.Exactness
public import Aglib.AlgebraicGeometry.Modules.Invertible.Nonvanishing.GlobalFrame
public import Aglib.AlgebraicGeometry.Modules.Invertible.Nonvanishing.Pullback
public import Aglib.AlgebraicGeometry.Modules.Tensor.Monoidal.Sections
public import Aglib.CategoryTheory.Monoidal.UnitMultiplication
public import Mathlib.RingTheory.Nakayama

/-!
# Actual support of a section-multiplication cokernel

The scalar core uses the original stalk map and Nakayama: on a finite
module over the actual local ring, scalar multiplication is surjective
exactly when the module is zero or the scalar is a unit. Consequently the
original cokernel is supported on the original support intersected with
the scalar's vanishing set. No injectivity or regularity is assumed.

The finite-stalk supplier uses the original affine localization and open
stalk comparison. Affine-local finite type suffices; no Noetherian bound
is added for this support calculation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Modules.Invertible SheafOfModulesOfCommRing
open CategoryTheory.MonoidalCategory
open scoped Pointwise

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Affine-local finite type gives finite generation of each original
module stalk, with its original structure-stalk scalar action. -/
theorem stalk_finite_of_affineLocallyFiniteType {X : Scheme.{u}}
    (M : X.Modules) (hM : affineLocallyFiniteType X M) (x : X) :
    Module.Finite (X.presheaf.stalk x) ((moduleStalk X x).obj M) := by
  obtain ⟨a, y, rfl⟩ := X.affineOpenCover.openCover.exists_eq x
  let j := X.affineOpenCover.f a
  let : IsOpenImmersion j := X.affineOpenCover.map_prop a
  change Module.Finite (X.presheaf.stalk (j y)) ((moduleStalk X (j y)).obj M)
  let R := X.affineOpenCover.X a
  let N := M.restrict j
  have hN := (affineLocallyFiniteType_spec_iff R N).mp
    (affineLocallyFiniteType_restrict j hM)
  let : N.IsQuasicoherent := hN.1
  let : Module.Finite R ((modulesSpecToSheaf.obj N).presheaf.obj (op ⊤)) := hN.2
  let eN := (moduleStalk (Spec R) y).mapIso (asIso N.fromTildeΓ)
  let : Module.Finite ((Spec R).presheaf.stalk y) ((moduleStalk (Spec R) y).obj N) :=
    Module.Finite.of_surjective (hM := Stalk.tilde_stalk_finite R _ y)
      eN.hom.hom eN.toLinearEquiv.surjective
  let P := (moduleStalk (Spec R) y).obj N
  let e := (restrictModuleStalkIso j y).app M
  let : IsIso (j.stalkMap y) := (IsOpenImmersion.iff_isIso_stalkMap.mp
    (inferInstanceAs (IsOpenImmersion j))).2 y
  exact Module.Finite.of_surjective
    (hM := Stalk.finite_restrictScalars (j.stalkMap y).hom
      (ConcreteCategory.bijective_of_isIso _).2 P)
    e.hom.hom e.toLinearEquiv.surjective

private theorem surjective_smul_iff_zero_or_unit
    (A : Type u) [CommRing A] [IsLocalRing A] (M : Type u)
    [AddCommGroup M] [Module A M] [Module.Finite A M] (c : A) :
    Function.Surjective (fun m : M => c • m) ↔ Subsingleton M ∨ IsUnit c := by
  constructor
  · intro hs
    by_cases hM : Subsingleton M
    · exact Or.inl hM
    · right
      let : Nontrivial M := not_subsingleton_iff_nontrivial.mp hM
      by_contra hc
      have hcJ : c ∈ (Module.annihilator A M).jacobson :=
        IsLocalRing.maximalIdeal_le_jacobson _
          ((IsLocalRing.mem_maximalIdeal c).mpr hc)
      apply Submodule.top_ne_pointwise_smul_of_mem_jacobson_annihilator hcJ
      apply le_antisymm _ le_top
      intro m _
      obtain ⟨v, hv⟩ := hs m
      exact (Submodule.mem_smul_pointwise_iff_exists m c (⊤ : Submodule A M)).mpr
        ⟨v, Submodule.mem_top, hv⟩
  · rintro (hz | ⟨c, rfl⟩)
    · let : Subsingleton M := hz
      intro m
      exact ⟨0, Subsingleton.elim _ _⟩
    · intro m
      refine ⟨(↑(c⁻¹) : A) • m, ?_⟩
      change (c : A) • ((↑(c⁻¹) : A) • m) = m
      rw [← mul_smul, Units.mul_inv, one_smul]

/-- The original global scalar endomorphism induces multiplication by
the original scalar germ on the actual module stalk. -/
theorem moduleStalk_globalScalarEndomorphism {X : Scheme.{u}}
    (M : X.Modules) (a : Γ(X, ⊤)) (x : X) :
    (moduleStalk X x).map (globalScalarEndomorphism X M a) =
      ModuleCat.ofHom (LinearMap.lsmul (X.presheaf.stalk x) ((moduleStalk X x).obj M)
        (X.presheaf.germ ⊤ x trivial a)) := by
  ext m
  obtain ⟨U, hx, s, rfl⟩ := M.presheaf.exists_germ_eq m
  change ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
    (globalScalarEndomorphism X M a).mapPresheaf)
      (M.presheaf.germ U x hx s) =
        X.presheaf.germ ⊤ x trivial a • M.presheaf.germ U x hx s
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  change M.presheaf.germ U x hx
    ((globalScalarEndomorphism X M a).val.app (op U) s) =
      X.presheaf.germ ⊤ x trivial a • M.presheaf.germ U x hx s
  rw [globalScalarEndomorphism_app]
  have h := PresheafOfModules.germ_smul M.val x U hx
    (X.presheaf.map (homOfLE le_top).op a) s
  exact h.trans (congrArg (fun b : X.presheaf.stalk x => b • M.presheaf.germ U x hx s)
    (X.presheaf.germ_res_apply (homOfLE le_top) x hx a))

/-- The actual cokernel of multiplication by a global scalar is supported
exactly where the finite-type coefficient is supported and the scalar vanishes. -/
theorem support_cokernel_globalScalarEndomorphism {X : Scheme.{u}}
    (M : X.Modules) (hM : affineLocallyFiniteType X M) (a : Γ(X, ⊤)) :
    support (cokernel (globalScalarEndomorphism X M a)) =
      support M ∩ (X.basicOpen a : Set X)ᶜ := by
  ext x
  let : Module.Finite (X.presheaf.stalk x) ((moduleStalk X x).obj M) :=
    stalk_finite_of_affineLocallyFiniteType M hM x
  have hzero : IsZero ((moduleStalk X x).obj (cokernel (globalScalarEndomorphism X M a))) ↔
      IsZero ((moduleStalk X x).obj M) ∨ IsUnit (X.presheaf.germ ⊤ x trivial a) := by
    rw [Iso.isZero_iff (PreservesCokernel.iso (moduleStalk X x)
      (globalScalarEndomorphism X M a)), ← Preadditive.epi_iff_isZero_cokernel,
      moduleStalk_globalScalarEndomorphism, ModuleCat.epi_iff_surjective]
    change Function.Surjective
      (fun m : (moduleStalk X x).obj M => X.presheaf.germ ⊤ x trivial a • m) ↔ _
    rw [surjective_smul_iff_zero_or_unit, ModuleCat.isZero_iff_subsingleton]
  change (¬ IsZero ((stalkFunctor X x).obj (cokernel (globalScalarEndomorphism X M a)))) ↔
    (¬ IsZero ((stalkFunctor X x).obj M)) ∧ x ∉ X.basicOpen a
  rw [← Coherent.Support.moduleStalk_isZero_iff, ← Coherent.Support.moduleStalk_isZero_iff,
    hzero, not_or, Scheme.mem_basicOpen_top]

-- The native monoidal module carrier and its original ring-sheaf sections coincide here.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem sectionTensor_apply (X : Scheme.{u}) (L M : X.Modules)
    (s : Γ(L, ⊤)) (U : X.Opens) (m : Γ(M, U)) :
    (unitMultiply ((unitHomGlobalSectionsEquiv X L).symm s) M).val.app (op U) m =
      moduleTensorSection X L M U (L.presheaf.map (homOfLE le_top).op s) m := by
  let σ : (𝟙_ X.Modules) ⟶ L := (unitHomGlobalSectionsEquiv X L).symm s
  change (σ ▷ M).val.app (op U)
    ((λ_ M).inv.val.app (op U) m) = _
  rw [leftUnitor_inv_moduleTensorSection]
  have ht := whiskerRight_moduleTensorSection σ M U (1 : Γ(X, U)) m
  have hs := unitHomGlobalSectionsEquiv_symm_app X L s U (1 : Γ(X, U))
  rw [one_smul] at hs
  exact ht.trans (congrArg (fun t => moduleTensorSection X L M U t m) hs)

-- The actual open restriction has the same sections with the transported scalar action.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem sectionTensor_restrict {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (L M : X.Modules) (s : Γ(L, ⊤)) :
    (unitMultiply ((unitHomGlobalSectionsEquiv U (L.restrict j)).symm
      (Nonvanishing.restrictSection j L s)) (M.restrict j)) ≫
        (tensorRestrictionIso j L M).hom =
      (Scheme.Modules.restrictFunctor j).map
        (unitMultiply ((unitHomGlobalSectionsEquiv X L).symm s) M) := by
  apply Scheme.Modules.hom_ext
  intro V
  ext m
  change (tensorRestrictionIso j L M).hom.app V
    ((unitMultiply ((unitHomGlobalSectionsEquiv U (L.restrict j)).symm
      (Nonvanishing.restrictSection j L s)) (M.restrict j)).val.app (op V) m) =
        (unitMultiply ((unitHomGlobalSectionsEquiv X L).symm s) M).val.app (op (j ''ᵁ V)) m
  rw [sectionTensor_apply, sectionTensor_apply, tensorRestrictionIso_section]
  have hs : (L.restrictAppIso j V).hom
      ((L.restrict j).presheaf.map (homOfLE le_top).op
        (Nonvanishing.restrictSection j L s)) =
      L.presheaf.map (homOfLE le_top).op s := by
    change L.presheaf.map (homOfLE (j.image_mono (show V ≤ ⊤ from le_top))).op
      (L.presheaf.map (homOfLE le_top).op s) = _
    exact (congrArg (fun f : Γ(L, ⊤) ⟶ Γ(L, j ''ᵁ V) => f s)
      (L.presheaf.map_comp (homOfLE (show j ''ᵁ ⊤ ≤ ⊤ from le_top)).op
        (homOfLE (j.image_mono (show V ≤ ⊤ from le_top))).op)).symm
  exact congrArg (fun t => moduleTensorSection X L M (j ''ᵁ V) t m) hs

-- Tensor coefficients cross the native commutative sheaf and ring-sheaf presentations.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem sectionTensor_comp_unitFrame {X : Scheme.{u}}
    (L M : X.Modules) (e : L ≅ SheafOfModules.unit X.ringCatSheaf) (s : Γ(L, ⊤)) :
    unitMultiply ((unitHomGlobalSectionsEquiv X L).symm s) M ≫
        (((tensorFunctor X.sheaf).mapIso e).app M ≪≫ (tensorLeftUnitIso X.sheaf).app M).hom =
      globalScalarEndomorphism X M (e.hom.val.app (op ⊤) s) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext m
  change ((tensorLeftUnitIso X.sheaf).hom.app M).val.app (op U)
    (((moduleTensorCoefficientMap X e.hom).app M).app U
      ((unitMultiply ((unitHomGlobalSectionsEquiv X L).symm s) M).val.app (op U) m)) =
    (globalScalarEndomorphism X M (e.hom.val.app (op ⊤) s)).app U m
  rw [sectionTensor_apply]
  have hc := moduleTensorCoefficientMap_section e.hom M U
    (L.presheaf.map (homOfLE le_top).op s) m
  have hunit := tensorLeftUnitIso_hom_section X M U
    (e.hom.app U (L.presheaf.map (homOfLE le_top).op s)) m
  have hg := globalScalarEndomorphism_app X M (e.hom.val.app (op ⊤) s) U m
  exact (congrArg (((tensorLeftUnitIso X.sheaf).hom.app M).val.app (op U)) hc).trans
    (hunit.trans ((congrArg (fun a : Γ(X, U) => a • m)
      (PresheafOfModules.naturality_apply e.hom.val (homOfLE le_top).op s)).trans hg.symm))

private theorem support_cokernel_sectionTensor_of_unitIso {X : Scheme.{u}}
    (L : LineBundle X) (e : L.val ≅ SheafOfModules.unit X.ringCatSheaf)
    (s : Γ(L.val, ⊤)) (M : X.Modules) (hM : affineLocallyFiniteType X M) :
    support (cokernel (unitMultiply ((unitHomGlobalSectionsEquiv X L.val).symm s) M)) =
      support M ∩ (nonvanishingOpen L s : Set X)ᶜ := by
  let ν : M ⟶ (moduleTensorLeftFunctor X L.val).obj M :=
    unitMultiply ((unitHomGlobalSectionsEquiv X L.val).symm s) M
  let eT : (moduleTensorLeftFunctor X L.val).obj M ≅ M :=
    ((tensorFunctor X.sheaf).mapIso e).app M ≪≫ (tensorLeftUnitIso X.sheaf).app M
  let eC := (cokernelCompIsIso ν eT.hom).symm ≪≫
    cokernelIsoOfEq (sectionTensor_comp_unitFrame L.val M e s)
  have h := support_cokernel_globalScalarEndomorphism M hM
    (e.hom.val.app (op ⊤) s)
  rw [← Nonvanishing.nonvanishingOpen_eq_basicOpen_of_unitIso L e s] at h
  exact (support_eq_of_iso eC).trans h

/-- For an arbitrary actual line-bundle section, its original multiplication
map has cokernel supported exactly on the original finite-type support
intersected with that section's vanishing set. No monomorphism, regularity,
Noetherianity or dimension hypothesis occurs. -/
theorem support_cokernel_tensor_section {X : Scheme.{u}} (L : LineBundle X)
    (s : Γ(L.val, ⊤)) (M : X.Modules) (hM : affineLocallyFiniteType X M) :
    support (cokernel ((tensorLeftUnitIso X.sheaf).inv.app M ≫
      (moduleTensorCoefficientMap X ((unitHomGlobalSectionsEquiv X L.val).symm s)).app M)) =
      support M ∩ (nonvanishingOpen L s : Set X)ᶜ := by
  change support (cokernel (unitMultiply ((unitHomGlobalSectionsEquiv X L.val).symm s) M)) = _
  ext x
  obtain ⟨U, hx, ⟨e⟩⟩ := (isLocallyRankOne_iff_restrict_unit L.val).mp L.property x
  let L' := Nonvanishing.restrictLineBundle U.ι L
  let s' := Nonvanishing.restrictSection U.ι L.val s
  let ν : M ⟶ (moduleTensorLeftFunctor X L.val).obj M :=
    unitMultiply ((unitHomGlobalSectionsEquiv X L.val).symm s) M
  let ν' : M.restrict U.ι ⟶
      (moduleTensorLeftFunctor U.toScheme L'.val).obj (M.restrict U.ι) :=
    unitMultiply ((unitHomGlobalSectionsEquiv U.toScheme L'.val).symm s') (M.restrict U.ι)
  let R : X.Modules ⥤ U.toScheme.Modules := Scheme.Modules.restrictFunctor U.ι
  let eT : (moduleTensorLeftFunctor U.toScheme L'.val).obj (M.restrict U.ι) ≅
      R.obj ((moduleTensorLeftFunctor X L.val).obj M) := tensorRestrictionIso U.ι L.val M
  let eC : R.obj (cokernel ν) ≅ cokernel ν' :=
    PreservesCokernel.iso R ν ≪≫
      cokernelIsoOfEq (sectionTensor_restrict U.ι L.val M s).symm ≪≫
        cokernelCompIsIso ν' eT.hom
  have h := (support_eq_of_iso eC).trans
    (support_cokernel_sectionTensor_of_unitIso L' e s' (M.restrict U.ι)
      (affineLocallyFiniteType_restrict U.ι hM))
  change support ((cokernel ν).restrict U.ι) =
    support (M.restrict U.ι) ∩ (nonvanishingOpen L' s' : Set U.toScheme)ᶜ at h
  dsimp only [L', s'] at h
  rw [support_restrict, support_restrict,
    Nonvanishing.nonvanishingOpen_restrictLineBundle] at h
  exact Set.ext_iff.mp h (⟨x, hx⟩ : U.toScheme)

end AlgebraicGeometry.Scheme.Modules
