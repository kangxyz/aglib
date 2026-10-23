/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Contraction.FormalNeighborhood.LocalCoordinates
public import Aglib.AlgebraicGeometry.Surfaces.Contraction.FormalNeighborhood.Vanishing
public import Aglib.AlgebraicGeometry.Modules.Invertible.TwoSections
public import Aglib.AlgebraicGeometry.Cohomology.Proper.StructureSheaf.Localization
public import Aglib.AlgebraicGeometry.Cohomology.Proper.FibreFormalFunctions.Stalk

/-!
# The original ordinary structure-map comparison

The original ordinary pushforward-stalk map is identified with the literal original local
structural ring map. The original first-order lifts prove bijectivity of that same map
for the selected projective presentation and generate its actual maximal ideal. The
semilinear conormal comparison proves nonprincipality independently of target normality.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Surfaces.Contraction.FormalNeighborhood

universe u v w t

section OriginalOrdinaryUnit

open AlgebraicGeometry.Scheme.Cohomology.ProperFibreFormalFunctions

variable {X Z : Scheme.{u}} (f : X ⟶ Z) (z : Z)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem fromSpecStalk_appLE_top (U : Z.Opens) (hz : z ∈ U)
    (ht : (⊤ : (Spec (Z.presheaf.stalk z)).Opens) ≤ Z.fromSpecStalk z ⁻¹ᵁ U) :
    (Z.fromSpecStalk z).appLE U ⊤ ht =
      Z.presheaf.germ U z hz ≫ (Scheme.ΓSpecIso (Z.presheaf.stalk z)).inv := by
  dsimp only [Scheme.Hom.appLE]
  rw [Scheme.fromSpecStalk_app hz]
  have hh : (Spec (Z.presheaf.stalk z)).presheaf.map
      (homOfLE (show Z.fromSpecStalk z ⁻¹ᵁ U ≤ ⊤ from le_top)).op ≫
      (Spec (Z.presheaf.stalk z)).presheaf.map (homOfLE ht).op = 𝟙 _ := by
    rw [← Functor.map_comp]
    exact (congrArg (Spec (Z.presheaf.stalk z)).presheaf.map
      (Subsingleton.elim _ (𝟙 (op (⊤ : (Spec (Z.presheaf.stalk z)).Opens))))).trans
        ((Spec (Z.presheaf.stalk z)).presheaf.map_id _)
  rw [Category.assoc, Category.assoc, hh, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual ordinary pushforward-stalk unit is exactly the original local
structural ring map through the native flat-base-change sections comparison. -/
theorem ordinaryUnit_localStructureHom [QuasiCompact f] [QuasiSeparated f]
    (a : Z.presheaf.stalk z) :
    ordinaryStalkLocalSectionsEquiv f z
      (((TopCat.Presheaf.stalkFunctor CommRingCat z).map f.c) a) =
        localStructureHom f z a := by
  obtain ⟨U, hz, s, rfl⟩ := Z.presheaf.exists_germ_eq a
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
    ordinaryStalkLocalSectionsEquiv_germ]
  let g := Z.fromSpecStalk z
  let b := pullback.snd f g
  let p := pullback.fst f g
  let hU : (⊤ : (Spec (Z.presheaf.stalk z)).Opens) ≤ g ⁻¹ᵁ U :=
    ProperFibreIdempotents.stalkRestriction_le z U hz
  let hW := localSourceRestriction_le f z U hz
  have hleft : (f.app U) ≫ p.appLE (f ⁻¹ᵁ U) ⊤ hW =
      (p ≫ f).appLE U ⊤ (by
        intro x _
        exact hW trivial) := by
    simpa only [Scheme.Hom.appLE_eq_app] using
      Scheme.Hom.appLE_comp_appLE p f U (f ⁻¹ᵁ U) ⊤ (le_refl _) hW
  have hright : g.appLE U ⊤ hU ≫ b.appTop =
      (b ≫ g).appLE U ⊤ (by
        intro x _
        exact hU trivial) := by
    have hb : b.appLE ⊤ ⊤ (by simp) = b.appTop := by
      simpa only [Scheme.Hom.preimage_top] using (b.appLE_eq_app (U := ⊤))
    have he := Scheme.Hom.appLE_comp_appLE b g U ⊤ ⊤ hU (by simp)
    rw [hb] at he
    exact he
  have hc : (p ≫ f).appLE U ⊤ (by intro x _; exact hW trivial) =
      (b ≫ g).appLE U ⊤ (by intro x _; exact hU trivial) := by
    congr 1
    exact pullback.condition
  have he : f.app U ≫ p.appLE (f ⁻¹ᵁ U) ⊤ hW =
      (Z.presheaf.germ U z hz ≫
        (Scheme.ΓSpecIso (Z.presheaf.stalk z)).inv) ≫ b.appTop := by
    rw [hleft, hc, ← hright, fromSpecStalk_appLE_top z U hz hU]
  exact ConcreteCategory.congr_hom he s

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Bijectivity of the literal original local structural map inverts the
ORIGINAL ordinary structure-sheaf map at the same image point. -/
theorem ordinaryUnit_stalk_isIso_of_localStructureHom_bijective
    [QuasiCompact f] [QuasiSeparated f]
    (hα : Function.Bijective (localStructureHom f z)) :
    IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat z).map f.c) := by
  let e := ordinaryStalkLocalSectionsEquiv f z
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · intro x y hxy
    apply hα.injective
    exact (ordinaryUnit_localStructureHom f z x).symm.trans
      ((congrArg e hxy).trans (ordinaryUnit_localStructureHom f z y))
  · intro y
    obtain ⟨a, ha⟩ := hα.surjective (e y)
    refine ⟨a, e.injective ?_⟩
    exact (ordinaryUnit_localStructureHom f z a).trans ha

end OriginalOrdinaryUnit

section OriginalKoszulSections

open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules.Invertible

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every actual ideal section is a linear combination of the original generating pair.
The lifting uses the canonical two-section sequence and vanishing of its actual dual. -/
theorem idealSection_inclusion_eq_sum
    {E X : Scheme.{u}} (i : E ⟶ X)
    (hI : IsLocallyRankOne X (Hom.idealModule i))
    (s : ULift.{u} (Fin 2) → (SheafOfModules.unit X.ringCatSheaf ⟶ Hom.idealModule i))
    [hEpi : Epi (Sigma.desc s)]
    (hH : Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf X (dualLineBundle X (cartierIdealLineBundle i hI)).val) 1))
    (m : Γ(Hom.idealModule i, ⊤)) :
    ∃ b : ULift.{u} (Fin 2) → Γ(X, ⊤),
      @Eq Γ(X, ⊤) ((Hom.idealInclusion i).val.app (op ⊤) m)
        (∑ j, Mul.mul (α := Γ(X, ⊤)) (b j) ((s j ≫ Hom.idealInclusion i).val.app (op ⊤)
          (1 : Γ(X, ⊤)) : Γ(X, ⊤))) := by
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let L := cartierIdealLineBundle i hI
  let S := twoSectionSequence L s
  have hs : Function.Surjective ((Sigma.desc s).val.app (op ⊤)) :=
    CartierCurve.sections_surjective_of_h1_subsingleton S
      (@twoSectionSequence_shortExact _ L s hEpi) hH
  let t : O ⟶ Hom.idealModule i := (unitHomGlobalSectionsEquiv X _).symm m
  obtain ⟨g, hg⟩ := exists_unitHom_factor_of_surjective (Sigma.desc s) hs t
  obtain ⟨c, hc⟩ := exists_eq_sum_sigma_ι g
  refine ⟨fun j => (unitHomGlobalSectionsEquiv X O (c j) : Γ(X, ⊤)), ?_⟩
  have ht : t ≫ Hom.idealInclusion i = ∑ j, c j ≫ s j ≫ Hom.idealInclusion i := by
    rw [← hg, hc, Preadditive.sum_comp, Preadditive.sum_comp]
    simp only [Category.assoc, Sigma.ι_comp_desc]
  calc
    (Hom.idealInclusion i).val.app (op ⊤) m =
        unitHomGlobalSectionsAddEquiv X O (t ≫ Hom.idealInclusion i) := by
      change (Hom.idealInclusion i).val.app (op ⊤) m =
        (Hom.idealInclusion i).val.app (op ⊤)
          (unitHomGlobalSectionsEquiv X _ ((unitHomGlobalSectionsEquiv X _).symm m))
      rw [Equiv.apply_symm_apply]
    _ = ∑ j, unitHomGlobalSectionsAddEquiv X O (c j ≫ s j ≫ Hom.idealInclusion i) := by
      rw [ht, map_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      let b : Γ(X, ⊤) := unitHomGlobalSectionsEquiv X O (c j)
      let φ : Γ(X, ⊤) →ₗ[Γ(X, ⊤)] Γ(X, ⊤) :=
        ((s j ≫ Hom.idealInclusion i).val.app (op ⊤)).hom
      change φ b = b * φ 1
      simpa only [smul_eq_mul, mul_one] using
        φ.map_smul b (1 : Γ(X, ⊤))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Original ideal-section generation puts the actual residue kernel in the original
base-ideal multiple. The pair's included functions are the specified original coefficients. -/
theorem kernel_mem_ideal_smul_of_twoSections
    {R : Type u} [CommRing R] {E X : Scheme.{u}} (i : E ⟶ X)
    (hI : IsLocallyRankOne X (Hom.idealModule i))
    (s : ULift.{u} (Fin 2) → (SheafOfModules.unit X.ringCatSheaf ⟶ Hom.idealModule i))
    [Epi (Sigma.desc s)]
    (hH : Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf X (dualLineBundle X (cartierIdealLineBundle i hI)).val) 1))
    (α : R →+* Γ(X, ⊤)) (I : Ideal R) (a : ULift.{u} (Fin 2) → R)
    (ha : ∀ j, a j ∈ I)
    (hs : ∀ j, (s j ≫ Hom.idealInclusion i).val.app (op ⊤) (1 : Γ(X, ⊤)) = α (a j))
    (b : Γ(X, ⊤)) (hb : i.appTop.hom b = 0) :
    letI : Algebra R Γ(X, ⊤) := α.toAlgebra
    b ∈ I • (⊤ : Submodule R Γ(X, ⊤)) := by
  let : Algebra R Γ(X, ⊤) := α.toAlgebra
  let m : Γ(Hom.idealModule i, ⊤) := (Hom.idealSectionsEquiv i ⊤).symm ⟨b, hb⟩
  have hm : (Hom.idealInclusion i).val.app (op ⊤) m = b := by
    rw [← Hom.idealSectionsEquiv_val]
    exact congrArg Subtype.val ((Hom.idealSectionsEquiv i ⊤).apply_symm_apply ⟨b, hb⟩)
  obtain ⟨c, hc⟩ := idealSection_inclusion_eq_sum i hI s hH m
  rw [← hm, hc]
  apply Submodule.sum_mem
  intro j _
  rw [hs j]
  have hj : a j • c j ∈ I • (⊤ : Submodule R Γ(X, ⊤)) :=
    Submodule.smul_mem_smul (ha j) (Submodule.mem_top : c j ∈ (⊤ : Submodule R Γ(X, ⊤)))
  change α (a j) * c j ∈ I • (⊤ : Submodule R Γ(X, ⊤)) at hj
  change c j * α (a j) ∈ I • (⊤ : Submodule R Γ(X, ⊤))
  exact (mul_comm (α (a j)) (c j)) ▸ hj

/-- Restriction to the original projective-line fibre followed by its actual
global-functions equivalence, over its full original coefficient field. -/
def projectiveLineResidueHom {k : Type u} [CommRing k] {X : Scheme.{u}}
    (i : ProjectiveSpace k (ULift.{u} (Fin 2)) ⟶ X) : Γ(X, ⊤) →+* k :=
  (globalFunctionsRingEquiv k (ULift.{u} (Fin 2))).symm.toRingHom.comp i.appTop.hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual geometric fibre triangle gives exactly the original scalar residue map. -/
theorem projectiveLineResidueHom_comp
    {R k : Type u} [CommRing R] [CommRing k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) (i : ProjectiveSpace k (ULift.{u} (Fin 2)) ⟶ X)
    (β : R →+* k)
    (w : i ≫ f = toSpec k (ULift.{u} (Fin 2)) ≫ Spec.map (CommRingCat.ofHom β)) :
    (projectiveLineResidueHom i).comp (affineFormalFunctionsScalar f) = β := by
  ext r
  apply (globalFunctionsRingEquiv k (ULift.{u} (Fin 2))).injective
  change (globalFunctionsRingEquiv k (ULift.{u} (Fin 2)))
      ((globalFunctionsRingEquiv k (ULift.{u} (Fin 2))).symm
        (i.appTop.hom (affineFormalFunctionsScalar f r))) = _
  rw [RingEquiv.apply_symm_apply]
  have hw := congrArg (fun q : ProjectiveSpace k (ULift.{u} (Fin 2)) ⟶ Spec (.of R) =>
    (Scheme.ΓSpecIso (.of R)).inv ≫ q.appTop) w
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop,
    ← Scheme.ΓSpecIso_inv_naturality_assoc] at hw
  exact ConcreteCategory.congr_hom hw r

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual proper formal functions, the original Koszul row and finite Nakayama
make the original structural map surjective. Its pair consists of original base coefficients. -/
theorem structuralMap_surjective_of_twoSections
    {R k : Type u} [CommRing R] [IsNoetherianRing R] [CommRing k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]
    (i : ProjectiveSpace k (ULift.{u} (Fin 2)) ⟶ X) [IsClosedImmersion i]
    (hI : IsLocallyRankOne X (Hom.idealModule i))
    (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
      twistingSheaf k (ULift.{u} (Fin 2)) 1)
    (I : Ideal R) (β : R →+* k) (hβ : RingHom.ker β = I)
    (hker : (Spec.map (CommRingCat.ofHom β)).ker.comap f = i.ker)
    (w : i ≫ f = toSpec k (ULift.{u} (Fin 2)) ≫ Spec.map (CommRingCat.ofHom β))
    (hJac : I ≤ (⊥ : Ideal R).jacobson) (hres : Function.Surjective β)
    (s : ULift.{u} (Fin 2) → (SheafOfModules.unit X.ringCatSheaf ⟶ Hom.idealModule i))
    [Epi (Sigma.desc s)] (a : ULift.{u} (Fin 2) → R) (ha : ∀ j, a j ∈ I)
    (hs : ∀ j, (s j ≫ Hom.idealInclusion i).val.app (op ⊤) (1 : Γ(X, ⊤)) =
      affineFormalFunctionsScalar f (a j)) :
    Function.Surjective (affineFormalFunctionsScalar f) := by
  let α := affineFormalFunctionsScalar f
  let δ := projectiveLineResidueHom i
  have hH := dualCartier_h1_subsingleton f i hI eI I β hβ hker hJac
  apply ringHom_surjective_of_finite_residue_kernel α δ I
    (Scheme.AffineStein.finite_structuralCoefficients R f) hJac
  · rw [projectiveLineResidueHom_comp f i β w]
    exact hres
  · intro b hb
    have hi : i.appTop.hom b = 0 := by
      apply (globalFunctionsRingEquiv k (ULift.{u} (Fin 2))).symm.injective
      exact hb.trans (map_zero _).symm
    exact kernel_mem_ideal_smul_of_twoSections i hI s hH α I a ha hs b hi

end OriginalKoszulSections

section OriginalSelectedStructureMap

open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Cohomology.ProperFibreFormalFunctions

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original local structural coefficient of a germ is its original pullback
from the same neighborhood. This is the existing ordinary-unit comparison on that germ. -/
theorem localStructureHom_germ {X Z : Scheme.{u}} (f : X ⟶ Z) (z : Z)
    [QuasiCompact f] [QuasiSeparated f] (U : Z.Opens) (hz : z ∈ U) (s : Γ(Z, U)) :
    localStructureHom f z ((Z.presheaf.germ U z hz).hom s) =
      (pullback.fst f (Z.fromSpecStalk z)).appLE (f ⁻¹ᵁ U) ⊤
        (localSourceRestriction_le f z U hz) ((f.app U).hom s) := by
  have h := ordinaryUnit_localStructureHom f z ((Z.presheaf.germ U z hz).hom s)
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
    ordinaryStalkLocalSectionsEquiv_germ] at h
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Once the original structure map is bijective, the original Koszul generators
generate exactly the original base ideal, with their original coefficient values. -/
theorem structuralIdeal_eq_span_of_twoSections
    {R k : Type u} [CommRing R] [CommRing k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) (i : ProjectiveSpace k (ULift.{u} (Fin 2)) ⟶ X)
    (hI : IsLocallyRankOne X (Hom.idealModule i))
    (s : ULift.{u} (Fin 2) → (SheafOfModules.unit X.ringCatSheaf ⟶ Hom.idealModule i))
    [Epi (Sigma.desc s)]
    (hH : Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf X (dualLineBundle X (cartierIdealLineBundle i hI)).val) 1))
    (I : Ideal R) (β : R →+* k) (hβ : RingHom.ker β = I)
    (w : i ≫ f = toSpec k (ULift.{u} (Fin 2)) ≫ Spec.map (CommRingCat.ofHom β))
    (a : ULift.{u} (Fin 2) → R) (ha : ∀ j, a j ∈ I)
    (hs : ∀ j, (s j ≫ Hom.idealInclusion i).val.app (op ⊤) (1 : Γ(X, ⊤)) =
      affineFormalFunctionsScalar f (a j))
    (hα : Function.Bijective (affineFormalFunctionsScalar f)) :
    I = Ideal.span (Set.range a) := by
  let α := affineFormalFunctionsScalar f
  apply le_antisymm
  · intro r hr
    have hβr : β r = 0 := by
      rw [← hβ] at hr
      exact hr
    have hδ : projectiveLineResidueHom i (α r) = 0 :=
      (congrArg (fun h : R →+* k => h r) (projectiveLineResidueHom_comp f i β w)).trans hβr
    have hi : i.appTop.hom (α r) = 0 := by
      apply (globalFunctionsRingEquiv k (ULift.{u} (Fin 2))).symm.injective
      exact hδ.trans (map_zero _).symm
    let m : Γ(Hom.idealModule i, ⊤) := (Hom.idealSectionsEquiv i ⊤).symm ⟨α r, hi⟩
    have hm : (Hom.idealInclusion i).val.app (op ⊤) m = α r := by
      rw [← Hom.idealSectionsEquiv_val]
      exact congrArg Subtype.val ((Hom.idealSectionsEquiv i ⊤).apply_symm_apply ⟨α r, hi⟩)
    obtain ⟨c, hc⟩ := idealSection_inclusion_eq_sum i hI s hH m
    choose b hb using fun j => hα.surjective (c j)
    have hr' : r = ∑ j, b j * a j := by
      apply hα.injective
      calc
        α r = (Hom.idealInclusion i).val.app (op ⊤) m := hm.symm
        _ = ∑ j, c j * α (a j) :=
          hc.trans (Finset.sum_congr rfl (fun j _ =>
            congrArg (fun z : Γ(X, ⊤) => c j * z) (hs j)))
        _ = α (∑ j, b j * a j) := by
          change ∑ j, c j * affineFormalFunctionsScalar f (a j) =
            affineFormalFunctionsScalar f (∑ j, b j * a j)
          simp only [map_sum, map_mul, hb]
    rw [hr']
    apply Ideal.sum_mem
    intro j _
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
  · apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact ha j

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}}
  {p : X ⟶ ProjectiveSpace A ι} {k : Type u} [Field k]
  (i : ProjectiveSpace k (ULift.{u} (Fin 2)) ⟶ X) [IsClosedImmersion i]
  (hI : IsLocallyRankOne X (Hom.idealModule i)) (H : LineBundle X)
  {eP : H.val ≅ (Scheme.Modules.pullback p).obj (twistingSheaf A ι 1)} (d : ℕ)
  {n : ℕ} {hn : 1 ≤ n}
  (F : CartierProjectivePresentation p i hI H eP d n hn)
  (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
    twistingSheaf k (ULift.{u} (Fin 2)) 1)
  (eH : (Scheme.Modules.pullback i).obj H.val ≅
    twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The selected original image-coordinate germ belongs to the original image-local
maximal ideal. Its residue is computed by the actual closed-point stalk map. -/
theorem selectedLocalCoordinate_mem_maximalIdeal (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀)))
    [IsClosedImmersion (F.residueToImage eI eH j₀ h₀)]
    (j : F.index)
    (hz : cartierResidueCoefficient i hI H d eI eH n (F.sections j) = 0) :
    selectedLocalCoordinate i hI H d F eI eH j₀ h₀ j ∈
      pointMaximalIdeal (F.residueToImage eI eH j₀ h₀) := by
  let c := F.residueToImage eI eH j₀ h₀
  let U := F.pointChartOpen j₀
  let hU := imagePoint_mem_pointChart i hI H d F eI eH j₀ h₀
  have hz' := F.pointChartCoordinate_mem_pointIdeal eI eH (Field.toIsField k) j₀ h₀ j hz
  rw [CartierProjectivePresentation.pointIdeal, Hom.ker_apply] at hz'
  change c.app U (F.pointChartCoordinate j₀ j) = 0 at hz'
  rw [← ker_pointResidueHom c]
  change pointResidueHom c (selectedLocalCoordinate i hI H d F eI eH j₀ h₀ j) = 0
  have he := ConcreteCategory.congr_hom (Scheme.germ_stalkClosedPointTo c U hU)
    (F.pointChartCoordinate j₀ j)
  let e := (Spec (.of k)).presheaf.mapIso
    (eqToIso (Scheme.preimage_eq_top_of_closedPoint_mem c hU).symm).op ≪≫
      Scheme.ΓSpecIso (.of k)
  change pointResidueHom c (selectedLocalCoordinate i hI H d F eI eH j₀ h₀ j) =
    e.hom.hom (c.app U (F.pointChartCoordinate j₀ j)) at he
  rw [hz', map_zero] at he
  exact he

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The selected original local ideal section includes as the literal original
structural image of the selected image-coordinate germ. -/
theorem selectedLocalIdealCoordinate_inclusion [QuasiCompact F.toImage]
    [QuasiSeparated F.toImage] (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀)))
    (j : F.index)
    (hz : cartierResidueCoefficient i hI H d eI eH n (F.sections j) = 0) :
    let c := F.residueToImage eI eH j₀ h₀
    (selectedLocalIdealCoordinate i hI H d F eI eH j₀ h₀ j hz ≫
        Hom.idealInclusion (selectedLocalExceptional i hI H d F eI eH j₀ h₀)).val.app
          (op ⊤) (1 : Γ(localSource F.toImage (imagePoint c), ⊤)) =
      localStructureHom F.toImage (imagePoint c)
        (selectedLocalCoordinate i hI H d F eI eH j₀ h₀ j) := by
  let c := F.residueToImage eI eH j₀ h₀
  let z := imagePoint c
  let U := F.pointChartOpen j₀
  let g := pullback.fst F.toImage (F.image.fromSpecStalk z)
  let V := F.toImage ⁻¹ᵁ U
  let hV := localSource_preimage_pointChart i hI H d F eI eH j₀ h₀
  let v := F.pointChartExceptionalCoordinate eI eH (Field.toIsField k) j₀ h₀ j hz
  let e := localExceptionalIdealIso c F.toImage i (toSpec k (ULift.{u} (Fin 2)))
    (F.exceptional_toImage_eq eI eH j₀ h₀).symm
  have hm : selectedLocalIdealCoordinate i hI H d F eI eH j₀ h₀ j hz ≫
      Hom.idealInclusion (selectedLocalExceptional i hI H d F eI eH j₀ h₀) =
      pullbackSectionOn g (SheafOfModules.unit X.ringCatSheaf) V hV
          ((F.toImage.app U).hom (F.pointChartCoordinate j₀ j)) ≫
        (pullbackUnitIso g).hom := by
    change (pullbackSectionOn g (Hom.idealModule i) V hV v ≫ e.hom) ≫ _ = _
    rw [Category.assoc, localExceptionalIdealIso_hom_inclusion, ← Category.assoc,
      ← pullbackSectionOn_map]
    rw [F.pointChartExceptionalCoordinate_inclusion eI eH (Field.toIsField k) j₀ h₀ j hz]
  change (selectedLocalIdealCoordinate i hI H d F eI eH j₀ h₀ j hz ≫
      Hom.idealInclusion (selectedLocalExceptional i hI H d F eI eH j₀ h₀)).val.app
        (op ⊤) (1 : Γ(localSource F.toImage z, ⊤)) =
    localStructureHom F.toImage z (selectedLocalCoordinate i hI H d F eI eH j₀ h₀ j)
  rw [hm]
  exact (pullbackSectionOn_unit_apply g V hV
      ((F.toImage.app U).hom (F.pointChartCoordinate j₀ j))).trans
    (localStructureHom_germ F.toImage z U
      (imagePoint_mem_pointChart i hI H d F eI eH j₀ h₀)
      (F.pointChartCoordinate j₀ j)).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original raw image has exactly the original local structural ring.
The original first-order pair gives the Koszul row, actual formal functions kills
its dual H1, and finite Nakayama gives surjectivity. Native image-stalk injectivity
gives injectivity. No normality or coefficient-field section is assumed. -/
theorem selectedLocalStructureAndParameters [IsNoetherianRing A] [IsClosedImmersion p]
    (r : ℕ) (eι : ι ≃ Fin (r + 1)) (hn2 : 2 ≤ n * d) (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀)))
    (hρ : Function.Surjective ((cartierResidueMap i hI H d eI eH n).val.app (op ⊤)))
    (t : ULift.{u} (Fin 2) → (SheafOfModules.unit X.ringCatSheaf ⟶
      (cartierPowerTwist i hI H n (n * d - 2 + 1)).val))
    (ht : ∀ a, t a ≫ (cartierStepSequence i hI
      (cartierPowerTwist i hI H n (n * d - 2))).g =
        firstOrderQuotientCoordinate i hI H d eI eH n hn2 a)
    (q : ULift.{u} (Fin 2) → F.index)
    (hq : ∀ a, F.sections (q a) = firstOrderCartierImage i hI H d n hn2 (t a)) :
    Function.Bijective (localStructureHom F.toImage
        (imagePoint (F.residueToImage eI eH j₀ h₀))) ∧
      pointMaximalIdeal (F.residueToImage eI eH j₀ h₀) =
        Ideal.span {selectedLocalCoordinate i hI H d F eI eH j₀ h₀ (q ⟨0⟩),
          selectedLocalCoordinate i hI H d F eI eH j₀ h₀ (q ⟨1⟩)} := by
  let _ : Finite ι := Finite.of_equiv _ eι.symm
  let _ : Finite F.index := F.finiteIndex
  let _ : IsProper F.toImage := F.toImage_isProper r eι
  let _ : IsProper F.toProjective := F.toProjective_isProper r eι
  let _ : IsLocallyNoetherian F.image :=
    LocallyOfFiniteType.isLocallyNoetherian F.imageInclusion
  let c := F.residueToImage eI eH j₀ h₀
  let _ : IsClosedImmersion c :=
    F.residueToImage_isClosedImmersion eI eH (Field.toIsField k) j₀ h₀ hρ
  let a := toSpec k (ULift.{u} (Fin 2))
  let w := (F.exceptional_toImage_eq eI eH j₀ h₀).symm
  let z := imagePoint c
  let _ : IsNoetherianRing (F.image.presheaf.stalk z) := inferInstance
  let j := localExceptional c F.toImage i a w
  let b := localSourceMap F.toImage z
  have hker : c.ker.comap F.toImage = i.ker :=
    F.pointIdeal_comap_eq eI eH r eι (Field.toIsField k) hn2 j₀ h₀ hρ t ht q hq
  let _ : IsClosedImmersion j := localExceptional_isClosedImmersion c F.toImage i a w hker
  let hJ := localExceptional_locallyRankOne c F.toImage i a w hI
  let eJ := localExceptionalConormalIso c F.toImage i a w eI
  let hz : ∀ x : ULift.{u} (Fin 2),
      cartierResidueCoefficient i hI H d eI eH n (F.sections (q x)) = 0 :=
    fun x => (congrArg (cartierResidueCoefficient i hI H d eI eH n) (hq x)).trans
      (firstOrderCartierImage_residueCoefficient i hI H d eI eH n hn2 (t x))
  let s := fun x => selectedLocalIdealCoordinate i hI H d F eI eH j₀ h₀ (q x) (hz x)
  let u := fun x => selectedLocalCoordinate i hI H d F eI eH j₀ h₀ (q x)
  let _ : Epi (Sigma.desc s) :=
    selectedLocalIdealCoordinates_epi i hI H d F eI eH hn2 j₀ h₀ hker t ht q hq
  have hsur : Function.Surjective (localStructureHom F.toImage z) :=
    structuralMap_surjective_of_twoSections (R := pointLocalRing c) b j hJ eJ (pointMaximalIdeal c)
      (pointResidueHom c) (ker_pointResidueHom c)
      (localExceptional_pointIdeal_comap c F.toImage i a w hker)
      (localExceptional_snd c F.toImage i a w)
      (IsLocalRing.maximalIdeal_le_jacobson ⊥) (pointResidueHom_surjective c)
      s u (fun x => selectedLocalCoordinate_mem_maximalIdeal i hI H d F eI eH
        j₀ h₀ (q x) (hz x))
      (fun x => selectedLocalIdealCoordinate_inclusion i hI H d F eI eH
        j₀ h₀ (q x) (hz x))
  have hinj : Function.Injective (localStructureHom F.toImage z) := by
    have hunit : Function.Injective
        ((TopCat.Presheaf.stalkFunctor CommRingCat z).map F.toImage.c) :=
      F.toProjective.stalkFunctor_toImage_injective z
    intro x y hxy
    apply hunit
    apply (ordinaryStalkLocalSectionsEquiv F.toImage z).injective
    exact (ordinaryUnit_localStructureHom F.toImage z x).trans
      (hxy.trans (ordinaryUnit_localStructureHom F.toImage z y).symm)
  have hbij : Function.Bijective (localStructureHom F.toImage z) := ⟨hinj, hsur⟩
  refine ⟨hbij, ?_⟩
  have hH := dualCartier_h1_subsingleton (R := pointLocalRing c) b j hJ eJ (pointMaximalIdeal c)
    (pointResidueHom c) (ker_pointResidueHom c)
    (localExceptional_pointIdeal_comap c F.toImage i a w hker)
    (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  have hgen := structuralIdeal_eq_span_of_twoSections b j hJ s hH (pointMaximalIdeal c)
    (pointResidueHom c) (ker_pointResidueHom c) (localExceptional_snd c F.toImage i a w)
    u (fun x => selectedLocalCoordinate_mem_maximalIdeal i hI H d F eI eH
      j₀ h₀ (q x) (hz x))
    (fun x => selectedLocalIdealCoordinate_inclusion i hI H d F eI eH
      j₀ h₀ (q x) (hz x)) hbij
  rw [hgen]
  congr 1
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨y⟩, rfl⟩
    fin_cases y <;> simp [u]
  · intro hx
    rcases hx with rfl | rfl
    · exact ⟨⟨0⟩, rfl⟩
    · exact ⟨⟨1⟩, rfl⟩

end OriginalSelectedStructureMap

section OriginalConormalCoefficients

open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules.Invertible

variable {R k : Type u} [CommRing R] [CommRing k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of R)) (i : ProjectiveSpace k (ULift.{u} (Fin 2)) ⟶ X)
  (I : Ideal R) (β : R →+* k) (hβ : RingHom.ker β = I)
  (w : i ≫ f = toSpec k (ULift.{u} (Fin 2)) ≫ Spec.map (CommRingCat.ofHom β))

include β hβ w

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An original base-ideal coefficient restricts to zero on the actual fibre. -/
theorem coefficient_restrict_eq_zero (r : I) :
    i.appTop.hom (affineFormalFunctionsScalar f r.val) = 0 := by
  have hr : β r.val = 0 := by
    have h : r.val ∈ RingHom.ker β := by rw [hβ]; exact r.property
    exact h
  have hδ : projectiveLineResidueHom i (affineFormalFunctionsScalar f r.val) = 0 :=
    (congrArg (fun h : R →+* k => h r.val) (projectiveLineResidueHom_comp f i β w)).trans hr
  apply (globalFunctionsRingEquiv k (ULift.{u} (Fin 2))).symm.injective
  exact hδ.trans (map_zero _).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The unique section of the actual exceptional kernel with the original
structural coefficient as its literal included function. -/
def idealSectionOfCoefficient (r : I) : Γ(Hom.idealModule i, ⊤) :=
  (Hom.idealSectionsEquiv i ⊤).symm
    ⟨affineFormalFunctionsScalar f r.val, coefficient_restrict_eq_zero f i I β hβ w r⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem idealSectionOfCoefficient_inclusion (r : I) :
    (Hom.idealInclusion i).val.app (op ⊤) (idealSectionOfCoefficient f i I β hβ w r) =
      affineFormalFunctionsScalar f r.val := by
  rw [← Hom.idealSectionsEquiv_val]
  exact congrArg Subtype.val ((Hom.idealSectionsEquiv i ⊤).apply_symm_apply _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Addition of original coefficients is addition of their actual ideal sections. -/
theorem idealSectionOfCoefficient_add (r s : I) :
    idealSectionOfCoefficient f i I β hβ w (r + s) =
      idealSectionOfCoefficient f i I β hβ w r + idealSectionOfCoefficient f i I β hβ w s := by
  apply (Hom.idealSectionsEquiv i ⊤).injective
  simp only [map_add, idealSectionOfCoefficient, LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  exact map_add (affineFormalFunctionsScalar f) r.val s.val

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Multiplication by an original base coefficient acts through the original structural map. -/
theorem idealSectionOfCoefficient_smul (r : R) (s : I) :
    idealSectionOfCoefficient f i I β hβ w (r • s) =
      affineFormalFunctionsScalar f r • idealSectionOfCoefficient f i I β hβ w s := by
  apply (Hom.idealSectionsEquiv i ⊤).injective
  have h : Hom.idealSectionsEquiv i ⊤ (idealSectionOfCoefficient f i I β hβ w (r • s)) =
      affineFormalFunctionsScalar f r •
        Hom.idealSectionsEquiv i ⊤ (idealSectionOfCoefficient f i I β hβ w s) := by
    simp only [idealSectionOfCoefficient, LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    exact map_mul (affineFormalFunctionsScalar f) r s.val
  exact h.trans ((Hom.idealSectionsEquiv i ⊤).map_smul (affineFormalFunctionsScalar f r)
    (idealSectionOfCoefficient f i I β hβ w s)).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Original base-ideal coefficients give actual conormal global sections.
Semilinearity uses only the original residue map and the original fibre triangle. -/
def conormalCoefficientMap
    (e : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
      twistingSheaf k (ULift.{u} (Fin 2)) 1) :
    letI := Module.compHom Γ(twistingSheaf k (ULift.{u} (Fin 2)) 1, ⊤)
      (affineFormalFunctionsScalar (toSpec k (ULift.{u} (Fin 2))))
    I →ₛₗ[β] Γ(twistingSheaf k (ULift.{u} (Fin 2)) 1, ⊤) := by
  letI := Module.compHom Γ(twistingSheaf k (ULift.{u} (Fin 2)) 1, ⊤)
    (affineFormalFunctionsScalar (toSpec k (ULift.{u} (Fin 2))))
  let P := (Scheme.Modules.pullback i).obj (Hom.idealModule i)
  let u₀ := ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
    (Hom.idealModule i)).val.app (op ⊤)
  let u : Γ(Hom.idealModule i, ⊤) →+ Γ(P, ⊤) := u₀.hom.toAddMonoidHom
  let v : Γ(P, ⊤) →ₗ[Γ(ProjectiveSpace k (ULift.{u} (Fin 2)), ⊤)]
      Γ(twistingSheaf k (ULift.{u} (Fin 2)) 1, ⊤) := (e.hom.val.app (op ⊤)).hom
  refine
    { toFun := fun r => v (u (idealSectionOfCoefficient f i I β hβ w r))
      map_add' := ?_
      map_smul' := ?_ }
  · intro r s
    rw [idealSectionOfCoefficient_add, map_add, map_add]
  · intro r s
    rw [idealSectionOfCoefficient_smul]
    have hu : u (affineFormalFunctionsScalar f r • idealSectionOfCoefficient f i I β hβ w s) =
        i.appTop.hom (affineFormalFunctionsScalar f r) •
          u (idealSectionOfCoefficient f i I β hβ w s) :=
      u₀.hom.map_smul (affineFormalFunctionsScalar f r) _
    have hc : i.appTop.hom (affineFormalFunctionsScalar f r) =
        globalFunctionsRingEquiv k (ULift.{u} (Fin 2)) (β r) :=
      ((globalFunctionsRingEquiv k (ULift.{u} (Fin 2))).apply_symm_apply _).symm.trans
        (congrArg (globalFunctionsRingEquiv k (ULift.{u} (Fin 2)))
          (congrArg (fun h : R →+* k => h r) (projectiveLineResidueHom_comp f i β w)))
    calc
      _ = v (i.appTop.hom (affineFormalFunctionsScalar f r) •
          u (idealSectionOfCoefficient f i I β hβ w s)) := congrArg v hu
      _ = i.appTop.hom (affineFormalFunctionsScalar f r) •
          v (u (idealSectionOfCoefficient f i I β hβ w s)) := v.map_smul _ _
      _ = _ := by rw [hc]; rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The coefficient-to-conormal map agrees with the actual pullback of any
original ideal section having that same included coefficient. -/
theorem conormalCoefficientMap_apply_of_section
    (e : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
      twistingSheaf k (ULift.{u} (Fin 2)) 1)
    (r : I) (s : SheafOfModules.unit X.ringCatSheaf ⟶ Hom.idealModule i)
    (hs : (s ≫ Hom.idealInclusion i).val.app (op ⊤) (1 : Γ(X, ⊤)) =
      affineFormalFunctionsScalar f r.val) :
    conormalCoefficientMap f i I β hβ w e r =
      unitHomGlobalSectionsEquiv (ProjectiveSpace k (ULift.{u} (Fin 2))) _
        (FromSections.pullbackSection i s ≫ e.hom) := by
  have hsection : idealSectionOfCoefficient f i I β hβ w r =
      unitHomGlobalSectionsEquiv X (Hom.idealModule i) s := by
    apply (Hom.idealSectionsEquiv i ⊤).injective
    apply Subtype.ext
    rw [Hom.idealSectionsEquiv_val, Hom.idealSectionsEquiv_val]
    exact (idealSectionOfCoefficient_inclusion f i I β hβ w r).trans hs.symm
  change e.hom.val.app (op ⊤)
    (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app (Hom.idealModule i)).val.app
      (op ⊤) (idealSectionOfCoefficient f i I β hβ w r)) = _
  rw [hsection, unitHomGlobalSectionsEquiv_naturality, FromSections.pullbackSection_global]
  rfl

end OriginalConormalCoefficients

section OriginalSelectedConormalCoefficients

open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules.Invertible

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}}
  {p : X ⟶ ProjectiveSpace A ι} {k : Type u} [Field k]
  (i : ProjectiveSpace k (ULift.{u} (Fin 2)) ⟶ X) [IsClosedImmersion i]
  (hI : IsLocallyRankOne X (Hom.idealModule i)) (H : LineBundle X)
  {eP : H.val ≅ (Scheme.Modules.pullback p).obj (twistingSheaf A ι 1)} (d : ℕ)
  {n : ℕ} {hn : 1 ≤ n}
  (F : CartierProjectivePresentation p i hI H eP d n hn)
  (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
    twistingSheaf k (ULift.{u} (Fin 2)) 1)
  (eH : (Scheme.Modules.pullback i).obj H.val ≅
    twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical original image-local maximal ideal maps to the original conormal
global sections semilinearly for the full actual residue field. -/
def selectedLocalConormalMap (hn2 : 2 ≤ n * d) (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀)))
    [IsClosedImmersion (F.residueToImage eI eH j₀ h₀)] :
    letI := Module.compHom Γ(twistingSheaf k (ULift.{u} (Fin 2)) 1, ⊤)
      (affineFormalFunctionsScalar (toSpec k (ULift.{u} (Fin 2))))
    pointMaximalIdeal (F.residueToImage eI eH j₀ h₀) →ₛₗ[
      pointResidueHom (F.residueToImage eI eH j₀ h₀)]
        Γ(twistingSheaf k (ULift.{u} (Fin 2)) 1, ⊤) :=
  conormalCoefficientMap
    (localSourceMap F.toImage (imagePoint (F.residueToImage eI eH j₀ h₀)))
    (selectedLocalExceptional i hI H d F eI eH j₀ h₀)
    (pointMaximalIdeal (F.residueToImage eI eH j₀ h₀))
    (pointResidueHom (F.residueToImage eI eH j₀ h₀))
    (ker_pointResidueHom (F.residueToImage eI eH j₀ h₀))
    (localExceptional_snd (F.residueToImage eI eH j₀ h₀) F.toImage i
      (toSpec k (ULift.{u} (Fin 2))) (F.exceptional_toImage_eq eI eH j₀ h₀).symm)
    (selectedLocalConormalIso i hI H d F eI eH hn2 j₀ h₀)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The two original image-coordinate coefficients have exactly the original
degree-one basis images in conormal global sections. -/
theorem selectedLocalConormalMap_coordinate [QuasiCompact F.toImage] [QuasiSeparated F.toImage]
    (hn2 : 2 ≤ n * d) (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀)))
    [IsClosedImmersion (F.residueToImage eI eH j₀ h₀)]
    (a : ULift.{u} (Fin 2))
    (t : SheafOfModules.unit X.ringCatSheaf ⟶
      (cartierPowerTwist i hI H n (n * d - 2 + 1)).val)
    (ht : t ≫ (cartierStepSequence i hI
      (cartierPowerTwist i hI H n (n * d - 2))).g =
        firstOrderQuotientCoordinate i hI H d eI eH n hn2 a)
    (q : F.index) (hq : F.sections q = firstOrderCartierImage i hI H d n hn2 t) :
    let hz := (congrArg (cartierResidueCoefficient i hI H d eI eH n) hq).trans
      (firstOrderCartierImage_residueCoefficient i hI H d eI eH n hn2 t)
    selectedLocalConormalMap i hI H d F eI eH hn2 j₀ h₀
      ⟨selectedLocalCoordinate i hI H d F eI eH j₀ h₀ q,
        selectedLocalCoordinate_mem_maximalIdeal i hI H d F eI eH j₀ h₀ q hz⟩ =
      exceptionalCoordinateBasis k a := by
  let c := F.residueToImage eI eH j₀ h₀
  let j := selectedLocalExceptional i hI H d F eI eH j₀ h₀
  let b := localSourceMap F.toImage (imagePoint c)
  let hz := (congrArg (cartierResidueCoefficient i hI H d eI eH n) hq).trans
    (firstOrderCartierImage_residueCoefficient i hI H d eI eH n hn2 t)
  let r : pointMaximalIdeal c := ⟨selectedLocalCoordinate i hI H d F eI eH j₀ h₀ q,
    selectedLocalCoordinate_mem_maximalIdeal i hI H d F eI eH j₀ h₀ q hz⟩
  let s := selectedLocalIdealCoordinate i hI H d F eI eH j₀ h₀ q hz
  have h := conormalCoefficientMap_apply_of_section b j (pointMaximalIdeal c)
    (pointResidueHom c) (ker_pointResidueHom c)
    (localExceptional_snd c F.toImage i (toSpec k (ULift.{u} (Fin 2)))
      (F.exceptional_toImage_eq eI eH j₀ h₀).symm)
    (selectedLocalConormalIso i hI H d F eI eH hn2 j₀ h₀) r s
    (selectedLocalIdealCoordinate_inclusion i hI H d F eI eH j₀ h₀ q hz)
  change selectedLocalConormalMap i hI H d F eI eH hn2 j₀ h₀ r = _
  refine h.trans ?_
  rw [selectedLocalIdealCoordinate_firstOrder i hI H d F eI eH hn2 j₀ h₀ a t ht q hq]
  exact (exceptionalCoordinateBasis_apply k a).symm

end OriginalSelectedConormalCoefficients

section OriginalNonprincipalIdeal

private theorem not_isPrincipal_of_two_basis_images
    {R k V : Type u} [CommRing R] [Field k] [AddCommGroup V] [Module k V]
    (I : Ideal R) (β : R →+* k) (σ : I →ₛₗ[β] V)
    (b : Module.Basis (ULift.{u} (Fin 2)) k V)
    (x : ULift.{u} (Fin 2) → I) (hx : ∀ a, σ (x a) = b a) : ¬ I.IsPrincipal := by
  intro hI
  let _ : I.IsPrincipal := hI
  obtain ⟨g, hg⟩ := Submodule.IsPrincipal.principal I
  have hgI : g ∈ I := by
    rw [hg]
    exact Submodule.mem_span_singleton_self g
  let t : I := ⟨g, hgI⟩
  have hm : ∀ j, ∃ a : R, a • g = (x j).val := by
    intro j
    apply Submodule.mem_span_singleton.mp
    rw [← hg]
    exact (x j).property
  choose a ha using hm
  have ht (j : ULift.{u} (Fin 2)) : a j • t = x j := Subtype.ext (ha j)
  have hb (j : ULift.{u} (Fin 2)) : β (a j) • σ t = b j :=
    (σ.map_smulₛₗ (a j) t).symm.trans ((congrArg σ (ht j)).trans (hx j))
  have ha₀ : β (a ⟨0⟩) ≠ 0 := by
    intro h
    have h₀ := hb ⟨0⟩
    rw [h, zero_smul] at h₀
    exact b.ne_zero ⟨0⟩ h₀.symm
  have h₀ : β (a ⟨0⟩) * (b.repr (σ t)) ⟨1⟩ = 0 := by
    simpa using congrArg (fun v => b.repr v ⟨1⟩) (hb ⟨0⟩)
  have hz : (b.repr (σ t)) ⟨1⟩ = 0 := (mul_eq_zero.mp h₀).resolve_left ha₀
  have h₁ : β (a ⟨1⟩) * (b.repr (σ t)) ⟨1⟩ = 1 := by
    simpa using congrArg (fun v => b.repr v ⟨1⟩) (hb ⟨1⟩)
  rw [hz, mul_zero] at h₁
  exact zero_ne_one h₁

open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules.Invertible

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}}
  {p : X ⟶ ProjectiveSpace A ι} {k : Type u} [Field k]
  (i : ProjectiveSpace k (ULift.{u} (Fin 2)) ⟶ X) [IsClosedImmersion i]
  (hI : IsLocallyRankOne X (Hom.idealModule i)) (H : LineBundle X)
  {eP : H.val ≅ (Scheme.Modules.pullback p).obj (twistingSheaf A ι 1)} (d : ℕ)
  {n : ℕ} {hn : 1 ≤ n}
  (F : CartierProjectivePresentation p i hI H eP d n hn)
  (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
    twistingSheaf k (ULift.{u} (Fin 2)) 1)
  (eH : (Scheme.Modules.pullback i).obj H.val ≅
    twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual image-local maximal ideal is not principal: the original two
first-order images are the original degree-one basis over the full residue field.
This conclusion uses no dimension, normality or regularity of the image. -/
theorem selectedLocalMaximalIdeal_not_isPrincipal
    [QuasiCompact F.toImage] [QuasiSeparated F.toImage]
    (hn2 : 2 ≤ n * d) (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀)))
    [IsClosedImmersion (F.residueToImage eI eH j₀ h₀)]
    (t : ULift.{u} (Fin 2) → (SheafOfModules.unit X.ringCatSheaf ⟶
      (cartierPowerTwist i hI H n (n * d - 2 + 1)).val))
    (ht : ∀ a, t a ≫ (cartierStepSequence i hI
      (cartierPowerTwist i hI H n (n * d - 2))).g =
        firstOrderQuotientCoordinate i hI H d eI eH n hn2 a)
    (q : ULift.{u} (Fin 2) → F.index)
    (hq : ∀ a, F.sections (q a) = firstOrderCartierImage i hI H d n hn2 (t a)) :
    ¬ (pointMaximalIdeal (F.residueToImage eI eH j₀ h₀)).IsPrincipal := by
  let := Module.compHom Γ(twistingSheaf k (ULift.{u} (Fin 2)) 1, ⊤)
    (affineFormalFunctionsScalar (toSpec k (ULift.{u} (Fin 2))))
  let c := F.residueToImage eI eH j₀ h₀
  let hz : ∀ a : ULift.{u} (Fin 2),
      cartierResidueCoefficient i hI H d eI eH n (F.sections (q a)) = 0 :=
    fun a => (congrArg (cartierResidueCoefficient i hI H d eI eH n) (hq a)).trans
      (firstOrderCartierImage_residueCoefficient i hI H d eI eH n hn2 (t a))
  let x : ULift.{u} (Fin 2) → pointMaximalIdeal c := fun a =>
    ⟨selectedLocalCoordinate i hI H d F eI eH j₀ h₀ (q a),
      selectedLocalCoordinate_mem_maximalIdeal i hI H d F eI eH j₀ h₀ (q a) (hz a)⟩
  exact not_isPrincipal_of_two_basis_images (pointMaximalIdeal c) (pointResidueHom c)
    (selectedLocalConormalMap i hI H d F eI eH hn2 j₀ h₀)
    (exceptionalCoordinateBasis k) x
    (fun a => selectedLocalConormalMap_coordinate i hI H d F eI eH hn2 j₀ h₀ a (t a)
      (ht a) (q a) (hq a))

end OriginalNonprincipalIdeal

end AlgebraicGeometry.Scheme.Surfaces.Contraction.FormalNeighborhood
