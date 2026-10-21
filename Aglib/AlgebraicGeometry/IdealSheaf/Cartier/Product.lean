/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.Cartier.Interfaces
public import Aglib.AlgebraicGeometry.IdealSheaf.Invertible.Affine
public import Aglib.AlgebraicGeometry.IdealSheaf.LocallyClosed
public import Aglib.AlgebraicGeometry.Modules.Invertible.Affine
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Tensor.Exact
public import Aglib.AlgebraicGeometry.Modules.Tensor.Sections
public import Aglib.RingTheory.Ideal.RegularPrincipal.Intersection

/-!
# Products of actual Cartier ideals

The existing multiplication of kernel inclusions factors canonically through the
kernel module of the native product ideal. Its factor is always an epimorphism.
If the first ideal is locally rank one, exact tensoring makes it a monomorphism
and hence an isomorphism. The second ideal may be an arbitrary closed ideal.

If the actual intersection on the second closed subscheme is Cartier, its
regular local generator also proves equality of the product and intersection
ideal-sheaf data.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open Scheme.Modules Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X C D : Scheme.{u}}

private theorem section_eq_of_affine_restrictions (N : X.Modules) (U : X.Opens)
    (s t : N.val.obj (op U))
    (h : ∀ (V : X.Opens) (_ : IsAffineOpen V) (hVU : V ≤ U),
      N.val.map (homOfLE hVU).op s = N.val.map (homOfLE hVU).op t) : s = t := by
  have hc : Presheaf.equalizerSieve (F := N.val.presheaf) s t ∈
      (Opens.grothendieckTopology X) U := by
    intro x hxU
    obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hxU
    exact ⟨V, homOfLE hVU, h V hV hVU, hxV⟩
  apply N.isSheaf.isSeparated U _ hc
  intro V q hq
  exact hq

/-- The original Cartier multiplication sends the original pure tensor to the
product of its two actual kernel inclusions. -/
theorem idealMultiplication_section (i : C ⟶ X) (j : D ⟶ X) (U : X.Opens)
    (m : (idealModule i).val.obj (op U)) (n : (idealModule j).val.obj (op U)) :
    (Cartier.idealMultiplication i j).val.app (op U)
      (moduleTensorSection X (idealModule i) (idealModule j) U m n) =
        (show Γ(X, U) from (idealInclusion i).val.app (op U) m) *
          (show Γ(X, U) from (idealInclusion j).val.app (op U) n) := by
  change (tensorSheafLeftUnit X (SheafOfModules.unit X.ringCatSheaf)).hom.val.app (op U)
    ((tensorSheafMap X (idealInclusion i) (idealInclusion j)).val.app (op U)
      ((tensorSheafUnit X (idealModule i) (idealModule j)).app (op U) (m ⊗ₜ n))) = _
  rw [tensorSheafMap_tmul]
  exact tensorLeftUnitIso_hom_section X (SheafOfModules.unit X.ringCatSheaf) U _ _

/-- The original multiplication vanishes on the subscheme of the native product ideal. -/
theorem idealMultiplication_structureMap (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    Cartier.idealMultiplication i j ≫ structureModuleMap (i.ker * j.ker).subschemeι = 0 := by
  let k := (i.ker * j.ker).subschemeι
  let N := (Scheme.Modules.pushforward k).obj (SheafOfModules.unit _)
  apply moduleTensor_hom_ext
  intro U m n
  change ((Cartier.idealMultiplication i j ≫ structureModuleMap k).val.app (op U))
    (moduleTensorSection X (idealModule i) (idealModule j) U m n) = 0
  apply section_eq_of_affine_restrictions N U _ 0
  intro V hV hVU
  rw [map_zero, ← PresheafOfModules.naturality_apply]
  have hres : (tensorSheaf X (idealModule i) (idealModule j)).val.map (homOfLE hVU).op
      (moduleTensorSection X (idealModule i) (idealModule j) U m n) =
    moduleTensorSection X (idealModule i) (idealModule j) V
      ((idealModule i).val.map (homOfLE hVU).op m)
      ((idealModule j).val.map (homOfLE hVU).op n) :=
    moduleTensorSection_restrict (idealModule i) (idealModule j) (homOfLE hVU) m n
  rw [hres]
  change (k.app V).hom ((Cartier.idealMultiplication i j).val.app (op V)
    (moduleTensorSection X (idealModule i) (idealModule j) V
      ((idealModule i).val.map (homOfLE hVU).op m)
      ((idealModule j).val.map (homOfLE hVU).op n))) = 0
  rw [idealMultiplication_section]
  apply RingHom.mem_ker.mp
  rw [(i.ker * j.ker).ker_subschemeι_app ⟨V, hV⟩]
  change _ ∈ i.ker.ideal ⟨V, hV⟩ * j.ker.ideal ⟨V, hV⟩
  rw [i.ker_apply ⟨V, hV⟩, j.ker_apply ⟨V, hV⟩]
  apply Ideal.mul_mem_mul
  · rw [← idealSectionsEquiv_val]
    exact (idealSectionsEquiv i V _).property
  · rw [← idealSectionsEquiv_val]
    exact (idealSectionsEquiv j V _).property

/-- The factor of the existing actual multiplication through the actual kernel
of the native product ideal. -/
def idealProductMap (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    tensorSheaf X (idealModule i) (idealModule j) ⟶
      idealModule (i.ker * j.ker).subschemeι :=
  kernel.lift (structureModuleMap (i.ker * j.ker).subschemeι)
    (Cartier.idealMultiplication i j) (idealMultiplication_structureMap i j)

@[reassoc (attr := simp)]
theorem idealProductMap_inclusion (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    idealProductMap i j ≫ idealInclusion (i.ker * j.ker).subschemeι =
      Cartier.idealMultiplication i j := kernel.lift_ι _ _ _

/-- On every affine open, actual tensor sections surject onto the actual product
ideal sections. No local freeness is needed for this surjectivity. -/
theorem idealProductMap_app_surjective (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Surjective ((idealProductMap i j).val.app (op U)) := by
  let k := (i.ker * j.ker).subschemeι
  have hm : ∀ z : Γ(X, U), z ∈ i.ker.ideal ⟨U, hU⟩ * j.ker.ideal ⟨U, hU⟩ →
      ∃ s : (tensorSheaf X (idealModule i) (idealModule j)).val.obj (op U),
        (Cartier.idealMultiplication i j).val.app (op U) s = z := by
    intro z hz
    refine Submodule.mul_induction_on hz ?_ ?_
    · intro a ha b hb
      have ha' : a ∈ RingHom.ker (i.app U).hom := by
        rwa [i.ker_apply ⟨U, hU⟩] at ha
      have hb' : b ∈ RingHom.ker (j.app U).hom := by
        rwa [j.ker_apply ⟨U, hU⟩] at hb
      refine ⟨moduleTensorSection X (idealModule i) (idealModule j) U
        ((idealSectionsEquiv i U).symm ⟨a, ha'⟩)
        ((idealSectionsEquiv j U).symm ⟨b, hb'⟩), ?_⟩
      rw [idealMultiplication_section, ← idealSectionsEquiv_val,
        ← idealSectionsEquiv_val]
      simp only [LinearEquiv.apply_symm_apply]
    · intro a b ha hb
      obtain ⟨s, hs⟩ := ha
      obtain ⟨t, ht⟩ := hb
      exact ⟨s + t, by rw [map_add, hs, ht]⟩
  intro t
  have ht : (idealSectionsEquiv k U t).val ∈
      i.ker.ideal ⟨U, hU⟩ * j.ker.ideal ⟨U, hU⟩ := by
    exact ((i.ker * j.ker).ker_subschemeι_app ⟨U, hU⟩).le
      (idealSectionsEquiv k U t).property
  obtain ⟨s, hs⟩ := hm _ ht
  refine ⟨s, ?_⟩
  apply (idealSectionsEquiv k U).injective
  apply Subtype.ext
  rw [idealSectionsEquiv_val]
  exact (congrArg (fun q ↦ q.val.app (op U) s) (idealProductMap_inclusion i j)).trans hs

/-- The canonical product comparison is always an epimorphism for actual closed ideals. -/
instance idealProductMap_epi (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] : Epi (idealProductMap i j) := by
  constructor
  intro N g h hgh
  apply Scheme.Modules.hom_ext
  intro U
  ext t
  apply section_eq_of_affine_restrictions N U _ _
  intro V hV hVU
  change N.val.map (homOfLE hVU).op (g.val.app (op U) t) =
    N.val.map (homOfLE hVU).op (h.val.app (op U) t)
  rw [← PresheafOfModules.naturality_apply, ← PresheafOfModules.naturality_apply]
  obtain ⟨s, hs⟩ := idealProductMap_app_surjective i j V hV
    ((idealModule (i.ker * j.ker).subschemeι).val.map (homOfLE hVU).op t)
  rw [← hs]
  exact congrArg (fun q ↦ q.val.app (op V) s) hgh

/-- Tensoring an actual Cartier ideal inclusion with any actual ideal inclusion
gives a monomorphism into the structure sheaf. -/
theorem idealMultiplication_mono (i : C ⟶ X) (j : D ⟶ X)
    (hI : IsLocallyRankOne X (idealModule i)) : Mono (Cartier.idealMultiplication i j) := by
  change @Mono X.Modules _ (tensorSheaf X (idealModule i) (idealModule j))
    (SheafOfModules.unit X.ringCatSheaf) (Cartier.idealMultiplication i j)
  have : IsFiniteLocallyFree X (idealModule i) := isFiniteLocallyFree_of_isLocallyRankOne hI
  let F := moduleTensorLeftFunctor X (idealModule i)
  have : PreservesFiniteLimits F := Functor.preservesFiniteLimits_of_preservesHomology F
  let ρ : (show X.Modules from tensorSheaf X (idealModule i)
      (SheafOfModules.unit X.ringCatSheaf)) ⟶ idealModule i :=
    (SheafOfModulesOfCommRing.tensorRightUnitIso X.sheaf).hom.app (idealModule i)
  have he : Cartier.idealMultiplication i j = F.map (idealInclusion j) ≫ ρ ≫
      idealInclusion i := by
    apply moduleTensor_hom_ext
    intro U m n
    change (Cartier.idealMultiplication i j).val.app (op U)
      (moduleTensorSection X (idealModule i) (idealModule j) U m n) =
        (idealInclusion i).val.app (op U)
      (ρ.val.app (op U) ((F.map (idealInclusion j)).val.app (op U)
        (moduleTensorSection X (idealModule i) (idealModule j) U m n)))
    rw [idealMultiplication_section]
    have hs : (F.map (idealInclusion j)).val.app (op U)
        (moduleTensorSection X (idealModule i) (idealModule j) U m n) =
      moduleTensorSection X (idealModule i) (SheafOfModules.unit X.ringCatSheaf) U m
        ((idealInclusion j).val.app (op U) n) :=
      moduleTensorLeftFunctor_map_section (idealModule i) (idealInclusion j) U m n
    have hunit : ρ.val.app (op U)
        (moduleTensorSection X (idealModule i) (SheafOfModules.unit X.ringCatSheaf) U m
          ((idealInclusion j).val.app (op U) n)) =
      (show Γ(X, U) from (idealInclusion j).val.app (op U) n) • m :=
      tensorRightUnitIso_hom_section X (idealModule i) U m _
    rw [hs, hunit]
    have hlinear := ((idealInclusion i).val.app (op U)).hom.map_smul
      (show Γ(X, U) from (idealInclusion j).val.app (op U) n) m
    exact (mul_comm
      (show Γ(X, U) from (idealInclusion i).val.app (op U) m)
      (show Γ(X, U) from (idealInclusion j).val.app (op U) n)).trans hlinear.symm
  have : Mono (F.map (idealInclusion j)) := inferInstance
  have : IsIso ρ := inferInstanceAs
    (IsIso ((SheafOfModulesOfCommRing.tensorRightUnitIso X.sheaf).hom.app (idealModule i)))
  rw [he]
  infer_instance

/-- One Cartier factor suffices for the canonical tensor-to-product comparison. -/
theorem idealProductMap_isIso (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (hI : IsLocallyRankOne X (idealModule i)) : IsIso (idealProductMap i j) := by
  have : Mono (Cartier.idealMultiplication i j) := idealMultiplication_mono i j hI
  have : Mono (idealProductMap i j ≫ idealInclusion (i.ker * j.ker).subschemeι) := by
    rw [idealProductMap_inclusion]
    infer_instance
  have : Mono (idealProductMap i j) := mono_of_mono _ (idealInclusion _)
  exact isIso_of_mono_of_epi (idealProductMap i j)

/-- The intrinsic product isomorphism for a Cartier ideal and an arbitrary closed ideal. -/
def idealProductIso (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (hI : IsLocallyRankOne X (idealModule i)) :
    tensorSheaf X (idealModule i) (idealModule j) ≅
      idealModule (i.ker * j.ker).subschemeι := by
  have := idealProductMap_isIso i j hI
  exact asIso (idealProductMap i j)

@[reassoc (attr := simp)]
theorem idealProductIso_hom_inclusion (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (hI : IsLocallyRankOne X (idealModule i)) :
    (idealProductIso i j hI).hom ≫ idealInclusion (i.ker * j.ker).subschemeι =
      Cartier.idealMultiplication i j := idealProductMap_inclusion i j

/-- The product of a Cartier ideal with a closed ideal equals their intersection
if the actual intersection ideal on the second closed subscheme is Cartier.
Local rank one of the second ideal on the ambient scheme is not needed. -/
theorem ideal_mul_eq_inf_of_cartier_intersection (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (hI : IsLocallyRankOne X (idealModule i))
    (hK : IsLocallyRankOne D (idealModule (pullback.snd i j))) :
    i.ker * j.ker = i.ker ⊓ j.ker := by
  classical
  let k := pullback.snd i j
  have hker : k.ker = i.ker.comap j := by
    rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion i j,
      ← Hom.ker_comp_of_isIso (pullbackSymmetry i j).hom (pullback.fst j i)]
    simp [k]
  have hlocal : ∀ x : X, ∃ (U : X.Opens) (hU : IsAffineOpen U), x ∈ U ∧
      i.ker.ideal ⟨U, hU⟩ * j.ker.ideal ⟨U, hU⟩ =
        i.ker.ideal ⟨U, hU⟩ ⊓ j.ker.ideal ⟨U, hU⟩ := by
    intro x
    by_cases hx : x ∈ Set.range j
    · obtain ⟨d, rfl⟩ := hx
      obtain ⟨V, hdV, ⟨eI⟩⟩ :=
        (isLocallyRankOne_iff_local_unit X (idealModule i)).mp hI (j d)
      obtain ⟨W, hdW, ⟨eK⟩⟩ :=
        (isLocallyRankOne_iff_local_unit D (idealModule k)).mp hK d
      obtain ⟨T, hT, hpre⟩ := j.isClosedEmbedding.isInducing.isOpen_iff.mp W.isOpen
      have hdT : j d ∈ T := by
        change d ∈ j ⁻¹' T
        rw [hpre]
        exact hdW
      let O : X.Opens := V ⊓ ⟨T, hT⟩
      obtain ⟨U, hU, hdU, hUO⟩ := exists_isAffineOpen_mem_and_subset
        (show j d ∈ O from ⟨hdV, hdT⟩)
      have hUV : U ≤ V := hUO.trans inf_le_left
      have hUW : j ⁻¹ᵁ U ≤ W := by
        intro z hz
        change z ∈ (W : Set D)
        rw [← hpre]
        exact (hUO hz).2
      obtain ⟨a, _ha, hIa⟩ := Ideal.ideal_exists_regular_generator _
        (idealKernelEquivOfLocalUnit i V U hUV eI)
      have hDU : IsAffineOpen (j ⁻¹ᵁ U) := hU.preimage j
      have hKa : RingHom.ker (k.app (j ⁻¹ᵁ U)).hom = Ideal.span {j.app U a} := by
        rw [← k.ker_apply ⟨j ⁻¹ᵁ U, hDU⟩, hker,
          Scheme.IdealSheafData.ideal_comap_eq_map_appLE i.ker j
            ⟨U, hU⟩ ⟨j ⁻¹ᵁ U, hDU⟩ le_rfl,
          i.ker_apply ⟨U, hU⟩, hIa, Ideal.map_span, Set.image_singleton,
          Scheme.Hom.appLE_eq_app]
      have hregular : IsSMulRegular Γ(D, j ⁻¹ᵁ U) (j.app U a) :=
        Ideal.isSMulRegular_generator_of_linearEquiv _
          (idealKernelEquivOfLocalUnit k W (j ⁻¹ᵁ U) hUW eK) _ hKa
      refine ⟨U, hU, hdU, ?_⟩
      rw [i.ker_apply ⟨U, hU⟩, j.ker_apply ⟨U, hU⟩]
      exact Ideal.mul_ker_eq_inf_of_regular_image (j.app U).hom _ a hIa hregular
    · let W : X.Opens :=
        ⟨(Set.range j)ᶜ, j.isClosedEmbedding.isClosed_range.isOpen_compl⟩
      obtain ⟨U, hU, hxU, hUW⟩ := exists_isAffineOpen_mem_and_subset
        (show x ∈ W from hx)
      have hJtop : j.ker.ideal ⟨U, hU⟩ = ⊤ := by
        by_contra hne
        obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal (j.ker.ideal ⟨U, hU⟩) hne
        let p : PrimeSpectrum Γ(X, U) := ⟨P, hP.isPrime⟩
        have hp := (j.ker.fromSpec_mem_support_iff ⟨U, hU⟩ p).mpr hIP
        change hU.fromSpec p ∈ (j.ker.support : Set X) at hp
        rw [Hom.support_ker, j.isClosedEmbedding.isClosed_range.closure_eq] at hp
        exact hUW (hU.range_fromSpec.subset ⟨p, rfl⟩) hp
      refine ⟨U, hU, hxU, ?_⟩
      rw [hJtop]
      simp only [Ideal.mul_top, inf_top_eq]
  choose U hU hxU hmul using hlocal
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top (fun x ↦ ⟨U x, hU x⟩)
  · apply top_le_iff.mp
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hxU x⟩
  · intro x
    exact hmul x

namespace Cartier

/-- The exact intrinsic tensor/product family, with its original inclusion triangle. -/
theorem cartierIdealTensorProduct : CartierIdealTensorProduct.{u} := by
  intro X C D i j hi hj hI _hJ
  let := hi
  let := hj
  exact ⟨idealProductIso i j hI, idealProductIso_hom_inclusion i j hI⟩

/-- The exact product-equals-union family, retaining Cartierness of the actual
intersection on the second divisor. -/
theorem cartierSumIdealEqualsUnion : CartierSumIdealEqualsUnion.{u} := by
  intro X C D i j hi hj hI _hJ hK
  let := hi
  let := hj
  exact ideal_mul_eq_inf_of_cartier_intersection i j hI hK

end Cartier
end AlgebraicGeometry.Scheme.Hom
