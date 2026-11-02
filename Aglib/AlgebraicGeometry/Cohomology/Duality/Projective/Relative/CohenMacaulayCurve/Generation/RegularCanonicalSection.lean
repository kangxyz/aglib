/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.CohenMacaulayCurve.Generation
public import Aglib.AlgebraicGeometry.Cohomology.ClosedImmersion.RightAdjoint.Cartier.Purity
public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.Locality
public import Aglib.AlgebraicGeometry.Modules.Coherent.Subobjects
public import Aglib.AlgebraicGeometry.Modules.Tensor.Monoidal.Sections
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# The original Cartier section is regular on the coefficient canonical module

The kernel is annihilated by the original Cartier ideal. A finite Cartier
zero scheme gives actual finite closed support, and coefficient purity kills
the kernel. All section and quotient maps are the original Cartier maps.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory Opposite TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory

private theorem idealTensorZero_of_sectionZero
    {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C]
    [HasZeroMorphisms C] (I L P : C)
    (τ : 𝟭 C ⟶ tensorLeft L)
    (htensor : ∀ A B : C, τ.app (A ⊗ B) ≫ (α_ L A B).inv = τ.app A ▷ B)
    (e : L ⊗ I ≅ 𝟙_ C) (i : I ⟶ 𝟙_ C) (hev : τ.app I ≫ e.hom = i)
    (hzero : ∀ A B N : C, (0 : A ⟶ B) ▷ N = 0)
    (hτ : τ.app P = 0) : i ▷ P = 0 := by
  have hright : τ.app (P ⊗ I) = 0 := by
    apply (cancel_mono (α_ L P I).inv).mp
    rw [zero_comp, htensor, hτ, hzero]
  have hleft : τ.app (I ⊗ P) = 0 := by
    apply (cancel_mono ((tensorLeft L).map (β_ I P).hom)).mp
    rw [zero_comp, ← τ.naturality (β_ I P).hom, hright, comp_zero]
  rw [← hev, comp_whiskerRight, ← htensor I P, hleft, zero_comp, zero_comp]

namespace AlgebraicGeometry.Scheme.Modules

/-- Vanishing of the original ideal coefficient map means actual affine
annihilation by the original scheme-map kernel ideal. -/
theorem killedByIdealSheaf_of_idealInclusion_tensor_eq_zero
    {D X : Scheme.{u}} (i : D ⟶ X) (M : X.Modules)
    (h : idealInclusion i ▷ M = 0) : killedByIdealSheaf i.ker M := by
  intro U a ha m
  let aI : Γ(idealModule i, U.1) :=
    (idealSectionsEquiv i U.1).symm ⟨a, i.ideal_ker_le U ha⟩
  have haI : (idealInclusion i).val.app (op U.1) aI = a := by
    rw [← idealSectionsEquiv_val]
    exact congrArg Subtype.val ((idealSectionsEquiv i U.1).apply_symm_apply _)
  have hz := congrArg (fun f : idealModule i ⊗ M ⟶
      SheafOfModules.unit X.ringCatSheaf ⊗ M =>
    f.val.app (op U.1) (moduleTensorSection X (idealModule i) M U.1 aI m)) h
  rw [whiskerRight_moduleTensorSection, haI] at hz
  change moduleTensorSection X (SheafOfModules.unit X.ringCatSheaf) M U.1 a m = 0 at hz
  have hu := congrArg
    (fun z => ((SheafOfModulesOfCommRing.tensorLeftUnitIso X.sheaf).hom.app M).val.app
      (op U.1) z) hz
  rw [tensorLeftUnitIso_hom_section, map_zero] at hu
  exact hu

/-- The kernel of the original Cartier tensor section is killed by the
original Cartier ideal, without a regularity or purity hypothesis on M. -/
theorem cartierTensorSection_kernel_killed
    {D X : Scheme.{u}} (i : D ⟶ X)
    (hI : IsLocallyRankOne X (idealModule i)) (M : X.Modules) :
    killedByIdealSheaf i.ker (kernel ((cartierTensorSection i).app M)) := by
  let I : X.Modules := idealModule i
  let L : X.Modules := dualSheaf X I
  let τ : 𝟭 X.Modules ⟶ tensorLeft L := cartierTensorSection i
  let K := kernel (τ.app M)
  let E := lineBundleDualTensorEquivalence X ⟨I, hI⟩
  have : E.functor.IsEquivalence := Equivalence.isEquivalence_functor E
  have : Mono ((tensorLeft L).map (kernel.ι (τ.app M))) :=
    inferInstanceAs (Mono (E.functor.map (kernel.ι (τ.app M))))
  have hτ : τ.app K = 0 := by
    apply (cancel_mono ((tensorLeft L).map (kernel.ι (τ.app M)))).mp
    rw [zero_comp, ← τ.naturality]
    exact kernel.condition (τ.app M)
  have hz : idealInclusion i ▷ K = 0 :=
    idealTensorZero_of_sectionZero I L K τ
      (fun A B => positiveCartierTensorSection_tensor X L A B (cartierDualIdealSection i))
      (dualEvaluationIso X ⟨I, hI⟩) (idealInclusion i)
      (cartierTensorSection_evaluation i hI)
      (fun A B N => (moduleTensorRightFunctor X N).map_zero A B) hτ
  exact killedByIdealSheaf_of_idealInclusion_tensor_eq_zero i K hz

/-- The original Cartier section pulls back to zero on its original closed
zero scheme. This is the original row-unit equation under the original
pullback/pushforward adjunction, without any section-coordinate replacement. -/
theorem pullback_cartierTensorSection_eq_zero
    {D X : Scheme.{u}} (i : D ⟶ X) [IsClosedImmersion i]
    (hI : IsLocallyRankOne X (idealModule i)) (M : X.Modules) :
    (pullback i).map ((cartierTensorSection i).app M) = 0 := by
  let N := tensorSheaf X (dualSheaf X (idealModule i)) M
  let b : M ⟶ N := (cartierTensorSection i).app M
  change (pullback i).map b = 0
  let adj := pullbackPushforwardAdjunction i
  apply (adj.homEquiv M ((pullback i).obj N)).injective
  rw [Adjunction.homAddEquiv_zero]
  calc
    adj.homEquiv M ((pullback i).obj N)
        ((pullback i).map b) =
        b ≫ adj.unit.app N := by
      simpa only [Category.comp_id, Adjunction.homEquiv_id] using
        adj.homEquiv_naturality_left b
          (𝟙 ((pullback i).obj N))
    _ = 0 := cartierCoefficientSequence_zero i hI M

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Cohomology.CanonicalEnlargement

/-- Actual annihilation by a closed ideal with finite field-valued zero scheme
gives finite closed support of the original module, without coherence. -/
theorem finiteClosedSupport_of_killed_finite
    (k : Type u) [Field k] {D X : Scheme.{u}} (i : D ⟶ X) [IsClosedImmersion i]
    (p : X ⟶ Spec (.of k)) [IsFinite (i ≫ p)]
    (M : X.Modules) (hM : killedByIdealSheaf i.ker M) : HasFiniteClosedSupport M := by
  classical
  let : IsLocallyArtinian D := IsLocallyArtinian.of_locallyQuasiFinite (i ≫ p)
  let : CompactSpace D := QuasiCompact.compactSpace_of_compactSpace (i ≫ p)
  let : Finite D := finite_of_compact_of_discrete
  let : Fintype D := Fintype.ofFinite D
  let e := (Fintype.equivFin D).symm
  refine ⟨Fintype.card D, fun a => i (e a),
    i.isClosedEmbedding.injective.comp e.injective, ?_, ?_⟩
  · intro a
    simpa only [Set.image_singleton] using
      i.isClosedEmbedding.isClosedMap {e a} isClosed_singleton
  · intro x hx
    have hnot : x ∉ i.ker.support := by
      change x ∉ (i.ker.support : Set X)
      rw [Scheme.Hom.support_ker, i.isClosedEmbedding.isClosed_range.closure_eq]
      rintro ⟨d, rfl⟩
      exact hx ⟨e.symm d, congrArg i (e.apply_symm_apply d)⟩
    have hz := killedByIdealSheaf_isZero_stalk_of_not_mem_support i.ker M hM x hnot
    rw [AddCommGrpCat.isZero_iff_subsingleton]
    exact (ModuleCat.isZero_iff_subsingleton).mp hz

/-- Every original pushforward from a finite closed field scheme has finite
closed support, regardless of coherence of the pushed module. -/
theorem finiteClosedSupport_pushforward_finite
    (k : Type u) [Field k] {D X : Scheme.{u}} (i : D ⟶ X) [IsClosedImmersion i]
    (p : X ⟶ Spec (.of k)) [IsFinite (i ≫ p)] (M : D.Modules) :
    HasFiniteClosedSupport ((pushforward i).obj M) :=
  finiteClosedSupport_of_killed_finite k i p _ (killedByIdealSheaf_pushforward_ker i M)

/-- The original Cartier row is short exact and has finite closed support
in its literal third object. The complete row comparison is formed before
specializing its coefficient module. -/
theorem cartierCoefficientSequence_shortExact_finiteClosedSupport
    (k : Type u) [Field k] {D X : Scheme.{u}} (i : D ⟶ X) [IsClosedImmersion i]
    (p : X ⟶ Spec (.of k)) [IsFinite (i ≫ p)]
    (hI : IsLocallyRankOne X (idealModule i)) (M : X.Modules)
    [Mono ((cartierTensorSection i).app M)] :
    (cartierCoefficientSequence i hI M).ShortExact ∧
      HasFiniteClosedSupport (cartierCoefficientSequence i hI M).X₃ := by
  refine ⟨cartierCoefficientSequence_shortExact i hI M, ?_⟩
  dsimp only [cartierCoefficientSequence, CategoryTheory.Functor.comp_obj]
  exact finiteClosedSupport_pushforward_finite k i p
    ((Scheme.Modules.pullback i).obj (tensorSheaf X (dualSheaf X (idealModule i)) M))

end AlgebraicGeometry.Scheme.Cohomology.CanonicalEnlargement

namespace AlgebraicGeometry.Scheme.Cohomology

variable (k : Type u) [Field k] (ι : Type u)
    {C : Scheme.{u}} (j : C ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    (V : ModuleCat.{u} k) [Module.Finite k V] (hV : Module.finrank k V = 1)
    (hCM : ∀ x : C, IsClosed ({x} : Set C) →
      ∃ b ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk x),
        IsSMulRegular (C.presheaf.stalk x) b ∧
          (Ideal.span {b}).radical = IsLocalRing.maximalIdeal (C.presheaf.stalk x))
    (hn : 1 ≤ n)

include e hV hCM hn in
/-- The actual Cartier section is monic on the coefficient canonical module,
even for the full nonreduced curve and an arbitrary ground field. -/
theorem cmCurveCoefficientCanonical_cartierTensorSection_mono
    {D : Scheme.{u}} (i : D ⟶ C) [IsClosedImmersion i]
    (hI : IsLocallyRankOne C (idealModule i))
    [IsFinite (i ≫ (j ≫ ProjectiveSpace.toSpec k ι))] :
    Mono ((cartierTensorSection i).app (cmCurveCoefficientCanonicalModule k ι j n V)) := by
  let W : C.Modules := cmCurveCoefficientCanonicalModule k ι j n V
  let K := kernel ((cartierTensorSection i).app W)
  let : Finite ι := Finite.of_equiv _ e.symm
  let : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian
    (j ≫ ProjectiveSpace.toSpec k ι)
  let : W.IsFinitePresentation :=
    cmCurveCoefficientCanonicalModule_finitePresentation k ι j n e V
  have hW : affineLocallyFiniteType C W := affineLocallyFiniteType_of_finitePresentation W
  let : W.IsQuasicoherent := quasicoherent_of_affineLocallyFiniteType hW
  let L := dualLineBundle C ⟨idealModule i, hI⟩
  let : L.val.IsFinitePresentation := lineBundle_isFinitePresentation C L
  have hL : affineLocallyFiniteType C L.val := affineLocallyFiniteType_of_finitePresentation L.val
  let : (L.val ⊗ W).IsQuasicoherent :=
    quasicoherent_of_affineLocallyFiniteType (affineLocallyFiniteType_tensor L.val W hL hW)
  let b : W ⟶ L.val ⊗ W := (cartierTensorSection i).app W
  let : K.IsQuasicoherent := quasicoherent_kernel b
  have hK : affineLocallyFiniteType C K :=
    Coherent.affineLocallyFiniteType_of_quasicoherent_mono (kernel.ι b) hW
  have hs : CanonicalEnlargement.HasFiniteClosedSupport K :=
    CanonicalEnlargement.finiteClosedSupport_of_killed_finite k i
      (j ≫ ProjectiveSpace.toSpec k ι) K (cartierTensorSection_kernel_killed i hI W)
  exact Preadditive.mono_of_isZero_kernel _
    (cmCurveCoefficientCanonical_no_finiteSupport_subobject k ι j n e V hV hCM hn
      K hK hs (kernel.ι b))

include e hV hCM hn in
/-- The original positive Cartier coefficient row is short exact, and its
literal pushforward quotient has actual finite closed support. -/
theorem cmCurveCoefficientCanonical_cartierCoefficientSequence
    {D : Scheme.{u}} (i : D ⟶ C) [IsClosedImmersion i]
    (hI : IsLocallyRankOne C (idealModule i))
    [IsFinite (i ≫ (j ≫ ProjectiveSpace.toSpec k ι))] :
    let W : C.Modules := cmCurveCoefficientCanonicalModule k ι j n V
    (cartierCoefficientSequence i hI W).ShortExact ∧
      CanonicalEnlargement.HasFiniteClosedSupport (cartierCoefficientSequence i hI W).X₃ := by
  let W : C.Modules := cmCurveCoefficientCanonicalModule k ι j n V
  let : Mono ((cartierTensorSection i).app W) :=
    cmCurveCoefficientCanonical_cartierTensorSection_mono k ι j n e V hV hCM hn i hI
  exact CanonicalEnlargement.cartierCoefficientSequence_shortExact_finiteClosedSupport
    k i (j ≫ ProjectiveSpace.toSpec k ι) hI W

end AlgebraicGeometry.Scheme.Cohomology
