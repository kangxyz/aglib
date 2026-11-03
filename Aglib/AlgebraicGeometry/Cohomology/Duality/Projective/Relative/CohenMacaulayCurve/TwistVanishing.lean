/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.CohenMacaulayCurve.Generation
public import Aglib.AlgebraicGeometry.Modules.Tensor.Basic
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.EqualRank
public import Aglib.AlgebraicGeometry.Modules.Invertible.RankOne
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction

/-!
# Vanishing for genuine canonical enlargement rows

A pure coherent enlargement of the coefficient-valued canonical sheaf,
with nonzero finite closed-support quotient, has zero H1. The proof uses
the original trace-normalized Serre maps: nonzero H1 would split the same
row and embed its nonzero finite-support quotient in the pure middle term.

For a positive twist the consumer must construct this row from an actual
regular section and establish its quotient support, nonzero quotient and
middle purity. Positivity on the reduction alone is not an input here.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory

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

omit [IsClosedImmersion j] in
/-- Global generation and honest scalar constants annihilate every map
from a nontrivial line to the structure module, over an arbitrary field. -/
theorem cmCurveHomUnit_eq_zero_of_generated_nontrivial
    (hc : Function.Bijective (cmCurveSerreStructuralH0Map k ι j))
    (L : Invertible.LineBundle C) [Epi (globalSectionsEval L.val)]
    (hL : ¬ Nonempty (L.val ≅ cmCurveSerreUnit C))
    (f : L.val ⟶ cmCurveSerreUnit C) : f = 0 := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  let O : C.Modules := cmCurveSerreUnit C
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) O 0
  let H : Ext.{u + 1} (C := C.Modules) O O 0 ≃ₗ[k]
      cmCurveSerreCohomology k ι j O 0 :=
    moduleExtCohomologyLinearEquivOfCategory C (cmCurveSerreScalar k ι j) O 0
  have scalar (g : O ⟶ O) : ∃ c : k, g = c • 𝟙 O := by
    obtain ⟨c, hc'⟩ := hc.2 (H (Ext.mk₀ g))
    refine ⟨c, ?_⟩
    apply (Ext.mk₀_bijective O O).1
    apply H.injective
    rw [Ext.mk₀_smul, H.map_smul]
    exact hc'.symm
  apply (cancel_epi (globalSectionsEval L.val)).mp
  apply Sigma.hom_ext
  intro t
  change Sigma.ι (fun _ : (𝟙_ C.Modules ⟶ (L.val : C.Modules)) => 𝟙_ C.Modules) t ≫
    globalSectionsEval (L.val : C.Modules) ≫ f = _
  erw [← Category.assoc, ι_globalSectionsEval]
  erw [comp_zero]
  obtain ⟨c, hc'⟩ := scalar (t ≫ f)
  by_cases hc0 : c = 0
  · simpa only [hc0, zero_smul] using hc'
  · exfalso
    let eO : O ≅ O :=
      { hom := c • 𝟙 O
        inv := c⁻¹ • 𝟙 O
        hom_inv_id := by simp [smul_smul, hc0]
        inv_hom_id := by simp [smul_smul, hc0] }
    have he : IsIso (t ≫ f) := by rw [hc']; exact eO.isIso_hom
    let := he
    let hf : Epi f := epi_of_epi t f
    let : IsIso f := @isIso_of_epi_of_sheafHasRank C L.val O f hf 1
      ((Invertible.isLocallyRankOne_iff_sheafHasRank_one L.val).mp L.property)
      ((Invertible.isLocallyRankOne_iff_sheafHasRank_one O).mp
        (Invertible.isLocallyRankOne_of_iso C
          (coproductUniqueIso (fun _ : PUnit.{u + 1} => O))
          (Invertible.trivialLineBundle C).property))
    exact hL ⟨asIso f⟩

include e hV hCM hn in
/-- A globally generated, nontrivial invertible line has vanishing
coefficient-canonical H1. No regular section or field extension is needed. -/
theorem cmCurveCoefficientTwist_h1_subsingleton_of_generated_nontrivial
    (hc : Function.Bijective (cmCurveSerreStructuralH0Map k ι j))
    (L : Invertible.LineBundle C) [Epi (globalSectionsEval L.val)]
    (hL : ¬ Nonempty (L.val ≅ cmCurveSerreUnit C)) :
    Subsingleton (cmCurveSerreCohomology k ι j
      (L.val ⊗ cmCurveCoefficientCanonicalModule k ι j n V) 1) := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  let O : C.Modules := cmCurveSerreUnit C
  let W : C.Modules := cmCurveCoefficientCanonicalModule k ι j n V
  let E := Invertible.lineBundleDualTensorEquivalence C L
  let D := Invertible.dualLineBundle C L
  let F : C.Modules := E.functor.obj O
  let : E.functor.Additive := by
    exact moduleTensorLeftFunctor_additive C D.val
  let : E.inverse.Additive := by
    exact moduleTensorLeftFunctor_additive C L.val
  let : D.val.IsFinitePresentation := Invertible.lineBundle_isFinitePresentation C D
  have hF : affineLocallyFiniteType C F :=
    affineLocallyFiniteType_tensor D.val O
      (affineLocallyFiniteType_of_finitePresentation D.val)
      (affineLocallyFiniteType_unit C)
  let LL : C.Modules := L.val
  let U : E.inverse.obj O ≅ LL :=
    MonoidalCategory.rightUnitor (C := C.Modules) L.val
  have hz (f : E.inverse.obj O ⟶ O) : f = 0 := by
    have hf : U.inv ≫ f = (0 : LL ⟶ O) :=
      cmCurveHomUnit_eq_zero_of_generated_nontrivial k ι j hc L hL (U.inv ≫ f)
    exact (U.hom_inv_id_assoc f).symm.trans
      ((congrArg (fun g : LL ⟶ O => U.hom ≫ g) hf).trans
        (comp_zero))
  let : Subsingleton (E.inverse.obj O ⟶ O) :=
    ⟨fun f g => (hz f).trans (hz g).symm⟩
  let : Subsingleton (E.symm.functor.obj O ⟶ O) :=
    inferInstanceAs (Subsingleton (E.inverse.obj O ⟶ O))
  let : Subsingleton (O ⟶ F) :=
    (E.symm.toAdjunction.homEquiv O O).symm.injective.subsingleton
  let : Subsingleton (Ext.{u + 1} O F 0) := (Ext.homEquiv₀ (X := O) (Y := F)).injective.subsingleton
  let H₀ : Ext.{u + 1} (C := C.Modules) O F 0 ≃+
      cmCurveSerreCohomology k ι j F 0 := moduleExtCohomologyAddEquiv C F 0
  let : Subsingleton (cmCurveSerreCohomology k ι j F 0) := H₀.symm.injective.subsingleton
  let P := cmCurveCoefficientSerreDuality k ι j n e V hV hCM F hF 1 (by omega) hn
  let : Subsingleton (Ext.{u + 1} F W 1) := P.injective.subsingleton
  let A : Ext.{u + 1} F W 1 ≃+ Ext.{u + 1} O (E.inverse.obj W) 1 :=
    E.toAdjunction.extEquiv
  let : Subsingleton (Ext.{u + 1} O (E.inverse.obj W) 1) := A.symm.injective.subsingleton
  let H₁ : Ext.{u + 1} (C := C.Modules) O (E.inverse.obj W) 1 ≃+
      cmCurveSerreCohomology k ι j (E.inverse.obj W) 1 :=
    moduleExtCohomologyAddEquiv C (E.inverse.obj W) 1
  exact H₁.symm.injective.subsingleton

include e hV hCM hn in
/-- Nonzero finite-support enlargement of the actual coefficient canonical
module has vanishing H1 when its coherent middle module is pure. -/
theorem cmCurveCoefficientEnlargement_h1_subsingleton
    [IsLocallyNoetherian C]
    (hc : Function.Bijective (cmCurveSerreStructuralH0Map k ι j))
    (F : C.Modules) (hF : affineLocallyFiniteType C F)
    (a : cmCurveCoefficientCanonicalModule k ι j n V ⟶ F) [Mono a]
    (hQ : CanonicalEnlargement.HasFiniteClosedSupport (cokernel a))
    (hQne : ¬ IsZero (cokernel a))
    (hPure : ∀ (T : C.Modules), affineLocallyFiniteType C T →
      CanonicalEnlargement.HasFiniteClosedSupport T →
        ∀ t : T ⟶ F, Mono t → IsZero T) :
    Subsingleton (cmCurveSerreCohomology k ι j F 1) := by
  let W : C.Modules := cmCurveCoefficientCanonicalModule k ι j n V
  have hW : affineLocallyFiniteType C W := by
    let : W.IsFinitePresentation :=
      cmCurveCoefficientCanonicalModule_finitePresentation k ι j n e V
    exact affineLocallyFiniteType_of_finitePresentation W
  rcases subsingleton_or_nontrivial (cmCurveSerreCohomology k ι j F 1) with h | h
  · exact h
  · let : Nontrivial (CanonicalEnlargement.H1 k (cmCurveSerreScalar k ι j) F) := h
    obtain ⟨sp⟩ := CanonicalEnlargement.splitting_of_finiteSupport
      k (cmCurveSerreScalar k ι j) V hV W
      (cmCurveCoefficientSerreTraceEquiv k ι j n e V hV hCM hn hc)
      F a hQ
      (cmCurveCoefficientHomH1Equiv k ι j n e V hV hCM hn F hF)
      (cmCurveCoefficientHomH1Equiv k ι j n e V hV hCM hn W hW)
      (fun f x => cmCurveCoefficientHomH1Equiv_apply k ι j n e V hV hCM hn F hF f x)
      (fun f x => cmCurveCoefficientHomH1Equiv_apply k ι j n e V hV hCM hn W hW f x)
    have hQcoh : affineLocallyFiniteType C (cokernel a) :=
      (affineLocallyFiniteType C).prop_cokernel a hW hF
    have hs : Mono sp.s := mono_of_mono_fac sp.s_g
    exact False.elim (hQne (hPure _ hQcoh hQ sp.s hs))

include e hV hCM hn in
/-- An actual nontrivial finite-support section row for an invertible twist
of the coefficient canonical sheaf implies vanishing, with purity derived. -/
theorem cmCurveCoefficientTwist_h1_subsingleton
    (hc : Function.Bijective (cmCurveSerreStructuralH0Map k ι j))
    (L : Invertible.LineBundle C)
    (a : cmCurveCoefficientCanonicalModule k ι j n V ⟶
      L.val ⊗ cmCurveCoefficientCanonicalModule k ι j n V) [Mono a]
    (hQ : CanonicalEnlargement.HasFiniteClosedSupport (cokernel a))
    (hQne : ¬ IsZero (cokernel a)) :
    Subsingleton (cmCurveSerreCohomology k ι j
      (L.val ⊗ cmCurveCoefficientCanonicalModule k ι j n V) 1) := by
  let : Finite ι := Finite.of_equiv _ e.symm
  let : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian j
  let W : C.Modules := cmCurveCoefficientCanonicalModule k ι j n V
  let : W.IsFinitePresentation :=
    cmCurveCoefficientCanonicalModule_finitePresentation k ι j n e V
  let : L.val.IsFinitePresentation := Invertible.lineBundle_isFinitePresentation C L
  have hF : affineLocallyFiniteType C (L.val ⊗ W) :=
    affineLocallyFiniteType_tensor L.val W
      (affineLocallyFiniteType_of_finitePresentation L.val)
      (affineLocallyFiniteType_of_finitePresentation W)
  apply cmCurveCoefficientEnlargement_h1_subsingleton k ι j n e V hV hCM hn
    hc (L.val ⊗ W) hF a hQ hQne
  intro T hT hSupp t ht
  let := ht
  exact cmCurveCoefficientCanonical_tensor_no_finiteSupport_subobject
    k ι j n e V hV hCM hn L T hT hSupp t

end AlgebraicGeometry.Scheme.Cohomology
