/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Tensor
public import Aglib.CategoryTheory.Limits.Shapes.ZeroObjects

/-! # Acyclicity on specified open restrictions

Source:
`Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/P5NativePhiSupport.lean`
at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Source SHA-256:
`91cab94a8c9ac24cbaaed74cf4fcd39bacea273e378e4a00ba43a9fa26ae76b2`.
Selected declarations: flatPullback_acyclic, flatPullback_preservesSupport, leftTensor_acyclic,
  leftTensor_preservesSupport, coprod_acyclic, coprod_preservesSupport.
Source:
`Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/P5NativeCoefficientsSupport.lean`
at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Source SHA-256:
`f960093218542cb3dc2e13439cc03be9268b0cb50607f10d119b08f3d24a31dd`.
Selected declarations: rightTensor_acyclic, rightTensor_restrictAcyclic.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Modules.Complex

lemma pullback_acyclic {P Y : Scheme.{u}} (f : P ⟶ Y) [Flat f]
    (A : CochainComplex Y.Modules ℤ) (hA : A.Acyclic) : ((pullback f).obj A).Acyclic := by
  intro n
  exact (hA n).map (Scheme.Modules.pullback f)

lemma pullback_restrict_acyclic {P Y : Scheme.{u}} (f : P ⟶ Y) [Flat f]
    (Z : Y.Opens) (A : CochainComplex Y.Modules ℤ) (hA : ((restrict Z.ι).obj A).Acyclic) :
    ((restrict (f ⁻¹ᵁ Z).ι).obj ((pullback f).obj A)).Acyclic := by
  have ha := pullback_acyclic (f ∣_ Z) ((restrict Z.ι).obj A) hA
  intro n
  exact (ha n).of_iso ((pullbackRestrictIso f Z).app A).symm

lemma tensorLeft_acyclic {P : Scheme.{u}} (L : P.Modules) [IsFiniteLocallyFree P L]
    (A : CochainComplex P.Modules ℤ) (hA : A.Acyclic) : ((tensorLeft L).obj A).Acyclic := by
  intro n
  exact (hA n).map (moduleTensorLeftFunctor P L)

lemma tensorLeft_restrict_acyclic {U P : Scheme.{u}} (j : U ⟶ P) [IsOpenImmersion j]
    (L : P.Modules) [IsFiniteLocallyFree P L] (A : CochainComplex P.Modules ℤ)
    (hA : ((restrict j).obj A).Acyclic) :
    ((restrict j).obj ((tensorLeft L).obj A)).Acyclic := by
  have ha := tensorLeft_acyclic (L.restrict j) ((restrict j).obj A) hA
  intro n
  exact (ha n).of_iso ((tensorLeftRestrictionIso j L).app A).symm

lemma coprod_acyclic {P : Scheme.{u}} (A B : CochainComplex P.Modules ℤ) (hA : A.Acyclic) (hB :
  B.Acyclic) :
    (A ⨿ B).Acyclic := by
  intro n
  rw [exactAt_iff_isZero_homology]
  let F := homologyFunctor P.Modules (.up ℤ) n
  let : PreservesFiniteBiproducts F := inferInstance
  let : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBiproducts F
  let : PreservesColimitsOfShape (Discrete WalkingPair) F :=
    preservesBinaryCoproducts_of_preservesBinaryBiproducts F
  exact (coprod_isZero (A.homology n) (B.homology n)
    (hA n).isZero_homology (hB n).isZero_homology).of_iso
      (asIso (coprodComparison F A B)).symm

lemma coprod_restrict_acyclic {U P : Scheme.{u}} (j : U ⟶ P) [IsOpenImmersion j]
    (A B : CochainComplex P.Modules ℤ) (hA : ((restrict j).obj A).Acyclic)
    (hB : ((restrict j).obj B).Acyclic) : ((restrict j).obj (A ⨿ B)).Acyclic := by
  have hab := coprod_acyclic ((restrict j).obj A) ((restrict j).obj B) hA hB
  intro n
  exact (hab n).of_iso (asIso (coprodComparison (restrict j) A B))

lemma tensorRight_acyclic {P : Scheme.{u}} (L : P.Modules) [IsFiniteLocallyFree P L]
    (K : CochainComplex P.Modules ℤ) (hK : K.Acyclic) :
    ((tensorRight L).obj K).Acyclic := by
  intro n
  exact (hK n).map (moduleTensorRightFunctor P L)

lemma tensorRight_restrict_acyclic {U P : Scheme.{u}} (j : U ⟶ P) [IsOpenImmersion j]
    (L : P.Modules) [IsFiniteLocallyFree P L] (K : CochainComplex P.Modules ℤ)
    (hK : ((restrict j).obj K).Acyclic) :
    ((restrict j).obj ((tensorRight L).obj K)).Acyclic := by
  have ht := tensorRight_acyclic (L.restrict j) ((restrict j).obj K) hK
  intro n
  exact (ht n).of_iso ((tensorRightRestrictionIso j L).app K).symm

end AlgebraicGeometry.Scheme.Modules.Complex
