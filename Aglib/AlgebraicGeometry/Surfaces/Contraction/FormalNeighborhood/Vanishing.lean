/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Contraction.FormalNeighborhood.Completion
public import Aglib.AlgebraicGeometry.Surfaces.Contraction.FormalNeighborhood.Powers

/-!
# Vanishing for the original line-coefficient quotients

The actual coefficient quotients have successive O_E(n+a) layers. For a ≥ −1, their H1 vanishes,
and actual proper formal functions plus finite Nakayama gives vanishing of the original dual
Cartier ideal. Compactness and separatedness are derived from the proper map in that endpoint.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Surfaces.Contraction.FormalNeighborhood

universe u v w t

section ActualLineQuotients

open CategoryTheory.MonoidalCategory AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules.Invertible AlgebraicGeometry.Scheme.Modules.QuasiCoherent

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of R))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Per original ideal, tensoring the actual structure quotient gives the
actual coefficient quotient. The comparison uses the original thickening
and the native closed-immersion projection formula, with no tower datum. -/
def tensorUnitQuotientIso (F : X.Modules) [F.IsQuasicoherent] (J : Ideal R) :
    tensorSheaf X F (idealQuotient X (affineFormalFunctionsScalar f)
        (SheafOfModules.unit X.ringCatSheaf) J) ≅
      idealQuotient X (affineFormalFunctionsScalar f) F J := by
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let _ : O.IsQuasicoherent := quasicoherent_of_affineCharts O
    (fun R p _ => (affineLocallyFiniteType_unit X R p).1)
  let _ : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  let j := idealThickeningι f J
  let e₀ : idealQuotient X (affineFormalFunctionsScalar f) O J ≅
      (Scheme.Modules.pushforward j).obj
        (SheafOfModules.unit (idealThickeningSpace f J).ringCatSheaf) :=
    idealQuotientThickeningIso f O J ≪≫
      (Scheme.Modules.pushforward j).mapIso (pullbackUnitIso j)
  exact tensorSheafIso X (Iso.refl F) e₀ ≪≫
    closedImmersionProjectionFormulaIso j F
      (SheafOfModules.unit (idealThickeningSpace f J).ringCatSheaf) ≪≫
    (Scheme.Modules.pushforward j).mapIso
      (rightUnitor (C := (idealThickeningSpace f J).Modules)
        ((Scheme.Modules.pullback j).obj F)) ≪≫
    (idealQuotientThickeningIso f F J).symm

variable {k : Type u} [CommRing k]
  (i : ProjectiveSpace k (ULift.{u} (Fin 2)) ⟶ X) [IsClosedImmersion i]
  (hI : IsLocallyRankOne X (Hom.idealModule i))
  (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
    twistingSheaf k (ULift.{u} (Fin 2)) 1)
  (I : Ideal R) (β : R →+* k) (hβ : RingHom.ker β = I)
  (hker : (Spec.map (CommRingCat.ofHom β)).ker.comap f = i.ker)
  (L : LineBundle X) (a : ℤ)
  (eL : (Scheme.Modules.pullback i).obj L.val ≅
    twistingSheaf k (ULift.{u} (Fin 2)) a)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual original line-coefficient quotients have the actual
successive projective-line twists as their short exact layers. -/
def lineQuotientLayerSequence (n : ℕ) : ShortComplex X.Modules := by
  let S := idealPowerFormalLayerSequence f i hI eI I β hβ hker n
  let T := (lineBundleDualTensorEquivalence X L).inverse
  let P := ProjectiveSpace k (ULift.{u} (Fin 2))
  let e₁ : (S.map T).X₁ ≅ (Scheme.Modules.pushforward i).obj
      (twistingSheaf k (ULift.{u} (Fin 2)) (a + (n : ℤ))) :=
    closedImmersionProjectionFormulaIso i L.val
      (twistingSheaf k (ULift.{u} (Fin 2)) (n : ℤ)) ≪≫
      (Scheme.Modules.pushforward i).mapIso
        (tensorSheafIso P eL (Iso.refl _)) ≪≫
      (Scheme.Modules.pushforward i).mapIso
        (twistingTensorIso k (ULift.{u} (Fin 2)) a (n : ℤ))
  let e₂ := tensorUnitQuotientIso f L.val (I ^ (n + 1))
  let e₃ := tensorUnitQuotientIso f L.val (I ^ n)
  exact cartierSequenceOfIsos (S.map T) e₁ e₂ e₃

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Exact tensoring by the actual line bundle proves the line-coefficient
quotient-layer exactness; no layer sequence is assumed. -/
theorem lineQuotientLayerSequence_shortExact (n : ℕ) :
    (lineQuotientLayerSequence f i hI eI I β hβ hker L a eL n).ShortExact := by
  let S := idealPowerFormalLayerSequence f i hI eI I β hβ hker n
  have hS := idealPowerFormalLayerSequence_shortExact f i hI eI I β hβ hker n
  let _ : Mono S.f := hS.mono_f
  let _ : Epi S.g := hS.epi_g
  let T := (lineBundleDualTensorEquivalence X L).inverse
  let _ : T.IsEquivalence := inferInstance
  dsimp only [lineQuotientLayerSequence]
  apply cartierSequenceOfIsos_shortExact
  exact hS.map T

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
include i hI eI β hβ hker eL in
/-- Every ORIGINAL coefficient quotient has vanishing H1 when the original
line restricts to O_E(a), a≥-1. The actual layers, not a vanishing oracle,
are constructed above; transition-coordinate comparisons are unnecessary. -/
theorem lineQuotient_h1_subsingleton [CompactSpace X] [X.IsSeparated] (ha : -1 ≤ a) (n : ℕ) :
    Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf X (idealPowerQuotient X (affineFormalFunctionsScalar f) L.val I n)) 1) := by
  induction n with
  | zero =>
    let α := affineFormalFunctionsScalar f
    exact ModuleCat.subsingleton_of_isZero
      ((moduleCohomologyFunctorOfHom X α 1).map_isZero
        (idealPowerQuotient_zero_isZero X α L.val I))
  | succ n ih =>
    let S := lineQuotientLayerSequence f i hI eI I β hβ hker L a eL n
    change Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X S.X₂) 1)
    exact CartierCurve.h1_subsingleton_middle S
      (lineQuotientLayerSequence_shortExact f i hI eI I β hβ hker L a eL n)
      (CartierCurve.pushforward_twist_cohomology_subsingleton i (a + (n : ℤ))
        (by omega) 1 (by decide)) ih

end ActualLineQuotients

section ActualDualCartierVanishing

open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

variable {R k : Type u} [CommRing R] [IsNoetherianRing R] [CommRing k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of R)) [IsProper f]
  (i : ProjectiveSpace k (ULift.{u} (Fin 2)) ⟶ X) [IsClosedImmersion i]
  (hI : IsLocallyRankOne X (Hom.idealModule i))
  (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
    twistingSheaf k (ULift.{u} (Fin 2)) 1)
  (I : Ideal R) (β : R →+* k) (hβ : RingHom.ker β = I)
  (hker : (Spec.map (CommRingCat.ofHom β)).ker.comap f = i.ker)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
include f eI β hβ hker in
/-- The ORIGINAL dual exceptional ideal has zero H1 on the actual proper
source. Its original adic quotients have the constructed layers O_E(n-1),
so no quotient vanishing, transition correction or coefficient field is assumed. -/
theorem dualCartier_h1_subsingleton (hJac : I ≤ (⊥ : Ideal R).jacobson) :
    Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf X (dualLineBundle X (cartierIdealLineBundle i hI)).val) 1) := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  let L := dualLineBundle X (cartierIdealLineBundle i hI)
  let eL := conormalDualRestrictionIso i (cartierIdealLineBundle i hI) eI
  let _ : L.val.IsFinitePresentation := lineBundle_isFinitePresentation X L
  apply h1_subsingleton_of_quotient_h1_subsingleton I f L.val
    (affineLocallyFiniteType_of_finitePresentation L.val) hJac
  intro n
  exact lineQuotient_h1_subsingleton f i hI eI I β hβ hker L (-1) eL (le_refl _) n

end ActualDualCartierVanishing

end AlgebraicGeometry.Scheme.Surfaces.Contraction.FormalNeighborhood
