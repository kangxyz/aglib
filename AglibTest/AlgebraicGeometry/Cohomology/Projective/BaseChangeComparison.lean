/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.BaseChangeComparison

/-! Focused consumer of the base-change comparison for the universal property of the flattening
stratification (Nitsure, arXiv:math/0504590v1, Thm 4.3 (ii), proof pp. 22–23, over affine
Noetherian `S = Spec A`, `T = Spec B`), and of its supporting leaves (pullback along composites,
iterated base change through a flat square, vanishing from the fibres), with axiom guards. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Cohomology

universe u

/-- Nitsure's comparison `φ^* π_* F(m) ≅ π_{T*} F_T(m)` for `T = Spec B ⟶ S = Spec A`, when
`F_T` is flat and (B), (C) hold at the points of `S` for the twist `m`. -/
example {A B : Type u} [CommRing A] [IsNoetherianRing A] [CommRing B] [IsNoetherianRing B]
    (σ : A →+* B) {ι : Type u} (n : ℕ) (e : ι ≃ Fin (n + 1)) (F : (ProjectiveSpace A ι).Modules)
    (hF : affineLocallyFiniteType (ProjectiveSpace A ι) F) (m : ℤ)
    (hC : ∀ s : PrimeSpectrum A, IsIso (moduleCohomologyBaseChangeMap (toSpec A ι)
      (algebraMap A s.asIdeal.ResidueField)
      ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι m)).obj F) 0))
    (hB : ∀ (s : PrimeSpectrum A) (q : ℕ), q ≠ 0 → Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf (pullback (toSpec A ι)
        (Spec.map (CommRingCat.ofHom (algebraMap A s.asIdeal.ResidueField))))
      ((Scheme.Modules.pullback (pullback.fst (toSpec A ι)
        (Spec.map (CommRingCat.ofHom (algebraMap A s.asIdeal.ResidueField))))).obj
        ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι m)).obj F))) q))
    (hflat : relativeFlat (toSpec B ι) ((Scheme.Modules.pullback (map σ ι)).obj F)) :
    IsIso (moduleCohomologyBaseChangeMap (toSpec A ι) σ
      ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι m)).obj F) 0) :=
  (moduleCohomologyBaseChangeMap_twist_isIso_and_projective_of_fiberwise σ n e F hF m hC hB
    hflat).1

/-- The same in the coordinates of `P^n_{κ(s)}` and `P^n_B`, with projective target. -/
example {A B : Type u} [CommRing A] [IsNoetherianRing A] [CommRing B] [IsNoetherianRing B]
    (σ : A →+* B) {ι : Type u} (n : ℕ) (e : ι ≃ Fin (n + 1)) (F : (ProjectiveSpace A ι).Modules)
    (hF : affineLocallyFiniteType (ProjectiveSpace A ι) F) (m : ℤ)
    (hC : ∀ s : PrimeSpectrum A, Function.Bijective
      (baseChangeTwistCohomologyHom (algebraMap A s.asIdeal.ResidueField) ι m F 0 ∘
        moduleCohomologyBaseChangeMap (toSpec A ι) (algebraMap A s.asIdeal.ResidueField)
          ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι m)).obj F) 0))
    (hB : ∀ (s : PrimeSpectrum A) (q : ℕ), q ≠ 0 → Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf (ProjectiveSpace s.asIdeal.ResidueField ι)
        ((moduleTensorLeftFunctor (ProjectiveSpace s.asIdeal.ResidueField ι)
          (twistingSheaf s.asIdeal.ResidueField ι m)).obj
          ((Scheme.Modules.pullback (map (algebraMap A s.asIdeal.ResidueField) ι)).obj F))) q))
    (hflat : relativeFlat (toSpec B ι) ((Scheme.Modules.pullback (map σ ι)).obj F)) :
    Function.Bijective (baseChangeTwistCohomologyHom σ ι m F 0 ∘
      moduleCohomologyBaseChangeMap (toSpec A ι) σ
        ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι m)).obj F) 0) :=
  (bijective_baseChangeTwist_and_projective_of_fiberwise_projectiveSpace σ n e F hF m hC hB
    hflat).1

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.pullbackPushforwardAdjunction_unit_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.pullbackPushforwardAdjunction_unit_comp

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.moduleCohomologyPullback_comp_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.moduleCohomologyPullback_comp_apply

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.moduleCohomologyPullback_congr_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.moduleCohomologyPullback_congr_apply

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.sheafH_map_toSheaf_comp_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.sheafH_map_toSheaf_comp_apply

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.sheafH_map_toSheaf_comp_apply_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.sheafH_map_toSheaf_comp_apply_eq

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.pullbackSquareCoefficientIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.pullbackSquareCoefficientIso

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.pullbackComp_inv_app_pullbackSquareCoefficientIso_hom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.pullbackComp_inv_app_pullbackSquareCoefficientIso_hom

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.moduleCohomologyPullback_pullbackSquare_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.moduleCohomologyPullback_pullbackSquare_apply

/--
info: 'ModuleCat.extendScalarsCongrIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.extendScalarsCongrIso

/--
info: 'ModuleCat.extendScalarsCongrIso_hom_one_tmul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.extendScalarsCongrIso_hom_one_tmul

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.specMap_comp_specMap_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.specMap_comp_specMap_eq

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.baseChangeCompLift_condition' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.baseChangeCompLift_condition

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.baseChangeCompLift' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.baseChangeCompLift

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.baseChangeCompLift_fst' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.baseChangeCompLift_fst

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.baseChangeCompLift_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.baseChangeCompLift_snd

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.isPullback_baseChangeCompLift' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.isPullback_baseChangeCompLift

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.isIso_moduleCohomologyTensorMap_baseChangeCompLift' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.isIso_moduleCohomologyTensorMap_baseChangeCompLift

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.isIso_moduleCohomologyTensorMap_comp_of_square' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.isIso_moduleCohomologyTensorMap_comp_of_square

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.isIso_moduleCohomologyBaseChangeMap_comp_of_isIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.isIso_moduleCohomologyBaseChangeMap_comp_of_isIso

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.subsingleton_moduleCohomology_baseChangeComp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.subsingleton_moduleCohomology_baseChangeComp

/--
info: 'Ideal.ResidueField.mapComap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ideal.ResidueField.mapComap

/--
info: 'Ideal.ResidueField.algebraMap_comp_eq_mapComap_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ideal.ResidueField.algebraMap_comp_eq_mapComap_comp

/--
info: 'Ideal.ResidueField.flat_mapComap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ideal.ResidueField.flat_mapComap

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.isIso_moduleCohomologyBaseChangeMap_comp_residueField' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.isIso_moduleCohomologyBaseChangeMap_comp_residueField

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.subsingleton_moduleCohomology_residueField_pullback' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.subsingleton_moduleCohomology_residueField_pullback

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.subsingleton_moduleCohomology_of_subsingleton_fiber_of_proper' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.subsingleton_moduleCohomology_of_subsingleton_fiber_of_proper

/--
info: 'AlgebraicGeometry.ProjectiveSpace.baseChangeIso_inv_toSpec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.baseChangeIso_inv_toSpec

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.subsingleton_moduleCohomology_baseChange_of_fiberwise' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.subsingleton_moduleCohomology_baseChange_of_fiberwise

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.moduleCohomologyBaseChangeMap_isIso_and_projective_of_fiberwise' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.moduleCohomologyBaseChangeMap_isIso_and_projective_of_fiberwise

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.baseChangeIsoPullbackInvHomIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.baseChangeIsoPullbackInvHomIso

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.relativeFlat_pullback_twist_of_relativeFlat_map' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.relativeFlat_pullback_twist_of_relativeFlat_map

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.moduleCohomologyBaseChangeMap_twist_isIso_and_projective_of_fiberwise' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.moduleCohomologyBaseChangeMap_twist_isIso_and_projective_of_fiberwise

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.bijective_baseChangeTwist_and_projective_of_fiberwise_projectiveSpace' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.bijective_baseChangeTwist_and_projective_of_fiberwise_projectiveSpace
