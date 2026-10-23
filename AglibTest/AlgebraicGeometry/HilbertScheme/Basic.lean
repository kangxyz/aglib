/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.HilbertScheme.FlatteningBridge
public import Aglib.AlgebraicGeometry.HilbertScheme.GrassmannianFunctor

/-! Focused consumer of the Hilbert functor of `P^n_A`, its uniform regularity bound, direct
images, Grassmannian point and injectivity in degree `m` (Nitsure, arXiv:math/0504590v1, §5,
pp. 24–26), with axiom guards. -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open scoped Polynomial

universe u

/-- The Hilbert functor is a functor on all schemes over `Spec A`, acting by pullback. -/
example {A : Type u} [CommRing A] (ι : Type u) (Φ : ℚ[X]) :
    (Over (Spec (CommRingCat.of A)))ᵒᵖ ⥤ Type u :=
  hilbertFunctor ι Φ

/-- The fiber condition may be tested at the residue fields of the points. -/
example {A : Type u} [CommRing A] (ι : Type u) [Finite ι] (Φ : ℚ[X]) {T : Scheme.{u}}
    (g : T ⟶ Spec (CommRingCat.of A)) (Z : (pullback (toSpec A ι) g).IdealSheafData) :
    IsHilbertFamily ι Φ g Z ↔ Flat (Z.subschemeι ≫ pullback.snd (toSpec A ι) g) ∧
      ∀ t : T, subschemeHilbertPolynomial ι (T.residueField t)
        (Z.comap (pointMap ι g (T.fromSpecResidueField t))) = Φ :=
  isHilbertFamily_iff_residueField ι Z

/-- **The uniform regularity bound**: one integer `m`, depending only on `n` and `Φ`, makes the
ideal sheaf of every fiber of every point of `Hilb^Φ(T)`, for every `T`, `m`-regular. -/
example {A : Type u} [CommRing A] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1)) (Φ : ℚ[X]) :
    ∃ m : ℤ, ∀ (T : Scheme.{u}) (g : T ⟶ Spec (CommRingCat.of A))
      (Z : (pullback (toSpec A ι) g).IdealSheafData), IsHilbertFamily ι Φ g Z →
      ∀ t : T, Scheme.Cohomology.IsProjectiveRegular (T.residueField t) ι
        (Scheme.Hom.idealModule (Z.comap (pointMap ι g (T.fromSpecResidueField t))).subschemeι)
        m :=
  ⟨hilbertRegularityBound n Φ, fun T _ _ hZ t =>
    hZ.isProjectiveRegular_fiber ι n e _ (T.fromSpecResidueField t)⟩

/-- **Direct images over an affine piece**: vanishing, projectivity and base change of the
cohomology of `I_Z(r)` for `r ≥ m`. -/
example {A : Type u} [CommRing A] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1)) {Φ : ℚ[X]}
    {T : Scheme.{u}} {g : T ⟶ Spec (CommRingCat.of A)}
    {Z : (pullback (toSpec A ι) g).IdealSheafData} (hZ : IsHilbertFamily ι Φ g Z) {B : Type u}
    [CommRing B] [IsNoetherianRing B] (x : Spec (CommRingCat.of B) ⟶ T) (r : ℤ)
    (hr : hilbertRegularityBound n Φ ≤ r) {C : Type u} [CommRing C] (σ : B →+* C) :
    (∀ q : ℕ, q ≠ 0 → Subsingleton (Sheaf.H.{u + 1} (Scheme.Cohomology.moduleAddSheaf
      (ProjectiveSpace B ι) (idealTwist ι (Z.comap (pointMap ι g x)) r)) q)) ∧
    (letI := Scheme.Cohomology.moduleCohomologyModuleOfHom (ProjectiveSpace B ι)
      ((toSpec B ι).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)
      (idealTwist ι (Z.comap (pointMap ι g x)) r) 0
    Module.Projective B (Sheaf.H.{u + 1} (Scheme.Cohomology.moduleAddSheaf (ProjectiveSpace B ι)
      (idealTwist ι (Z.comap (pointMap ι g x)) r)) 0)) ∧
    ∀ q : ℕ, IsIso (Scheme.Cohomology.moduleCohomologyBaseChangeMap (toSpec B ι) σ
      (idealTwist ι (Z.comap (pointMap ι g x)) r) q) :=
  ⟨hZ.subsingleton_moduleCohomology_idealTwist ι n e x r hr,
    hZ.projective_moduleCohomology_idealTwist ι n e x r hr,
    fun q => hZ.isIso_moduleCohomologyBaseChangeMap_idealTwist ι n e x r hr q σ⟩

/-- **Injectivity over an affine test scheme**: a point of `Hilb^Φ(Spec B)` is determined by the
global sections of `I(r) ⊆ 𝒪(r)`, for `r ≥ m`. -/
example {A : Type u} [CommRing A] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1)) {Φ : ℚ[X]}
    {B : Type u} [CommRing B] [IsNoetherianRing B]
    {g : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A)}
    (Z Z' : (hilbertFunctor ι Φ).obj (Opposite.op (Over.mk g))) (r : ℤ)
    (hr : hilbertRegularityBound n Φ ≤ r)
    (h : idealTwistSections ι (Z.1.comap (pointMap ι g (𝟙 _))) r =
      idealTwistSections ι (Z'.1.comap (pointMap ι g (𝟙 _))) r) : Z = Z' :=
  Subtype.ext (Z.2.eq_of_idealTwistSections_eq ι n e Z'.2 r hr h)

/-- **Direct images of the structure module and the exact sequence** over `P^n_B`, for a flat
family with all fiber Hilbert polynomials `Φ` and `r ≥ m`. -/
example {B : Type u} [CommRing B] [IsNoetherianRing B] (ι : Type u) (n : ℕ)
    (e : ι ≃ Fin (n + 1)) {Φ : ℚ[X]} (Z : (ProjectiveSpace B ι).IdealSheafData)
    [Flat (Z.subschemeι ≫ toSpec B ι)]
    (hfib : ∀ p : PrimeSpectrum B,
      subschemeHilbertPolynomial ι p.asIdeal.ResidueField (primeFiber ι Z p) = Φ)
    (r : ℕ) (hr : hilbertRegularityBound n Φ ≤ r) (p : PrimeSpectrum B) :
    (letI := h0Module ι (quotientTwist ι Z r)
    Module.Projective B (Sheaf.H.{u + 1} (Scheme.Cohomology.moduleAddSheaf (ProjectiveSpace B ι)
      (quotientTwist ι Z r)) 0)) ∧
    (Scheme.Cohomology.moduleFiberCohomologyDimension (toSpec B ι) (quotientTwist ι Z r) 0 p :
      ℚ) = Φ.eval (r : ℚ) ∧
    (Scheme.Cohomology.moduleFiberCohomologyDimension (toSpec B ι) (idealTwist ι Z r) 0 p : ℚ) =
      ((r + n).choose n : ℚ) - Φ.eval (r : ℚ) :=
  ⟨projective_moduleCohomology_quotientTwist ι n e Z hfib r hr,
    moduleFiberCohomologyDimension_quotientTwist ι n e Z hfib r hr p,
    moduleFiberCohomologyDimension_idealTwist ι n e Z hfib r hr p⟩

/-- **The Grassmannian point is injective over an affine test scheme.** -/
example {A : Type u} [CommRing A] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1)) {Φ : ℚ[X]}
    {B : Type u} [CommRing B] [IsNoetherianRing B]
    {g : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A)}
    (Z Z' : (hilbertFunctor ι Φ).obj (Opposite.op (Over.mk g))) (r : ℕ)
    (hr : hilbertRegularityBound n Φ ≤ r) :
    letI := h0Module ι (unitTwist (B := B) ι r)
    Z.2.grassmannianPoint ι n e (𝟙 _) r hr = Z'.2.grassmannianPoint ι n e (𝟙 _) r hr → Z = Z' :=
  fun h => Subtype.ext (Z.2.eq_of_grassmannianPoint_eq ι n e Z'.2 r hr h)

/-- **The Hilbert functor in the charts of the flattening stratification**: a closed subscheme is
a point of `Hilb^Φ(T)` iff it is flat over `T` and the chart fiber polynomial of `𝒪_Z` is `Φ`
everywhere. -/
example {A : Type u} [CommRing A] (ι : Type u) [Finite ι] (Φ : ℚ[X]) {T : Scheme.{u}}
    (g : T ⟶ Spec (CommRingCat.of A)) (Z : (pullback (toSpec A ι) g).IdealSheafData) :
    IsHilbertFamily ι Φ g Z ↔ Flat (Z.subschemeι ≫ pullback.snd (toSpec A ι) g) ∧
      ∀ t : T, Scheme.Cohomology.fiberHilbertPolynomialAt ι g Z.quotientModule t = Φ :=
  isHilbertFamily_iff_fiberHilbertPolynomialAt ι

/-- **The point of Mathlib's Grassmannian functor** of a point of `Hilb^Φ(Spec B)`, for an
`A`-algebra `B` with `B` Noetherian: an element of
`(Module.Grassmannian.functor (R := A) (M := A[x]_r) ⌊Φ(r)⌋₊).obj B`. -/
noncomputable example {A : Type u} [CommRing A] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1))
    {Φ : ℚ[X]} (B : CommAlgCat.{u} A) [IsNoetherianRing B]
    {Z : (pullback (toSpec A ι) (Spec.map (CommRingCat.ofHom (algebraMap A B)))).IdealSheafData}
    (hZ : IsHilbertFamily ι Φ (Spec.map (CommRingCat.ofHom (algebraMap A B))) Z) (r : ℕ)
    (hr : hilbertRegularityBound n Φ ≤ r) :
    (Module.Grassmannian.functor (R := A) (M := MvPolynomial.homogeneousSubmodule ι A r)
      ⌊Φ.eval (r : ℚ)⌋₊).obj B :=
  hZ.grassmannianFunctorPoint ι n e r hr

/--
info: 'AlgebraicGeometry.ProjectiveSpace.hilbertFunctor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.hilbertFunctor

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.comap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.comap

/--
info: 'AlgebraicGeometry.ProjectiveSpace.isHilbertFamily_iff_residueField' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.isHilbertFamily_iff_residueField

/--
info: 'AlgebraicGeometry.ProjectiveSpace.subschemeHilbertPolynomial_comap_map' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.subschemeHilbertPolynomial_comap_map

/--
info: 'AlgebraicGeometry.ProjectiveSpace.isProjectiveRegular_idealModule' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.isProjectiveRegular_idealModule

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.isProjectiveRegular_fiber' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.isProjectiveRegular_fiber

/--
info: 'AlgebraicGeometry.Scheme.Modules.relativeFlat_idealModule_of_flat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.relativeFlat_idealModule_of_flat

/--
info: 'AlgebraicGeometry.ProjectiveSpace.isIso_moduleCohomologyBaseChangeMap_idealTwist' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.isIso_moduleCohomologyBaseChangeMap_idealTwist

/--
info: 'AlgebraicGeometry.ProjectiveSpace.projective_moduleCohomology_idealTwist' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.projective_moduleCohomology_idealTwist

/--
info: 'AlgebraicGeometry.ProjectiveSpace.moduleFiberCohomologyDimension_idealTwist' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.moduleFiberCohomologyDimension_idealTwist

/--
info: 'AlgebraicGeometry.ProjectiveSpace.isProjectiveRegular_idealModule_of_flat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.isProjectiveRegular_idealModule_of_flat

/--
info: 'AlgebraicGeometry.ProjectiveSpace.eq_of_idealTwistSections_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.eq_of_idealTwistSections_eq

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.eq_of_idealTwistSections_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.eq_of_idealTwistSections_eq

/--
info: 'AlgebraicGeometry.Scheme.IdealSheafData.affineLocallyFiniteType_quotientModule' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.affineLocallyFiniteType_quotientModule

/--
info: 'AlgebraicGeometry.Scheme.IdealSheafData.relativeFlat_quotientModule_of_flat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.relativeFlat_quotientModule_of_flat

/--
info: 'AlgebraicGeometry.ProjectiveSpace.isIso_moduleCohomologyBaseChangeMap_quotientTwist' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.isIso_moduleCohomologyBaseChangeMap_quotientTwist

/--
info: 'AlgebraicGeometry.ProjectiveSpace.moduleFiberCohomologyDimension_quotientTwist' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.moduleFiberCohomologyDimension_quotientTwist

/--
info: 'AlgebraicGeometry.ProjectiveSpace.exact_moduleCohomology_twistedShortComplex' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.exact_moduleCohomology_twistedShortComplex

/--
info: 'AlgebraicGeometry.ProjectiveSpace.grassmannianPoint' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.grassmannianPoint

/--
info: 'AlgebraicGeometry.ProjectiveSpace.eq_of_grassmannianPoint_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.eq_of_grassmannianPoint_eq

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.grassmannianPoint' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.grassmannianPoint

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.eq_of_grassmannianPoint_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.eq_of_grassmannianPoint_eq

/--
info: 'AlgebraicGeometry.ProjectiveSpace.isHilbertFamily_iff_fiberHilbertPolynomialAt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.isHilbertFamily_iff_fiberHilbertPolynomialAt

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.fiberHilbertPolynomialAt_quotientModule_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.fiberHilbertPolynomialAt_quotientModule_eq

/--
info: 'AlgebraicGeometry.ProjectiveSpace.affineBaseMap_eq_pointMap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.affineBaseMap_eq_pointMap

/--
info: 'AlgebraicGeometry.ProjectiveSpace.isHilbertFamily_iff_relativeFlat_and_fiberHilbertPolynomialAt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.isHilbertFamily_iff_relativeFlat_and_fiberHilbertPolynomialAt

/--
info: 'AlgebraicGeometry.Scheme.IdealSheafData.relativeFlat_quotientModule_iff_flat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.relativeFlat_quotientModule_iff_flat

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.projective_moduleCohomology_quotientTwist' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.projective_moduleCohomology_quotientTwist

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.grassmannianFunctorPoint' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.grassmannianFunctorPoint

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.eq_of_grassmannianFunctorPoint_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.eq_of_grassmannianFunctorPoint_eq

/--
info: 'Module.Grassmannian.eq_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Module.Grassmannian.eq_of_le

/--
info: 'Module.Grassmannian.map_toSubmodule_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Module.Grassmannian.map_toSubmodule_le

/--
info: 'Module.Grassmannian.map_eq_of_forall' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Module.Grassmannian.map_eq_of_forall

/--
info: 'AlgebraicGeometry.ProjectiveSpace.add_two_le_hilbertRegularityBound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.add_two_le_hilbertRegularityBound

/--
info: 'AlgebraicGeometry.ProjectiveSpace.rankAtStalk_moduleCohomology_idealTwist' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.rankAtStalk_moduleCohomology_idealTwist

/--
info: 'AlgebraicGeometry.ProjectiveSpace.rankAtStalk_moduleCohomology_quotientTwist' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.rankAtStalk_moduleCohomology_quotientTwist

/--
info: 'AlgebraicGeometry.ProjectiveSpace.pointMap_comp_baseChangeMap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.pointMap_comp_baseChangeMap

/--
info: 'AlgebraicGeometry.ProjectiveSpace.isPullback_pointMap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.isPullback_pointMap

/--
info: 'AlgebraicGeometry.ProjectiveSpace.map_comp_pointMap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.map_comp_pointMap

/--
info: 'AlgebraicGeometry.ProjectiveSpace.isPullback_baseChangeMap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.isPullback_baseChangeMap

/--
info: 'AlgebraicGeometry.Scheme.IdealSheafData.le_of_idealInclusion_factor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.le_of_idealInclusion_factor

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.unitHomH0Equiv_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.unitHomH0Equiv_comp

/--
info: 'AlgebraicGeometry.Scheme.Hom.affineLocallyFiniteType_idealModule' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Hom.affineLocallyFiniteType_idealModule

/--
info: 'Int.eq_of_forall_sum_mul_choose_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Int.eq_of_forall_sum_mul_choose_eq

/--
info: 'MvPolynomial.finrank_homogeneousSubmodule_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MvPolynomial.finrank_homogeneousSubmodule_eq

/--
info: 'MvPolynomial.homogeneousSubmoduleBaseChangeEquiv_tmul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MvPolynomial.homogeneousSubmoduleBaseChangeEquiv_tmul

/--
info: 'Module.rankAtStalk_eq_finrank_of_extendScalars_iso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Module.rankAtStalk_eq_finrank_of_extendScalars_iso

/--
info: 'Module.Grassmannian.ofSurjective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Module.Grassmannian.ofSurjective

/--
info: 'Module.Grassmannian.ofLinearEquiv_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Module.Grassmannian.ofLinearEquiv_injective
