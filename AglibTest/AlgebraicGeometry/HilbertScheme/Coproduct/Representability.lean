/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.HilbertScheme.Coproduct.Representability
public import Aglib.AlgebraicGeometry.HilbertScheme.Quotient.Datum

/-! Focused consumer of the representability of the Hilbert functor of an immersed scheme with
Hilbert polynomials in a set `F` by the disjoint union `H_F = ∐_{Φ ∈ F} H^Φ_Y`: from any
representations of the pieces, for the Hilbert schemes of `HilbertScheme/Immersed/Representability`,
the existence for every set `F`, and the Hilbert datum of the quotient construction built from
`H_F`, with axiom guards. -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open scoped Polynomial

universe u

section Pieces

variable {A : Type u} [CommRing A] {ι : Type u} [Finite ι] {Y : Scheme.{u}}
  (i : Y ⟶ ProjectiveSpace A ι) [IsImmersion i] {F : Set ℚ[X]}
  {H : F → Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
  (E : ∀ Φ : F, (locallyNoetherianImmersedHilbertFunctor i rfl Φ).RepresentableBy (H Φ))
  (n : ℕ) (e : ι ≃ Fin (n + 1))

/-- **From representations of the pieces**: the disjoint union represents the Hilbert functor with
polynomials in `F`, the point given by `a` being the pullback of the glued universal family, which
restricts to the universal family of each piece. -/
example {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (a : T ⟶ Scheme.LocallyNoetherianOver.sigma H) (Φ : F) :
    ((sigmaImmersedHilbertRepresentableBy i rfl E n e).homEquiv a).1 =
        (sigmaImmersedHilbertFamily i rfl E).comap (pullback.map (i ≫ toSpec A ι) T.obj.hom
          (i ≫ toSpec A ι) (Sigma.desc fun Φ : F => (H Φ).obj.hom) (𝟙 Y) a.hom.left (𝟙 _)
          (by simp) ((Category.comp_id _).trans (Over.w a.hom).symm)) ∧
      (sigmaImmersedHilbertFamily i rfl E).comap
          (Scheme.pullbackSigmaι (i ≫ toSpec A ι) (fun Φ : F => (H Φ).obj.hom) Φ) =
        ((E Φ).homEquiv (𝟙 (H Φ))).1 :=
  ⟨sigmaImmersedHilbertRepresentableBy_homEquiv_coe i rfl E n e a,
    comap_sigmaImmersedHilbertFamily i rfl E Φ⟩

/-- **Injectivity and surjectivity on plain morphisms** from a locally Noetherian scheme. -/
example {T : Scheme.{u}} [IsLocallyNoetherian T] (g : T ⟶ Spec (CommRingCat.of A))
    (V : (pullback (i ≫ toSpec A ι) g).IdealSheafData)
    (hV : IsImmersedHilbertFamilyIn i rfl F g V) :
    ∃ (a : T ⟶ ∐ fun Φ : F => (H Φ).obj.left)
      (ha : a ≫ Sigma.desc (fun Φ : F => (H Φ).obj.hom) = g),
      (sigmaImmersedHilbertFamily i rfl E).comap (pullback.map (i ≫ toSpec A ι) g
        (i ≫ toSpec A ι) (Sigma.desc fun Φ : F => (H Φ).obj.hom) (𝟙 Y) a (𝟙 _) (by simp)
        (by simp [ha])) = V :=
  exists_comap_sigmaImmersedHilbertFamily_eq i rfl E n e g V hV

end Pieces

section Scheme

variable (ι : Type u) [Finite ι] (n : ℕ) (e : ι ≃ Fin (n + 1)) (A : Type u) [CommRing A]
  [IsNoetherianRing A] {F : Set ℚ[X]} (r : F → ℕ)
  (hr : ∀ Φ : F, hilbertRegularityBound n Φ ≤ r Φ) {J : F → Type u}
  (φ : ∀ Φ : F, SheafOfModules.free (R := (ProjectiveSpace A ι).ringCatSheaf) (J Φ) ⟶
    twistingSheaf A ι (r Φ : ℤ))
  {Y : Scheme.{u}} (i : Y ⟶ ProjectiveSpace A ι) [IsImmersion i]
  (hC : ∀ Φ : F, Scheme.Modules.Hom.imageIdealData (sectionPairing ι (r Φ) (φ Φ)) = i.ker)

/-- **`H_F` represents the Hilbert functor of `Y` with Hilbert polynomials in `F`**, with universal
family glued from the universal families of the `H^Φ_Y`. -/
example {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (a : T ⟶ sigmaImmersedHilbertSchemeOver ι n e A r hr φ i) (Φ : F) :
    ((locallyNoetherianImmersedHilbertFunctorInRepresentableBy ι n e A r hr φ i rfl hC).homEquiv
        a).1 =
        (universalSigmaImmersedHilbertFamily ι n e A r hr φ i rfl).comap
          (pullback.map (i ≫ toSpec A ι) T.obj.hom (i ≫ toSpec A ι)
            (sigmaImmersedHilbertSchemeOver ι n e A r hr φ i).obj.hom (𝟙 Y) a.hom.left (𝟙 _)
            (by simp) ((Category.comp_id _).trans (Over.w a.hom).symm)) ∧
      (universalSigmaImmersedHilbertFamily ι n e A r hr φ i rfl).comap
          (Scheme.pullbackSigmaι (i ≫ toSpec A ι)
            (fun Φ : F => (immersedHilbertSchemeOver ι n e A Φ (r Φ) (hr Φ) (φ Φ) i).obj.hom) Φ) =
        universalImmersedHilbertFamily ι n e A Φ (r Φ) (hr Φ) (φ Φ) i rfl :=
  ⟨locallyNoetherianImmersedHilbertFunctorInRepresentableBy_homEquiv_coe ι n e A r hr φ i rfl hC a,
    comap_universalSigmaImmersedHilbertFamily ι n e A r hr φ i rfl Φ⟩

/-- **The glued image** of the universal family of `H_F`. -/
example :
    (universalSigmaImmersedHilbertFamily ι n e A r hr φ i rfl).map
        (immersionBaseChange i rfl (sigmaImmersedHilbertSchemeOver ι n e A r hr φ i).obj.hom) =
      Scheme.IdealSheafData.sigmaGlue (toSpec A ι)
        (fun Φ : F => (immersedHilbertSchemeOver ι n e A Φ (r Φ) (hr Φ) (φ Φ) i).obj.hom)
        fun Φ => (universalImmersedHilbertFamily ι n e A Φ (r Φ) (hr Φ) (φ Φ) i rfl).map
          (immersionBaseChange i rfl
            (immersedHilbertSchemeOver ι n e A Φ (r Φ) (hr Φ) (φ Φ) i).obj.hom) :=
  map_universalSigmaImmersedHilbertFamily ι n e A r hr φ i rfl hC

/-- **Existence**: for every set `F` of polynomials there are bounds and sections for which `H_F`
represents the Hilbert functor of `Y` with Hilbert polynomials in `F`. -/
example (F : Set ℚ[X]) :
    ∃ (r : F → ℕ) (hr : ∀ Φ : F, hilbertRegularityBound n Φ ≤ r Φ) (J : F → Type u)
      (φ : ∀ Φ : F, SheafOfModules.free (R := (ProjectiveSpace A ι).ringCatSheaf) (J Φ) ⟶
        twistingSheaf A ι (r Φ : ℤ)),
      (∀ Φ : F, Scheme.Modules.Hom.imageIdealData (sectionPairing ι (r Φ) (φ Φ)) = i.ker) ∧
        Nonempty ((locallyNoetherianImmersedHilbertFunctorIn i rfl F).RepresentableBy
          (sigmaImmersedHilbertSchemeOver ι n e A r hr φ i)) :=
  exists_sigmaImmersedHilbertScheme_representableBy ι n e A i rfl F

/-- **The Hilbert datum of the quotient construction from `H_F`** (Nitsure, arXiv:math/0504590v1,
proof of Thm 6.8, p. 33): for a locally Noetherian `Y`, a relation `j : R ⟶ Y ×_{Spec A} Y` whose
ideal is a point of the Hilbert functor of `Y` with polynomials in `F` (for `R` regarded as a family
over `Y` through the second projection), and `0 ∉ F`, the scheme `H_F` with its universal family
and the classifying morphism of `R` is a `QuotientHilbertDatum`. -/
example [IsLocallyNoetherian Y] {R : Scheme.{u}} (j : R ⟶ pullback (i ≫ toSpec A ι) (i ≫ toSpec A ι))
    (hR : IsImmersedHilbertFamilyIn i rfl F (i ≫ toSpec A ι) j.ker) (h0 : (0 : ℚ[X]) ∉ F) :
    QuotientHilbertDatum (i ≫ toSpec A ι) j :=
  have hφ := exists_comap_universalSigmaImmersedHilbertFamily_eq ι n e A r hr φ i rfl hC
    (i ≫ toSpec A ι) j.ker hR
  { H := sigmaImmersedHilbertScheme ι n e A r hr φ i
    πH := (sigmaImmersedHilbertSchemeOver ι n e A r hr φ i).obj.hom
    D := universalSigmaImmersedHilbertFamily ι n e A r hr φ i rfl
    flat := flat_universalSigmaImmersedHilbertFamily ι n e A r hr φ i rfl hC
    isProper := isProper_universalSigmaImmersedHilbertFamily ι n e A r hr φ i rfl hC
    surjective :=
      surjective_universalSigmaImmersedHilbertFamily_of_zero_notMem ι n e A r hr φ i rfl hC h0
    φ := hφ.choose
    w := hφ.choose_spec.choose
    comap_eq := hφ.choose_spec.choose_spec
    injective := fun T _ g a b ha hb h =>
      eq_of_comap_universalSigmaImmersedHilbertFamily_eq ι n e A r hr φ i rfl hC T g a b ha hb h }

end Scheme

section Occurring

variable (ι : Type u) [Finite ι] (n : ℕ) (e : ι ≃ Fin (n + 1)) (A : Type u) [CommRing A]
  [IsNoetherianRing A] {Y : Scheme.{u}} (i : Y ⟶ ProjectiveSpace A ι) [IsImmersion i]

/-- **The quotient datum for the polynomials that occur**: for a locally Noetherian `Y` and a
relation `j : R ⟶ Y ×_{Spec A} Y` whose ideal is proper, flat and surjective over `Y` through the
second projection, take for `F` the fibre polynomials of the image of `R`; then `0 ∉ F`, and `H_F`
gives a `QuotientHilbertDatum`. -/
example [IsLocallyNoetherian Y] {R : Scheme.{u}}
    (j : R ⟶ pullback (i ≫ toSpec A ι) (i ≫ toSpec A ι))
    (hp : IsProper (j.ker.subschemeι ≫ pullback.snd (i ≫ toSpec A ι) (i ≫ toSpec A ι)))
    (hf : Flat (j.ker.subschemeι ≫ pullback.snd (i ≫ toSpec A ι) (i ≫ toSpec A ι)))
    (hs : Surjective (j.ker.subschemeι ≫ pullback.snd (i ≫ toSpec A ι) (i ≫ toSpec A ι))) :
    Nonempty (QuotientHilbertDatum (i ≫ toSpec A ι) j) := by
  have hR := isImmersedHilbertFamilyIn_range_fiberHilbertPolynomialAt i rfl (i ≫ toSpec A ι)
    j.ker hp hf
  have := hR.isClosedImmersion
  have h0 := (zero_notMem_range_fiberHilbertPolynomialAt_map_immersionBaseChange_iff i rfl
    (i ≫ toSpec A ι) j.ker n e).mpr hs
  obtain ⟨r, hr, J, φ, hC, -⟩ := exists_sigmaImmersedHilbertScheme_representableBy ι n e A i rfl
    (Set.range (Scheme.Cohomology.fiberHilbertPolynomialAt ι (i ≫ toSpec A ι)
      (j.ker.map (immersionBaseChange i rfl (i ≫ toSpec A ι))).quotientModule))
  obtain ⟨a, ha, haR⟩ := exists_comap_universalSigmaImmersedHilbertFamily_eq ι n e A r hr φ i rfl
    hC (i ≫ toSpec A ι) j.ker hR
  exact ⟨{ H := sigmaImmersedHilbertScheme ι n e A r hr φ i
           πH := (sigmaImmersedHilbertSchemeOver ι n e A r hr φ i).obj.hom
           D := universalSigmaImmersedHilbertFamily ι n e A r hr φ i rfl
           flat := flat_universalSigmaImmersedHilbertFamily ι n e A r hr φ i rfl hC
           isProper := isProper_universalSigmaImmersedHilbertFamily ι n e A r hr φ i rfl hC
           surjective :=
             surjective_universalSigmaImmersedHilbertFamily_of_zero_notMem ι n e A r hr φ i rfl hC
               h0
           φ := a
           w := ha
           comap_eq := haR
           injective := fun T _ g a b ha hb h =>
             eq_of_comap_universalSigmaImmersedHilbertFamily_eq ι n e A r hr φ i rfl hC T g a b ha
               hb h }⟩

end Occurring

/--
info: 'AlgebraicGeometry.ProjectiveSpace.sigmaImmersedHilbertRepresentableBy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.sigmaImmersedHilbertRepresentableBy

/--
info: 'AlgebraicGeometry.ProjectiveSpace.eq_of_comap_sigmaImmersedHilbertFamily_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.eq_of_comap_sigmaImmersedHilbertFamily_eq

/--
info: 'AlgebraicGeometry.ProjectiveSpace.exists_comap_sigmaImmersedHilbertFamily_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.exists_comap_sigmaImmersedHilbertFamily_eq

/--
info: 'AlgebraicGeometry.ProjectiveSpace.locallyNoetherianImmersedHilbertFunctorInRepresentableBy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.locallyNoetherianImmersedHilbertFunctorInRepresentableBy

/--
info: 'AlgebraicGeometry.ProjectiveSpace.locallyNoetherianImmersedHilbertFunctorInRepresentableBy_homEquiv_coe' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.ProjectiveSpace.locallyNoetherianImmersedHilbertFunctorInRepresentableBy_homEquiv_coe

/--
info: 'AlgebraicGeometry.ProjectiveSpace.eq_of_comap_universalSigmaImmersedHilbertFamily_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.eq_of_comap_universalSigmaImmersedHilbertFamily_eq

/--
info: 'AlgebraicGeometry.ProjectiveSpace.exists_comap_universalSigmaImmersedHilbertFamily_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.exists_comap_universalSigmaImmersedHilbertFamily_eq

/--
info: 'AlgebraicGeometry.ProjectiveSpace.isImmersedHilbertFamilyIn_universalSigmaImmersedHilbertFamily' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.ProjectiveSpace.isImmersedHilbertFamilyIn_universalSigmaImmersedHilbertFamily

/--
info: 'AlgebraicGeometry.ProjectiveSpace.surjective_universalSigmaImmersedHilbertFamily_of_zero_notMem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.ProjectiveSpace.surjective_universalSigmaImmersedHilbertFamily_of_zero_notMem

/--
info: 'AlgebraicGeometry.ProjectiveSpace.map_universalSigmaImmersedHilbertFamily' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.map_universalSigmaImmersedHilbertFamily

/--
info: 'AlgebraicGeometry.ProjectiveSpace.exists_sigmaImmersedHilbertScheme_representableBy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.exists_sigmaImmersedHilbertScheme_representableBy
