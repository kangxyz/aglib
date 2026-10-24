/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.HilbertScheme.Coproduct.Functor

/-! Focused consumer of the Hilbert functor of an immersed scheme `Y ⊆ P^n_A` with Hilbert
polynomials in a set `F`: the image over the base, the points and their base change, the functor,
the comparison with `Hilb^Φ_Y`, and the glued families (the glued image and the component
detection), with axiom guards. -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Cohomology
open scoped Polynomial

universe u

variable {A : Type u} [CommRing A] {ι : Type u} {Y : Scheme.{u}}
  (i : Y ⟶ ProjectiveSpace A ι) [IsImmersion i] (F : Set ℚ[X])

/-- **The image over the base**: a closed subscheme of `Y_T` closed in `P_T` and its image in
`P_T` have the same image in `T`; the image is flat over `T` exactly when the subscheme is. -/
example {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of A))
    (V : (pullback (i ≫ toSpec A ι) g).IdealSheafData)
    [IsClosedImmersion (V.subschemeι ≫ immersionBaseChange i rfl g)] :
    Set.range ((V.map (immersionBaseChange i rfl g)).subschemeι ≫ pullback.snd (toSpec A ι) g) =
        Set.range (V.subschemeι ≫ pullback.snd (i ≫ toSpec A ι) g) ∧
      (IsProper ((V.map (immersionBaseChange i rfl g)).subschemeι ≫ pullback.snd (toSpec A ι) g) ↔
        IsProper (V.subschemeι ≫ pullback.snd (i ≫ toSpec A ι) g)) :=
  ⟨range_map_immersionBaseChange_subschemeι_comp_snd i rfl g V,
    map_immersionBaseChange_subschemeι_comp_snd_iff i rfl g V @IsProper⟩

/-- **A point of `Hilb^Φ_Y` with `Φ ≠ 0` covers its base**, and the fibre polynomial of the image
vanishes exactly off the image of the family. -/
example (n : ℕ) (e : ι ≃ Fin (n + 1)) {Φ : ℚ[X]} {T : Scheme.{u}}
    {g : T ⟶ Spec (CommRingCat.of A)} {V : (pullback (i ≫ toSpec A ι) g).IdealSheafData}
    (hV : IsImmersedHilbertFamily i rfl Φ g V) (hΦ : Φ ≠ 0) (t : T) :
    Surjective (V.subschemeι ≫ pullback.snd (i ≫ toSpec A ι) g) ∧
      (fiberHilbertPolynomialAt ι g (V.map (immersionBaseChange i rfl g)).quotientModule t ≠ 0 ↔
        t ∈ Set.range (V.subschemeι ≫ pullback.snd (i ≫ toSpec A ι) g)) :=
  have := hV.isClosedImmersion
  ⟨hV.surjective_of_ne_zero n e hΦ,
    fiberHilbertPolynomialAt_map_immersionBaseChange_ne_zero_iff i rfl g V n e t⟩

/-- **Points with Hilbert polynomials in `F`**: closed in `P_T`, with flat image, stable under base
change, and surjective onto the base when `0 ∉ F`. -/
example [Finite ι] (n : ℕ) (e : ι ≃ Fin (n + 1)) {T T' : Scheme.{u}}
    {g : T ⟶ Spec (CommRingCat.of A)} {g' : T' ⟶ Spec (CommRingCat.of A)} (f : T' ⟶ T)
    (h : f ≫ g = g') {V : (pullback (i ≫ toSpec A ι) g).IdealSheafData}
    (hV : IsImmersedHilbertFamilyIn i rfl F g V) (h0 : (0 : ℚ[X]) ∉ F) :
    IsClosedImmersion (V.subschemeι ≫ immersionBaseChange i rfl g) ∧
      Flat ((V.map (immersionBaseChange i rfl g)).subschemeι ≫ pullback.snd (toSpec A ι) g) ∧
      IsImmersedHilbertFamilyIn i rfl F g' (V.comap (pullback.map (i ≫ toSpec A ι) g'
        (i ≫ toSpec A ι) g (𝟙 Y) f (𝟙 _) (by simp) (by rw [Category.comp_id, h]))) ∧
      Surjective (V.subschemeι ≫ pullback.snd (i ≫ toSpec A ι) g) :=
  ⟨hV.isClosedImmersion, hV.flat_map, hV.comap f h, hV.surjective_of_zero_notMem n e h0⟩

/-- **For a single polynomial** the points with polynomials in `{Φ}` are the points of
`Hilb^Φ_Y`; a point of `Hilb^Φ_Y` with `Φ ∈ F` has polynomials in `F`. -/
example [Finite ι] {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of A))
    (V : (pullback (i ≫ toSpec A ι) g).IdealSheafData) (Φ : ℚ[X]) (hΦ : Φ ∈ F) :
    (IsImmersedHilbertFamilyIn i rfl {Φ} g V ↔ IsImmersedHilbertFamily i rfl Φ g V) ∧
      (IsImmersedHilbertFamily i rfl Φ g V → IsImmersedHilbertFamilyIn i rfl F g V) :=
  ⟨isImmersedHilbertFamilyIn_singleton_iff i rfl g V Φ,
    fun hV => hV.isImmersedHilbertFamilyIn_of_mem hΦ⟩

/-- **The functor** acts by pullback along `Y_{T'} ⟶ Y_T`, on all schemes over `Spec A`. -/
example [Finite ι] {T T' : (Over (Spec (CommRingCat.of A)))ᵒᵖ} (f : T ⟶ T')
    (V : (immersedHilbertFunctorIn i rfl F).obj T) :
    ((immersedHilbertFunctorIn i rfl F).map f V).1 =
      V.1.comap (pullback.map (i ≫ toSpec A ι) T'.unop.hom (i ≫ toSpec A ι) T.unop.hom (𝟙 Y)
        f.unop.left (𝟙 _) (by simp) (by rw [Category.comp_id, Over.w f.unop])) :=
  immersedHilbertFunctorIn_map_coe i rfl F f V

/-- **The polynomials that occur**: a proper flat closed subscheme is a point with polynomials in
the set of fibre polynomials of its image, finite over a quasi-compact locally Noetherian base and
omitting `0` exactly when the family covers the base. -/
example (n : ℕ) (e : ι ≃ Fin (n + 1)) {T : Scheme.{u}} [IsLocallyNoetherian T] [CompactSpace T]
    (g : T ⟶ Spec (CommRingCat.of A)) (V : (pullback (i ≫ toSpec A ι) g).IdealSheafData)
    (hp : IsProper (V.subschemeι ≫ pullback.snd (i ≫ toSpec A ι) g))
    (hf : Flat (V.subschemeι ≫ pullback.snd (i ≫ toSpec A ι) g)) :
    IsImmersedHilbertFamilyIn i rfl (Set.range (fiberHilbertPolynomialAt ι g
        (V.map (immersionBaseChange i rfl g)).quotientModule)) g V ∧
      (Set.range (fiberHilbertPolynomialAt ι g
        (V.map (immersionBaseChange i rfl g)).quotientModule)).Finite ∧
      ((0 : ℚ[X]) ∉ Set.range (fiberHilbertPolynomialAt ι g
          (V.map (immersionBaseChange i rfl g)).quotientModule) ↔
        Surjective (V.subschemeι ≫ pullback.snd (i ≫ toSpec A ι) g)) :=
  have hV := isImmersedHilbertFamilyIn_range_fiberHilbertPolynomialAt i rfl g V hp hf
  have := hV.isClosedImmersion
  ⟨hV, finite_range_fiberHilbertPolynomialAt_map_immersionBaseChange i rfl g V n e,
    zero_notMem_range_fiberHilbertPolynomialAt_map_immersionBaseChange_iff i rfl g V n e⟩

variable {J : Type} {H : J → Scheme.{u}} (πH : ∀ j, H j ⟶ Spec (CommRingCat.of A))
  (D : ∀ j, (pullback (i ≫ toSpec A ι) (πH j)).IdealSheafData)

/-- **The glued image**: the image of the glued family is the glued family of the images. -/
example [Finite ι] (hD : ∀ j, IsProper ((D j).subschemeι ≫ pullback.snd (i ≫ toSpec A ι) (πH j))) :
    (Scheme.IdealSheafData.sigmaGlue (i ≫ toSpec A ι) πH D).map
        (immersionBaseChange i rfl (Sigma.desc πH)) =
      Scheme.IdealSheafData.sigmaGlue (toSpec A ι) πH
        fun j => (D j).map (immersionBaseChange i rfl (πH j)) :=
  map_sigmaGlue_immersionBaseChange i rfl πH D hD

/-- **Glued points**: the family glued from points of `Hilb^{Φ j}_Y` with `Φ j ∈ F` has
polynomials in `F`, and for distinct `Φ j` its pullback detects the components. -/
example [Finite ι] (Φ : J → ℚ[X]) (hΦF : ∀ j, Φ j ∈ F) (hΦ : Function.Injective Φ)
    (hD : ∀ j, IsImmersedHilbertFamily i rfl (Φ j) (πH j) (D j)) {T : Scheme.{u}}
    (g : T ⟶ Spec (CommRingCat.of A)) (a : T ⟶ ∐ H) (ha : a ≫ Sigma.desc πH = g) (t : T)
    (j : J) :
    IsImmersedHilbertFamilyIn i rfl F (Sigma.desc πH)
        (Scheme.IdealSheafData.sigmaGlue (i ≫ toSpec A ι) πH D) ∧
      (fiberHilbertPolynomialAt ι g (((Scheme.IdealSheafData.sigmaGlue (i ≫ toSpec A ι) πH D).comap
          (pullback.map (i ≫ toSpec A ι) g (i ≫ toSpec A ι) (Sigma.desc πH) (𝟙 Y) a (𝟙 _)
            (by simp) (by rw [Category.comp_id, ha]))).map
              (immersionBaseChange i rfl g)).quotientModule t = Φ j ↔
        a t ∈ Set.range (Sigma.ι H j)) :=
  ⟨isImmersedHilbertFamilyIn_sigmaGlue i rfl πH D Φ hΦF hD,
    fiberHilbertPolynomialAt_map_comap_sigmaGlue_eq_iff i rfl πH D Φ hΦ hD g a ha t j⟩

/--
info: 'AlgebraicGeometry.ProjectiveSpace.immersedHilbertFunctorIn' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.immersedHilbertFunctorIn

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsImmersedHilbertFamilyIn.comap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.IsImmersedHilbertFamilyIn.comap

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsImmersedHilbertFamilyIn.surjective_of_zero_notMem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.IsImmersedHilbertFamilyIn.surjective_of_zero_notMem

/--
info: 'AlgebraicGeometry.ProjectiveSpace.isImmersedHilbertFamilyIn_singleton_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.isImmersedHilbertFamilyIn_singleton_iff

/--
info: 'AlgebraicGeometry.ProjectiveSpace.range_map_immersionBaseChange_subschemeι_comp_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.range_map_immersionBaseChange_subschemeι_comp_snd

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsImmersedHilbertFamily.surjective_of_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.IsImmersedHilbertFamily.surjective_of_ne_zero

/--
info: 'AlgebraicGeometry.ProjectiveSpace.fiberHilbertPolynomialAt_map_immersionBaseChange_ne_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.ProjectiveSpace.fiberHilbertPolynomialAt_map_immersionBaseChange_ne_zero_iff

/--
info: 'AlgebraicGeometry.ProjectiveSpace.map_sigmaGlue_immersionBaseChange' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.map_sigmaGlue_immersionBaseChange

/--
info: 'AlgebraicGeometry.ProjectiveSpace.isImmersedHilbertFamilyIn_sigmaGlue' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.isImmersedHilbertFamilyIn_sigmaGlue

/--
info: 'AlgebraicGeometry.ProjectiveSpace.fiberHilbertPolynomialAt_map_comap_sigmaGlue_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.fiberHilbertPolynomialAt_map_comap_sigmaGlue_eq_iff

/--
info: 'AlgebraicGeometry.ProjectiveSpace.finite_range_fiberHilbertPolynomialAt_map_immersionBaseChange' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.ProjectiveSpace.finite_range_fiberHilbertPolynomialAt_map_immersionBaseChange

/--
info: 'AlgebraicGeometry.ProjectiveSpace.zero_notMem_range_fiberHilbertPolynomialAt_map_immersionBaseChange_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.ProjectiveSpace.zero_notMem_range_fiberHilbertPolynomialAt_map_immersionBaseChange_iff
