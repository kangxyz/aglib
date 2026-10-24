/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.HilbertScheme.Immersed.Fiber

/-! Focused consumer of the Hilbert polynomials of the fibres of closed subschemes of an embedded
family `X ⊆ P^N_A`: the cartesian fibre square at a field point, the fibre of the image as the
image of the fibre, the Hilbert polynomial of a fibre as `χ(X_x, O(n)) − χ(X_x, I_{V_x}(n))`, the
flat case with the pulled-back ideal, the polynomial `ψ − φ₀`, and the instantiation at a residue
field, with axiom guards. -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Cohomology
open scoped Polynomial

universe u

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}} (i : X ⟶ ProjectiveSpace A ι)
  {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of A))

/-- The fibre `X_x` of `X_T` at a field point is the base change of `X_T ⟶ P_T` along
`P^N_K ⟶ P_T`, for any `i`. -/
example {K : Type u} [Field K] (x : Spec (CommRingCat.of K) ⟶ T) :
    IsPullback (pullback.map (i ≫ toSpec A ι) (x ≫ g) (i ≫ toSpec A ι) g (𝟙 X) x (𝟙 _)
        (by simp) (by simp))
      (Scheme.Cohomology.embeddedFiberι i (x ≫ g)) (immersionBaseChange i rfl g)
      (pointMap ι g x) :=
  isPullback_embeddedFiberι_pointMap i g x

/-- For a closed immersion `i`, the fibre of the image of any closed subscheme `V ⊆ X_T` is the
image of its fibre, and its Hilbert polynomial is that of the pushforward of `𝒪_{V_x}`. -/
example [IsClosedImmersion i] (V : (pullback (i ≫ toSpec A ι) g).IdealSheafData) {K : Type u}
    [Field K] (x : Spec (CommRingCat.of K) ⟶ T) :
    (V.map (immersionBaseChange i rfl g)).comap (pointMap ι g x) =
        (V.comap (pullback.map (i ≫ toSpec A ι) (x ≫ g) (i ≫ toSpec A ι) g (𝟙 X) x (𝟙 _)
          (by simp) (by simp))).map (Scheme.Cohomology.embeddedFiberι i (x ≫ g)) ∧
      subschemeHilbertPolynomial ι K
          ((V.map (immersionBaseChange i rfl g)).comap (pointMap ι g x)) =
        projectiveHilbertPolynomial K ι
          ((Scheme.Modules.pushforward (Scheme.Cohomology.embeddedFiberι i (x ≫ g))).obj
            (V.comap (pullback.map (i ≫ toSpec A ι) (x ≫ g) (i ≫ toSpec A ι) g (𝟙 X) x (𝟙 _)
              (by simp) (by simp))).quotientModule) :=
  ⟨comap_pointMap_map_immersionBaseChange i g x V,
    subschemeHilbertPolynomial_comap_pointMap_map_immersionBaseChange i g x V⟩

/-- **The Hilbert polynomial of a fibre** is `χ(X_x, O(n)) − χ(X_x, I_{V_x}(n))`, for any closed
subscheme `V ⊆ X_T` and the ideal of its fibre. -/
example [IsClosedImmersion i] (N : ℕ) (e : ι ≃ Fin (N + 1))
    (V : (pullback (i ≫ toSpec A ι) g).IdealSheafData) {K : Type u} [Field K]
    (x : Spec (CommRingCat.of K) ⟶ T) (n : ℤ) :
    (subschemeHilbertPolynomial ι K
        ((V.map (immersionBaseChange i rfl g)).comap (pointMap ι g x))).eval (n : ℚ) =
      (embeddedFiberTwistEulerChar i (x ≫ g) (SheafOfModules.unit _) n : ℚ) -
        embeddedFiberTwistEulerChar i (x ≫ g)
          (Scheme.Hom.idealModule (V.comap (pullback.map (i ≫ toSpec A ι) (x ≫ g)
            (i ≫ toSpec A ι) g (𝟙 X) x (𝟙 _) (by simp) (by simp))).subschemeι) n :=
  eval_subschemeHilbertPolynomial_comap_pointMap_map_immersionBaseChange i g x N e V n

/-- **Flat families**: the image is flat, the ideal of the fibre is the pulled-back ideal, and the
Hilbert polynomial of a fibre is `χ(X_x, O(n)) − χ(X_x, (b_x^* I_V)(n))`. -/
example [IsClosedImmersion i] (N : ℕ) (e : ι ≃ Fin (N + 1))
    (V : (pullback (i ≫ toSpec A ι) g).IdealSheafData)
    [Flat (V.subschemeι ≫ pullback.snd (i ≫ toSpec A ι) g)] {K : Type u} [Field K]
    (x : Spec (CommRingCat.of K) ⟶ T) (n : ℤ) :
    Flat ((V.map (immersionBaseChange i rfl g)).subschemeι ≫ pullback.snd (toSpec A ι) g) ∧
      Nonempty ((Scheme.Modules.pullback (pullback.map (i ≫ toSpec A ι) (x ≫ g) (i ≫ toSpec A ι)
          g (𝟙 X) x (𝟙 _) (by simp) (by simp))).obj (Scheme.Hom.idealModule V.subschemeι) ≅
        Scheme.Hom.idealModule (V.comap (pullback.map (i ≫ toSpec A ι) (x ≫ g) (i ≫ toSpec A ι)
          g (𝟙 X) x (𝟙 _) (by simp) (by simp))).subschemeι) ∧
      (subschemeHilbertPolynomial ι K
          ((V.map (immersionBaseChange i rfl g)).comap (pointMap ι g x))).eval (n : ℚ) =
        (embeddedFiberTwistEulerChar i (x ≫ g) (SheafOfModules.unit _) n : ℚ) -
          embeddedFiberTwistEulerChar i (x ≫ g)
            ((Scheme.Modules.pullback (pullback.map (i ≫ toSpec A ι) (x ≫ g) (i ≫ toSpec A ι) g
              (𝟙 X) x (𝟙 _) (by simp) (by simp))).obj (Scheme.Hom.idealModule V.subschemeι)) n :=
  ⟨flat_map_immersionBaseChange_subschemeι_comp_snd i g rfl V,
    ⟨fieldPointIdealPullbackIso i g x V⟩,
    eval_subschemeHilbertPolynomial_comap_pointMap_map_immersionBaseChange_of_flat i g x V N e n⟩

/-- **The polynomial `ψ − φ₀` at a residue field**: the variable-field statement instantiated at
`Spec κ(t) ⟶ T`, whose base-change map is `residueFieldBaseChange`. -/
example [IsClosedImmersion i] (N : ℕ) (e : ι ≃ Fin (N + 1))
    (V : (pullback (i ≫ toSpec A ι) g).IdealSheafData)
    [Flat (V.subschemeι ≫ pullback.snd (i ≫ toSpec A ι) g)] (t : T) {ψ φ₀ : ℚ[X]}
    (hψ : ∀ n : ℤ, (embeddedFiberTwistEulerChar i (K := T.residueField t)
      (T.fromSpecResidueField t ≫ g) (SheafOfModules.unit _) n : ℚ) = ψ.eval (n : ℚ))
    (hφ₀ : ∀ n : ℤ, (embeddedFiberTwistEulerChar i (K := T.residueField t)
      (T.fromSpecResidueField t ≫ g)
      ((Scheme.Modules.pullback (residueFieldBaseChange (i ≫ toSpec A ι) g t)).obj
        (Scheme.Hom.idealModule V.subschemeι)) n : ℚ) = φ₀.eval (n : ℚ)) :
    subschemeHilbertPolynomial ι (T.residueField t)
      ((V.map (immersionBaseChange i rfl g)).comap (pointMap ι g (T.fromSpecResidueField t))) =
        ψ - φ₀ :=
  subschemeHilbertPolynomial_comap_pointMap_map_immersionBaseChange_eq_sub i g
    (T.fromSpecResidueField t) V N e hψ hφ₀

/--
info: 'AlgebraicGeometry.ProjectiveSpace.isPullback_embeddedFiberι_pointMap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isPullback_embeddedFiberι_pointMap

/--
info: 'AlgebraicGeometry.ProjectiveSpace.comap_pointMap_map_immersionBaseChange' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms comap_pointMap_map_immersionBaseChange

/--
info: 'AlgebraicGeometry.ProjectiveSpace.isClosedImmersion_comap_subschemeι_comp_embeddedFiberι' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isClosedImmersion_comap_subschemeι_comp_embeddedFiberι

/--
info: 'AlgebraicGeometry.ProjectiveSpace.subschemeHilbertPolynomial_comap_pointMap_map_immersionBaseChange' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms subschemeHilbertPolynomial_comap_pointMap_map_immersionBaseChange

/--
info: 'AlgebraicGeometry.ProjectiveSpace.eval_subschemeHilbertPolynomial_comap_pointMap_map_immersionBaseChange' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms eval_subschemeHilbertPolynomial_comap_pointMap_map_immersionBaseChange

/--
info: 'AlgebraicGeometry.ProjectiveSpace.flat_map_immersionBaseChange_subschemeι_comp_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms flat_map_immersionBaseChange_subschemeι_comp_snd

/--
info: 'AlgebraicGeometry.ProjectiveSpace.isIso_idealPullbackMap_fieldPoint' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isIso_idealPullbackMap_fieldPoint

/--
info: 'AlgebraicGeometry.ProjectiveSpace.fieldPointIdealPullbackIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fieldPointIdealPullbackIso

/--
info: 'AlgebraicGeometry.ProjectiveSpace.eval_subschemeHilbertPolynomial_comap_pointMap_map_immersionBaseChange_of_flat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms eval_subschemeHilbertPolynomial_comap_pointMap_map_immersionBaseChange_of_flat

/--
info: 'AlgebraicGeometry.ProjectiveSpace.subschemeHilbertPolynomial_comap_pointMap_map_immersionBaseChange_eq_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms subschemeHilbertPolynomial_comap_pointMap_map_immersionBaseChange_eq_sub
