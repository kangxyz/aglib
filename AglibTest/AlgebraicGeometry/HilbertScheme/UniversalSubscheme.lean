/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.HilbertScheme.UniversalSubschemeGrassmannian

/-! Focused consumer of the universal closed subscheme over the Grassmannian (Nitsure,
arXiv:math/0504590v1, §5, pp. 26–27): the epimorphism onto the image ideal of a module-to-unit
map and its pullback without flatness, the closed subscheme `Z(K)` cut out by a subsheaf of the
free sheaf on the monomials, its base change, and the pullback of the universal subscheme along a
classifying map, with axiom guards. -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace

universe u

/-- For a quasi-coherent `M`, the factor `M ⟶ I(φ)` onto the image ideal is an epimorphism. -/
example {X : Scheme.{u}} {M : X.Modules} [M.IsQuasicoherent]
    (φ : M ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf)) :
    Epi (Scheme.Modules.Hom.zeroIdealFactor φ
      (Scheme.Modules.Hom.imageIdealLocalizes_of_isQuasicoherent φ)) :=
  Scheme.Modules.Hom.epi_zeroIdealFactor φ _

/-- **The image ideal commutes with every pullback**: `I(f^* φ) = I(φ).comap f`, no flatness. -/
example {X Y : Scheme.{u}} (f : Y ⟶ X) {M : X.Modules} [M.IsQuasicoherent]
    (φ : M ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf)) :
    Scheme.Modules.Hom.imageIdealData
        ((Scheme.Modules.pullback f).map φ ≫ (Scheme.Modules.pullbackUnitIso f).hom) =
      (Scheme.Modules.Hom.imageIdealData φ).comap f :=
  Scheme.Modules.Hom.imageIdealData_pullback f φ

/-- For the coordinate powers, the evaluation of homogeneous polynomials is the generating map
of `𝒪(r)`. -/
example {A : Type u} [CommRing A] (ι : Type u) (r : ℕ) :
    homogeneousEvaluation ι r (coordinatePower A ι r) = coordinatePowerGeneratingMap A ι r :=
  homogeneousEvaluation_coordinatePower ι r

/-- **Base change of `Z(ker q)`** for a rank-`k` locally free quotient `q` of the free sheaf on
the monomials. -/
example {A : Type u} [CommRing A] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1)) (r k : ℕ)
    {T T' : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of A)) (g' : T' ⟶ Spec (CommRingCat.of A))
    (f : T' ⟶ T) (h : f ≫ g = g') {Q : T.Modules}
    (q : SheafOfModules.free {a : ι →₀ ℕ // a.degree = r} ⟶ Q) [Epi q]
    (hQ : Scheme.Modules.SheafHasRank Q k) :
    (evaluationIdeal ι g r (monomialFamily ι r) (Limits.kernel.ι q)).comap
        (baseChangeMap ι g g' f h) =
      evaluationIdeal ι g' r (monomialFamily ι r)
        (Limits.kernel.ι ((Scheme.Modules.pullback f).map q) ≫
          (Scheme.Modules.pullbackFreeIso f _).hom) :=
  evaluationIdeal_kernel_comap_baseChangeMap ι r k _ _ (monomialsEquiv ι n e r) g g' f h q hQ

/-- **Base change of `Z(K)`** for a quasi-coherent subsheaf `K` of the free sheaf on the monomials
of degree `r`, along any `f : T' ⟶ T` over `Spec A`. -/
example {A : Type u} [CommRing A] (ι : Type u) {T T' : Scheme.{u}}
    (g : T ⟶ Spec (CommRingCat.of A)) (g' : T' ⟶ Spec (CommRingCat.of A)) (f : T' ⟶ T)
    (h : f ≫ g = g') (r : ℕ) {K : T.Modules} [K.IsQuasicoherent]
    (ιK : K ⟶ SheafOfModules.free {a : ι →₀ ℕ // a.degree = r}) :
    (evaluationIdeal ι g r (monomialFamily ι r) ιK).comap (baseChangeMap ι g g' f h) =
      evaluationIdeal ι g' r (monomialFamily ι r)
        ((Scheme.Modules.pullback f).map ιK ≫ (Scheme.Modules.pullbackFreeIso f _).hom) :=
  evaluationIdeal_comap_baseChangeMap ι g' f h r _ ιK

/-- **Pullback of the universal subscheme**: the universal subscheme over the Grassmannian of
rank-`k` quotients of the free sheaf on the monomials pulls back along the classifying map of a
quotient `q` to the subscheme cut out by `ker q`. -/
example {A : Type u} [CommRing A] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1)) (r k : ℕ)
    {T : Over (Spec (CommRingCat.of A))} {Q : T.left.Modules}
    (q : SheafOfModules.free {a : ι →₀ ℕ // a.degree = r} ⟶ Q) [Epi q]
    (hQ : Scheme.Modules.SheafHasRank Q k) :
    (universalHilbertSubscheme (A := A) ι r k n e).comap
        (baseChangeMap ι (Grassmannian.schemeOver (CommRingCat.of A) k ((n + r).choose r)).hom
          T.hom (Grassmannian.classifyingMap
            (Grassmannian.LocallyFreeQuotient.ofFree (monomialsEquiv ι n e r) q hQ)).left
          (Over.w _)) =
      evaluationIdeal ι T.hom r (monomialFamily ι r) (Limits.kernel.ι q) :=
  universalHilbertSubscheme_comap_classifyingMap ι r k n e q hQ

/--
info: 'AlgebraicGeometry.Scheme.Modules.Hom.epi_zeroIdealFactor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.Hom.epi_zeroIdealFactor

/--
info: 'AlgebraicGeometry.Scheme.Modules.Hom.imageIdealData_eq_of_epi_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.Hom.imageIdealData_eq_of_epi_comp

/--
info: 'AlgebraicGeometry.Scheme.Modules.Hom.imageIdealData_epi_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.Hom.imageIdealData_epi_comp

/--
info: 'AlgebraicGeometry.Scheme.Modules.Hom.imageIdealData_pullback' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.Hom.imageIdealData_pullback

/--
info: 'AlgebraicGeometry.Scheme.Modules.pullback_map_pullbackPairing' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.pullback_map_pullbackPairing

/--
info: 'AlgebraicGeometry.Scheme.Modules.pullbackPairingOf_pullback' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.pullbackPairingOf_pullback

/--
info: 'AlgebraicGeometry.Scheme.Modules.pullbackSquareIso_hom_freeTransfer' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.pullbackSquareIso_hom_freeTransfer

/--
info: 'AlgebraicGeometry.ProjectiveSpace.evaluationIdeal_eq_of_iso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.evaluationIdeal_eq_of_iso

/--
info: 'AlgebraicGeometry.ProjectiveSpace.evaluationIdeal_comap_baseChangeMap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.evaluationIdeal_comap_baseChangeMap

/--
info: 'AlgebraicGeometry.ProjectiveSpace.universalEvaluationIdeal_comap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.universalEvaluationIdeal_comap

/--
info: 'AlgebraicGeometry.ProjectiveSpace.universalEvaluationIdeal_comap_classifyingMap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.universalEvaluationIdeal_comap_classifyingMap

/--
info: 'AlgebraicGeometry.ProjectiveSpace.universalHilbertSubscheme_comap_classifyingMap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.universalHilbertSubscheme_comap_classifyingMap

/--
info: 'AlgebraicGeometry.ProjectiveSpace.evaluationIdeal_kernel_comap_baseChangeMap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.evaluationIdeal_kernel_comap_baseChangeMap
