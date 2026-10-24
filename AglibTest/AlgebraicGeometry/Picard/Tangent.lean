/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Picard.Tangent.DualNumbers

/-! Focused consumer of the tangent-space algebra of the Picard functor
(Kleiman, arXiv:math/0504020v1, Thm 5.11). For a split square-zero thickening with an ideal
generator, and in particular for `X[ε] = X ×_{Spec k} Spec k[ε]`, the truncated exponential
sequence `0 → 𝒪_X → 𝒪_{X[ε]}^* → 𝒪_X^* → 1`, `b ↦ 1 + b ε`, is short exact and split,
unit cohomology splits in every degree, `Pic(X[ε]) ≃+ Pic(X) × ker(i^*)` through the
retraction, and a unit-cohomology comparison identifies `ker(i^*)` with `H^1(X, 𝒪_X)`. -/

@[expose] public section

noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.SplitThickening Scheme.Modules.Invertible Scheme.Modules.Invertible.PullbackTensor.Local

universe u

section Thickening

variable {X Y : Scheme.{u}} (i : X ⟶ Y) (p : Y ⟶ X) (h : i ≫ p = 𝟙 X)

example (G : IdealGenerator i p h) : G.unitsComplex.ShortExact := G.unitsComplex_shortExact

example (G : IdealGenerator i p h) : G.unitsComplex.Splitting := G.unitsSplitting

example (G : IdealGenerator i p h) (U : X.Opensᵒᵖ) (a : Γ(X, U.unop)) :
    ((G.oneAddMap.hom.app U a).toMul : (Γ(Y, p ⁻¹ᵁ U.unop))ˣ).val =
      1 + restrictTop p G.ε U.unop * (p.app U.unop).hom a :=
  G.oneAddMap_app_apply U a

example (G : IdealGenerator i p h) (n : ℕ) :
    Sheaf.H (ringSheaf p).units n ≃+
      Sheaf.H (idealSheaf i p h) n × Sheaf.H X.sheaf.units n :=
  unitsCohomologyEquiv i p h G.reduction_ker_sq n

example : PicardGroup Y ≃+ PicardGroup X × (pullbackHom i).ker := picardRetractionEquiv i p h

example (G : IdealGenerator i p h) (C : UnitsCohomologyComparison i p h) :
    (pullbackHom i).ker ≃+ Sheaf.H (Scheme.structureAddSheaf X) 1 :=
  G.picardKerEquiv C

end Thickening

section DualNumbers

variable (k : Type u) [CommRing k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

example : (Scheme.DualNumbers.dualIdealGenerator k sX).unitsComplex.ShortExact :=
  Scheme.DualNumbers.unitsComplex_shortExact k sX

example (n : ℕ) :
    Sheaf.H (ringSheaf (Scheme.DualNumbers.projection k sX)).units n ≃+
      Sheaf.H (Scheme.structureAddSheaf X) n × Sheaf.H X.sheaf.units n :=
  Scheme.DualNumbers.unitsCohomologyEquiv k sX n

example (n : ℕ) :
    (Sheaf.H.map (Sheaf.unitsMap (reduction (Scheme.DualNumbers.inclusion k sX)
      (Scheme.DualNumbers.projection k sX) (Scheme.DualNumbers.inclusion_projection k sX)))
        n).ker ≃+ Sheaf.H (Scheme.structureAddSheaf X) n :=
  Scheme.DualNumbers.unitsCohomologyKerEquiv k sX n

example (C : UnitsCohomologyComparison (Scheme.DualNumbers.inclusion k sX)
      (Scheme.DualNumbers.projection k sX) (Scheme.DualNumbers.inclusion_projection k sX)) :
    PicardGroup (Scheme.DualNumbers.dualScheme k sX) ≃+
      PicardGroup X × Sheaf.H (Scheme.structureAddSheaf X) 1 :=
  Scheme.DualNumbers.picardEquiv k sX C

end DualNumbers

/--
info: 'AlgebraicGeometry.Scheme.DualNumbers.unitsComplex_shortExact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Scheme.DualNumbers.unitsComplex_shortExact

/--
info: 'AlgebraicGeometry.Scheme.DualNumbers.unitsCohomologyEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Scheme.DualNumbers.unitsCohomologyEquiv

/--
info: 'AlgebraicGeometry.Scheme.DualNumbers.unitsCohomologyKerEquiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Scheme.DualNumbers.unitsCohomologyKerEquiv

/--
info: 'AlgebraicGeometry.Scheme.DualNumbers.picardEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Scheme.DualNumbers.picardEquiv

/--
info: 'AlgebraicGeometry.Scheme.SplitThickening.IdealGenerator.picardEquiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms IdealGenerator.picardEquiv

/--
info: 'AlgebraicGeometry.Scheme.SplitThickening.picardRetractionEquiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms picardRetractionEquiv
