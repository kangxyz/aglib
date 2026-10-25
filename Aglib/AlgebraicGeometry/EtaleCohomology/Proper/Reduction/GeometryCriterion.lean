/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Reduction.ChowGeometry
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.Finite
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.Surjective
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Geometric projective-line reduction through the original production maps

For an existing morphism property with the stated composition, base-change,
finite-map and proper-surjective descent rules, the original projective line
implies every original proper morphism over the fixed arbitrary spectrum.
The proof uses the original finite surjective binary-form multiplication and
the transported production Chow packet. This geometric criterion does not
assert those closure rules for a new base-change predicate.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction

universe u

variable (P : MorphismProperty Scheme.{u})
  [P.IsStableUnderComposition] [P.IsStableUnderBaseChange]
  (hfinite : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsFinite f → P f)
  (hdescent : ∀ {X Y S : Scheme.{u}} (f : X ⟶ S) (p : Y ⟶ X),
    IsProper f → IsProper p → Surjective p → P p → P (p ≫ f) → P f)
  (R : Type u) [CommRing R]
  (hline : P (ProjectiveLine.structureMap R))

include hfinite hline

/-- Finite products of the original projective line satisfy the specified
property by actual native product projections and the stated closure rules. -/
theorem binaryProductStructure_mem (n : ℕ) :
    P (ProjectiveSpace.BinaryFormProduct.structureMap R n) := by
  induction n with
  | zero =>
    change P (𝟙 (Spec (CommRingCat.of R)))
    exact hfinite _ inferInstance
  | succ n hn =>
    change P ((Over.mk (ProjectiveLine.structureMap R) ⨯
      ProjectiveSpace.BinaryFormProduct.product R n).hom)
    rw [Scheme.overProd_hom_eq]
    apply P.comp_mem
    · exact hfinite _ inferInstance
    · exact P.comp_mem _ _
        (MorphismProperty.pullback_fst (P := P) _ _ hn) hline

include hdescent

/-- The original finite surjective binary-form map reduces the original
standard projective-space projection to the original projective line. -/
theorem projectiveSpaceStructure_mem (n : ℕ) :
    P (ProjectiveSpace.toSpec R (ULift.{u} (Fin (n + 1)))) := by
  let p := ProjectiveSpace.BinaryFormProduct.multiplication R n
  let f := ProjectiveSpace.toSpec R (ULift.{u} (Fin (n + 1)))
  have hp : P p := hfinite p inferInstance
  have hc : P (p ≫ f) := by
    rw [ProjectiveSpace.BinaryFormProduct.multiplication_over]
    exact binaryProductStructure_mem P hfinite R hline n
  exact hdescent f p inferInstance inferInstance inferInstance hp hc

/-- The actual production Chow packet and original projective-line products
reduce the specified property to P1 for every proper morphism over an
arbitrary original spectrum. No Noetherian or finite-presentation premise occurs. -/
theorem proper_affine_mem_of_projectiveLine
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f] : P f := by
  obtain ⟨Y, p, m, j, hp, hs, hj, hbase⟩ := exists_projective_modification R f
  have : IsProper p := hp
  have : Surjective p := hs
  have : IsClosedImmersion j := hj
  let t := ProjectiveSpace.toSpec R (ULift.{u} (Fin (m + 1)))
  have ht : P t := projectiveSpaceStructure_mem P hfinite hdescent R hline m
  have hc : P (p ≫ f) := by
    rw [← hbase]
    exact P.comp_mem _ _ (hfinite j inferInstance) ht
  let a : Y ⟶ pullback f t := pullback.lift p j hbase.symm
  have haj_eq : a ≫ pullback.snd f t = j :=
    pullback.lift_snd p j hbase.symm
  have haj : IsClosedImmersion (a ≫ pullback.snd f t) := by
    rw [haj_eq]
    exact hj
  have : IsClosedImmersion a := IsClosedImmersion.of_comp a (pullback.snd f t)
  have ha : P a := hfinite a inferInstance
  have hπ : P (pullback.fst f t) := MorphismProperty.pullback_fst (P := P) f t ht
  have hpa : P p := by
    have h := P.comp_mem a (pullback.fst f t) ha hπ
    simpa only [a, pullback.lift_fst] using h
  exact hdescent f p inferInstance hp hs hpa hc

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction
