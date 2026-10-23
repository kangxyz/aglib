/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Unramified.GaloisPoint
public import Aglib.AlgebraicGeometry.EtaleCohomology.StrictlyLocal.Site
public import Aglib.AlgebraicGeometry.FundamentalGroup.Field.ArbitraryGalois

/-!
# Finite Galois refinement of small-etale field covers

A nonempty affine chart of an actual etale cover has a point over a finite Galois
extension. Consequently every covering sieve of the original terminal small-etale
object contains the actual finite-field cover associated to some finite Galois
intermediate field of the separable closure. No field perfection is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Fields

universe u

open Scheme.FiniteEtale
open Scheme.FiniteEtale.FieldGalois.Arbitrary

variable (K : Type u) [Field K]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A nonempty etale scheme over a field has an actual point over a finite
Galois intermediate field of the separable closure. -/
theorem exists_finiteGalois_point {U : Scheme.{u}}
    (p : U ⟶ Spec (.of K)) [Etale p] (x : U) :
    ∃ (L : FiniteGaloisIntermediateField K (SeparableClosure K))
      (s : Spec (.of L) ⟶ U), s ≫ p = Spec.algebraMap K L := by
  obtain ⟨A, j, _, hj, _⟩ := exists_affine_mem_range_and_range_subset
    (x := x) (U := ⊤) (by simp)
  obtain ⟨a, _⟩ := hj
  let : Nontrivial A := a.nontrivial
  obtain ⟨g, hg⟩ := Spec.map_surjective (j ≫ p)
  let : Algebra K A := g.hom.toAlgebra
  have hcoord : Spec.algebraMap K A = j ≫ p := hg
  let : Algebra.Etale K A := by
    have he : Etale (Spec.algebraMap K A) := by
      rw [hcoord]
      infer_instance
    exact RingHom.etale_algebraMap.mp
      ((HasRingHomProperty.Spec_iff (P := @Etale.{u})).mp he)
  obtain ⟨L, ⟨b⟩⟩ := Algebra.FormallyUnramified.exists_finiteGalois_algHom K A
  refine ⟨L, Spec.map (CommRingCat.ofHom b.toRingHom) ≫ j, ?_⟩
  rw [Category.assoc, ← hcoord]
  exact Spec.map_algHom_algebraMap b

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Every covering sieve of the original terminal small-etale object contains
an actual finite Galois field cover. -/
theorem exists_finiteGalois_mem_covering_sieve
    (W : Sieve (StrictlyLocal.terminalObject K))
    (hW : W ∈ Scheme.smallEtaleTopology (Spec (.of K)) (StrictlyLocal.terminalObject K)) :
    ∃ L : FiniteGaloisIntermediateField K (SeparableClosure K),
      W ((StrictlyLocal.terminalIsTerminal K).from
        ((toEtale _).obj (finiteFieldCover K L))) := by
  obtain ⟨𝒰, hOver, hEtale, hle⟩ :=
    (Scheme.mem_smallGrothendieckTopology (StrictlyLocal.terminalObject K) W).mp hW
  let := hOver
  obtain ⟨i, y, _⟩ := 𝒰.exists_eq (default : Spec (.of K))
  have hstruct : 𝒰.f i = (𝒰.X i ↘ Spec (.of K)) := by
    have h := HomIsOver.comp_over (f := 𝒰.f i) (S := Spec (.of K))
    change 𝒰.f i ≫ 𝟙 (Spec (.of K)) = (𝒰.X i ↘ Spec (.of K)) at h
    exact (Category.comp_id (𝒰.f i : 𝒰.X i ⟶ Spec (.of K))).symm.trans h
  let : Etale (𝒰.f i) := by rw [hstruct]; exact hEtale i
  obtain ⟨L, s, hs⟩ := exists_finiteGalois_point K (𝒰.f i) y
  let V := (𝒰.X i).asOverProp (Spec (.of K)) (hEtale i)
  let f : V ⟶ StrictlyLocal.terminalObject K := (𝒰.f i).asOverProp (Spec (.of K))
  have hf : W f := hle _ _ ⟨i⟩
  let T := (toEtale _).obj (finiteFieldCover K L)
  let a : T ⟶ V := MorphismProperty.Over.homMk s (by
    change s ≫ (𝒰.X i ↘ Spec (.of K)) = Spec.algebraMap K L
    rw [← hstruct]
    exact hs)
  have h := W.downward_closed hf a
  have heq : a ≫ f = (StrictlyLocal.terminalIsTerminal K).from T :=
    (StrictlyLocal.terminalIsTerminal K).hom_ext _ _
  exact ⟨L, heq ▸ h⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Fields
