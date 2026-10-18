/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdjoinRootNestedBaseChange

/-!
# Coefficient equivalences of literal scalar branches

An equivalence of coefficient algebras transports every monic irreducible
branch by the literal polynomial coefficient map. The native equivalence of
root quotients preserves the original lower root-field algebra structures.
-/

@[expose] public noncomputable section

open Polynomial

namespace AdjoinRoot

variable {k A B : Type*} [Field k] [Field A] [Field B]
  [Algebra k A] [Algebra k B]

/-- Coefficient transport of one literal scalar branch. -/
def scalarBranchCoefficientMap (ε : A ≃ₐ[k] B) (h : k[X])
    (r : IrreducibleBranch (h.map (algebraMap k A))) :
    IrreducibleBranch (h.map (algebraMap k B)) := by
  refine ⟨⟨r.val.val.map ε.toRingHom, r.val.property.1.map _, ?_⟩, ?_⟩
  · exact r.val.property.2.map (Polynomial.mapEquiv ε.toRingEquiv)
  · have hd := Polynomial.map_dvd ε.toRingHom r.property
    have he : (h.map (algebraMap k A)).map ε.toRingHom =
        h.map (algebraMap k B) := by
      rw [Polynomial.map_map]
      congr 1
      ext a
      exact ε.commutes a
    rwa [he] at hd

/-- Coefficient equivalence bijects all literal monic irreducible branches. -/
def scalarBranchCoefficientEquiv (ε : A ≃ₐ[k] B) (h : k[X]) :
    IrreducibleBranch (h.map (algebraMap k A)) ≃
      IrreducibleBranch (h.map (algebraMap k B)) where
  toFun := scalarBranchCoefficientMap ε h
  invFun := scalarBranchCoefficientMap ε.symm h
  left_inv r := by
    apply Subtype.ext
    apply Subtype.ext
    change (r.val.val.map ε.toRingHom).map ε.symm.toRingHom = r.val.val
    rw [Polynomial.map_map]
    have he : ε.symm.toRingHom.comp ε.toRingHom = RingHom.id A := by
      ext a
      exact ε.symm_apply_apply a
    rw [he, Polynomial.map_id]
  right_inv r := by
    apply Subtype.ext
    apply Subtype.ext
    change (r.val.val.map ε.symm.toRingHom).map ε.toRingHom = r.val.val
    rw [Polynomial.map_map]
    have he : ε.toRingHom.comp ε.symm.toRingHom = RingHom.id B := by
      ext b
      exact ε.apply_symm_apply b
    rw [he, Polynomial.map_id]

@[simp]
theorem scalarBranchCoefficientEquiv_val (ε : A ≃ₐ[k] B) (h : k[X])
    (r : IrreducibleBranch (h.map (algebraMap k A))) :
    (scalarBranchCoefficientEquiv ε h r).val.val = r.val.val.map ε.toRingHom := rfl

attribute [local instance] scalarBranchAlgebra

/-- The native root equivalence preserves the original lower root-field action. -/
def scalarBranchCoefficientAlgEquiv (ε : A ≃ₐ[k] B) (h : k[X])
    [Fact (Irreducible h)] (r : IrreducibleBranch (h.map (algebraMap k A))) :
    AdjoinRoot r.val.val ≃ₐ[AdjoinRoot h]
      AdjoinRoot (scalarBranchCoefficientEquiv ε h r).val.val :=
  { mapRingEquiv ε.toRingEquiv r.val.val (r.val.val.map ε.toRingHom)
      (Associated.refl _) with
    commutes' := by
      intro x
      have he :
          (mapRingEquiv ε.toRingEquiv r.val.val (r.val.val.map ε.toRingHom)
            (Associated.refl _)).toRingHom.comp
              (Polynomial.LocalResidue.adjoinRootMap (algebraMap k A) h r.val.val
                r.property) =
            Polynomial.LocalResidue.adjoinRootMap (algebraMap k B) h
              (scalarBranchCoefficientEquiv ε h r).val.val
                (scalarBranchCoefficientEquiv ε h r).property := by
        apply AdjoinRoot.ringHom_ext
        · apply RingHom.ext
          intro a
          change map ε.toRingHom r.val.val (r.val.val.map ε.toRingHom) dvd_rfl
            (Polynomial.LocalResidue.adjoinRootMap (algebraMap k A) h r.val.val
              r.property (algebraMap k (AdjoinRoot h) a)) =
            Polynomial.LocalResidue.adjoinRootMap (algebraMap k B) h
              (scalarBranchCoefficientEquiv ε h r).val.val
                (scalarBranchCoefficientEquiv ε h r).property
                  (algebraMap k (AdjoinRoot h) a)
          rw [Polynomial.LocalResidue.adjoinRootMap_algebraMap,
            Polynomial.LocalResidue.adjoinRootMap_algebraMap]
          change map ε.toRingHom r.val.val (r.val.val.map ε.toRingHom) dvd_rfl
            (of r.val.val (algebraMap k A a)) =
              of (r.val.val.map ε.toRingHom) (algebraMap k B a)
          rw [map_of]
          exact congrArg (of (r.val.val.map ε.toRingHom)) (ε.commutes a)
        · change map ε.toRingHom r.val.val (r.val.val.map ε.toRingHom) dvd_rfl
            (Polynomial.LocalResidue.adjoinRootMap (algebraMap k A) h r.val.val
              r.property (root h)) =
            Polynomial.LocalResidue.adjoinRootMap (algebraMap k B) h
              (scalarBranchCoefficientEquiv ε h r).val.val
                (scalarBranchCoefficientEquiv ε h r).property (root h)
          rw [Polynomial.LocalResidue.adjoinRootMap_root,
            Polynomial.LocalResidue.adjoinRootMap_root, map_root]
          rfl
      exact RingHom.congr_fun he x }

/-- No quotient equivalence is replaced: the underlying map is the native map. -/
theorem scalarBranchCoefficientAlgEquiv_toRingHom (ε : A ≃ₐ[k] B) (h : k[X])
    [Fact (Irreducible h)] (r : IrreducibleBranch (h.map (algebraMap k A))) :
    (scalarBranchCoefficientAlgEquiv ε h r).toRingHom =
      (mapRingEquiv ε.toRingEquiv r.val.val (r.val.val.map ε.toRingHom)
        (Associated.refl _)).toRingHom := rfl

theorem scalarBranchCoefficientAlgEquiv_root (ε : A ≃ₐ[k] B) (h : k[X])
    [Fact (Irreducible h)] (r : IrreducibleBranch (h.map (algebraMap k A))) :
    scalarBranchCoefficientAlgEquiv ε h r (root r.val.val) =
      root (scalarBranchCoefficientEquiv ε h r).val.val :=
  map_root ε.toRingHom r.val.val (r.val.val.map ε.toRingHom) dvd_rfl

theorem scalarBranchCoefficientAlgEquiv_algebraMap (ε : A ≃ₐ[k] B) (h : k[X])
    [Fact (Irreducible h)] (r : IrreducibleBranch (h.map (algebraMap k A))) (a : A) :
    scalarBranchCoefficientAlgEquiv ε h r (algebraMap A (AdjoinRoot r.val.val) a) =
      algebraMap B (AdjoinRoot (scalarBranchCoefficientEquiv ε h r).val.val) (ε a) :=
  map_of ε.toRingHom r.val.val (r.val.val.map ε.toRingHom) dvd_rfl a

end AdjoinRoot
