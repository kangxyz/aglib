/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Irreducibility under field extension

Let `k` be a field and `q : Y ⟶ Spec k` a scheme over `k`; write `Y_K` for the base change
`pullback q (Spec K ⟶ Spec k)` along a field extension `K` of `k`. This module proves:

* **irreducibility descends along field extensions**
  (`irreducibleSpace_pullback_of_irreducibleSpace_pullback_of_isScalarTower`): for fields
  `k ⊆ K ⊆ L`, if `Y_L` is irreducible then so is `Y_K`, because `Y_L ≅ (Y_K)_L` maps onto
  `Y_K` (`Spec L ⟶ Spec K` is surjective, and surjectivity is stable under base change);
* **geometric irreducibility from algebraically closed extensions**
  (`AlgebraicGeometry.Scheme.Geometrically.geometricallyIrreducible_of_forall_isAlgClosed`): if
  `Y_K` is irreducible for every algebraically closed field extension `K` of `k`, then `q` is
  geometrically irreducible in Mathlib's sense (`AlgebraicGeometry.GeometricallyIrreducible`).
  For an arbitrary extension `K`, the algebraic closure of `K` is such an extension.

No finiteness or separation hypothesis is used. The descent step is the surjectivity argument in
the proof of Stacks Project, Tag 054P; geometric irreducibility is Mathlib's form of Stacks 0365,
for extensions in the universe of `k`. The criterion asks for every algebraically closed extension
of `k`, not only for one algebraic closure. Consumer: the geometric irreducibility of the identity
component of a group scheme locally of finite type over a field
(`Aglib.AlgebraicGeometry.Group.IdentityComponent.FiniteType`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Geometrically

universe u

variable {k : Type u} [Field k] {Y : Scheme.{u}} (q : Y ⟶ Spec (.of k))

/-- **Irreducibility descends along field extensions**: for fields `k ⊆ K ⊆ L`, if the base
change of `Y` to `L` is irreducible, so is its base change to `K`. -/
theorem irreducibleSpace_pullback_of_irreducibleSpace_pullback_of_isScalarTower
    (K L : Type u) [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L]
    [IsScalarTower k K L]
    [IrreducibleSpace (pullback q (Spec.map (CommRingCat.ofHom (algebraMap k L))) : Scheme.{u})] :
    IrreducibleSpace (pullback q (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}) := by
  set bK := Spec.map (CommRingCat.ofHom (algebraMap k K))
  set c := Spec.map (CommRingCat.ofHom (algebraMap K L))
  have hc : Spec.map (CommRingCat.ofHom (algebraMap k L)) = c ≫ bK := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact IsScalarTower.algebraMap_apply k K L x
  have h₁ : IrreducibleSpace (pullback q (c ≫ bK) : Scheme.{u}) := by
    rw [← hc]
    infer_instance
  have h₂ : IrreducibleSpace (pullback (pullback.snd q bK) c : Scheme.{u}) :=
    (pullbackLeftPullbackSndIso q bK c).hom.homeomorph.irreducibleSpace_iff.mpr h₁
  have : Surjective c := ⟨Function.surjective_to_subsingleton _⟩
  exact Function.Surjective.irreducibleSpace (pullback.fst (pullback.snd q bK) c).continuous
    (pullback.fst (pullback.snd q bK) c).surjective

/-- **Geometric irreducibility from algebraically closed extensions**: if the base change of `Y`
to every algebraically closed field extension of `k` is irreducible, then `Y` is geometrically
irreducible over `k`. -/
theorem geometricallyIrreducible_of_forall_isAlgClosed
    (h : ∀ (K : Type u) [Field K] [Algebra k K] [IsAlgClosed K],
      IrreducibleSpace (pullback q (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u})) :
    GeometricallyIrreducible q := by
  constructor
  apply (geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
    (P := fun Z : Scheme.{u} => IrreducibleSpace Z) (R := k) (f := q)).mpr
  intro K _ _
  have := h (AlgebraicClosure K)
  exact irreducibleSpace_pullback_of_irreducibleSpace_pullback_of_isScalarTower q K
    (AlgebraicClosure K)

end AlgebraicGeometry.Scheme.Geometrically
