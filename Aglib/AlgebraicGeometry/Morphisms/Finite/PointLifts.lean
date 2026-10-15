/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.FieldTheory.Minpoly.Field

/-!
# Finiteness of field-valued lifts through a finite scheme morphism

A finite scheme morphism has finitely many lifts of any field-valued point.
The field need not be closed, and the morphism need not be etale or surjective.

Source: R5Lab/AlgebraicGeometry/FiniteEtale/Fiber.lean
at R5 revision 2f9ca464b192cff865858dda70b2d8e5dca8b3df.
SHA256: 2ea7277dcd82b233b4ecada3e0aa91cd6099a8e7704248b807eb140af8f12355
Selection: finite_hom_over_field and finite_hom_over_point only; no etale condition is used.
Actual objects, maps, universes and hypotheses are retained.
-/
@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u

namespace AlgebraicGeometry.Scheme.Finite

/-- A finite scheme over a field has finitely many sections over that field.
The proof injects sections into homomorphisms from the finite-dimensional
global-section algebra; no étale or closed-field hypothesis is used. -/
lemma finite_hom_over_field {K : Type u} [Field K] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of K)) [IsFinite f] :
    Finite (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk f) := by
  let : IsAffine Y := isAffine_of_isAffineHom f
  let a : K →+* Γ(Y, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop).hom
  let : Algebra K Γ(Y, ⊤) := a.toAlgebra
  have ha : a.Finite := by
    exact (IsFinite.finite_app f ⊤ (isAffineOpen_top _)).comp
      (RingHom.Finite.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2)
  let : Module.Finite K Γ(Y, ⊤) := ha
  let toAlg : (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk f) →
      (Γ(Y, ⊤) →ₐ[K] K) := fun p =>
    { toRingHom := (p.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom
      commutes' := fun k => by
        have hp : p.left ≫ f = 𝟙 _ := Over.w p
        have he : ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop) ≫
            (p.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom) =
              𝟙 (CommRingCat.of K) := by
          rw [Category.assoc, ← Category.assoc f.appTop p.left.appTop,
            ← Scheme.Hom.comp_appTop, hp]
          simp
        exact congrArg (fun h : CommRingCat.of K ⟶ CommRingCat.of K => h.hom k) he }
  exact Finite.of_injective toAlg (by
    intro p q h
    apply Over.OverMorphism.ext
    apply ext_of_isAffine (Y := Y)
    apply (cancel_mono (Scheme.ΓSpecIso (CommRingCat.of K)).hom).mp
    exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom h))

/-- Every finite scheme morphism has finitely many lifts of a field-valued point. -/
lemma finite_hom_over_point {X Y : Scheme.{u}} {K : Type u} [Field K]
    (f : Y ⟶ X) [IsFinite f] (x : Spec (CommRingCat.of K) ⟶ X) :
    Finite (Over.mk x ⟶ Over.mk f) := by
  let : Finite (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ (Over.pullback x).obj (Over.mk f)) :=
    finite_hom_over_field (pullback.snd f x)
  have h := Finite.of_equiv
    (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ (Over.pullback x).obj (Over.mk f))
    ((Over.mapPullbackAdj x).homEquiv (Over.mk (𝟙 (Spec (CommRingCat.of K)))) (Over.mk f)).symm
  change Finite (Over.mk (𝟙 (Spec (CommRingCat.of K)) ≫ x) ⟶ Over.mk f) at h
  simpa only [Category.id_comp] using h

end AlgebraicGeometry.Scheme.Finite
