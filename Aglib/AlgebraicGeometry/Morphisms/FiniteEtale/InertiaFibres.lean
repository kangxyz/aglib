/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralClosure.Inertia.FixesPoints
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Adic.Fullness
public import Aglib.AlgebraicGeometry.FundamentalGroup.Field.Basic

/-!
# Inertia fixes geometric points of extending finite-etale covers

A finite-etale cover extending over Spec R has its actual generic Omega-points fixed by the
specified integral-closure inertia.

Source: `R5Lab.Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.InertiaFibres`, frozen R5
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`3f122dd1160ace5d4c3af2af51a812bd410338a5e3d887550e3ffa81396a9d6e`. Selected lines: [[25, 89]].
The actual objects, canonical maps, universes and stated premises are retained.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber baseChange baseChangeComp)
open _root_.AlgebraicGeometry.Scheme.FiniteEtale
open AlgebraicGeometry.Scheme.FiniteEtale.Adic
open integralClosure.Inertia

namespace AlgebraicGeometry.Scheme.FiniteEtale.Inertia
universe u
variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]

/-- The actual action on every geometric point of a cover extending over the
trait is trivial on integral-closure inertia. -/
theorem inertia_fixes_traitPoint (Q : Ideal (IntegralModel R K)) [Q.IsPrime]
    (γ : inertia R K Q) (Y : Scheme.FiniteEtale (Spec (.of R)))
    (p : Spec (.of (AlgebraicClosure K)) ⟶ Y.obj.left)
    (hp : p ≫ Y.obj.hom = Spec.algebraMap R (AlgebraicClosure K)) :
    Spec.map (CommRingCat.ofHom (galoisAutomorphism γ.val).toRingHom) ≫ p = p := by
  let : Algebra R (sections R Y) := sectionsAlgebra R Y
  let q := p ≫ Y.obj.left.isoSpec.hom
  have hq : q ≫ Spec.algebraMap R (sections R Y) =
      Spec.algebraMap R (AlgebraicClosure K) := by
    rw [← sections_over R Y]
    simpa [q] using hp
  let f : sections R Y →ₐ[R] AlgebraicClosure K := Spec.homEquivAlgHom ⟨q, hq⟩
  have hf : Spec.map (CommRingCat.ofHom f.toRingHom) = q :=
    congrArg Subtype.val (Spec.homEquivAlgHom.symm_apply_apply ⟨q, hq⟩)
  apply (cancel_mono Y.obj.left.isoSpec.hom).mp
  change Spec.map _ ≫ q = q
  rw [← hf, ← Spec.map_comp]
  congr 1
  ext a
  exact inertia_fixes_algHom Q γ f a

/-- The canonical algebraic-closure point factors through the actual base algebra. -/
theorem geometricPoint_comp_algebraMap :
    FieldGalois.geometricPoint K ≫ Spec.algebraMap R K =
      Spec.algebraMap R (AlgebraicClosure K) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1

/-- The actual field Galois action on a generic fibre of a trait cover is
trivial on the actual integral-closure inertia subgroup. -/
theorem inertia_fixes_genericFiber (Q : Ideal (IntegralModel R K)) [Q.IsPrime]
    (γ : inertia R K Q) (Y : Scheme.FiniteEtale (Spec (.of R)))
    (t : Fiber (FieldGalois.geometricPoint K)
      ((baseChange (Spec.algebraMap R K)).obj Y)) :
    FieldGalois.pointEnd K γ.val ≫ t = t := by
  have ht : t.left ≫ pullback.snd Y.obj.hom (Spec.algebraMap R K) =
      FieldGalois.geometricPoint K := Over.w t
  have hf := inertia_fixes_traitPoint Q γ Y
    (t.left ≫ pullback.fst Y.obj.hom (Spec.algebraMap R K)) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, ht,
        geometricPoint_comp_algebraMap])
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change (Spec.map _ ≫ t.left) ≫ pullback.fst Y.obj.hom (Spec.algebraMap R K) =
      t.left ≫ pullback.fst Y.obj.hom (Spec.algebraMap R K)
    simpa only [Category.assoc] using hf
  · change (Spec.map _ ≫ t.left) ≫ pullback.snd Y.obj.hom (Spec.algebraMap R K) =
      t.left ≫ pullback.snd Y.obj.hom (Spec.algebraMap R K)
    rw [Category.assoc, ht]
    exact Over.w (FieldGalois.pointEnd K γ.val)

/-- A cover of the original scheme extends over every displayed trait map;
the canonical pullback-composition isomorphism preserves its actual points. -/
theorem inertia_fixes_globalGenericFiber (Q : Ideal (IntegralModel R K)) [Q.IsPrime]
    (γ : inertia R K Q) {X : Scheme.{u}} (m : Spec (.of R) ⟶ X)
    (j : Spec (.of K) ⟶ X) (hj : j = Spec.algebraMap R K ≫ m) (Y : Scheme.FiniteEtale X)
    (t : Fiber (FieldGalois.geometricPoint K) ((baseChange j).obj Y)) :
    FieldGalois.pointEnd K γ.val ≫ t = t := by
  subst j
  let e := (baseChangeComp m (Spec.algebraMap R K)).app Y
  have h := inertia_fixes_genericFiber Q γ ((baseChange m).obj Y) (t ≫ e.hom.hom)
  apply (cancel_mono e.hom.hom).mp
  simpa only [Category.assoc] using h

end AlgebraicGeometry.Scheme.FiniteEtale.Inertia
