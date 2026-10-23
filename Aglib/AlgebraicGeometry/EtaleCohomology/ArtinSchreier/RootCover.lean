/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Etale.ArtinSchreier
public import Aglib.AlgebraicGeometry.Group.RootsFiniteEtale
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-!
# Actual finite etale Artin--Schreier root covers

Every global function acquires a solution of `b^p - b = a` on the actual
polynomial cover pulled back along `X.toSpecΓ`. This cover is finite,
surjective, and etale when `p = 0` in the global sections of the base.
The construction permits arbitrary schemes and the empty scheme.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
open _root_.Algebra.ArtinSchreier

namespace AlgebraicGeometry.Scheme.EtaleCohomology.ArtinSchreier

universe u

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]

/-- The actual polynomial root cover, obtained by base change from global sections. -/
def scheme (a : Γ(X, ⊤)) : Over X :=
  Over.mk (pullback.fst X.toSpecΓ
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤) (RootAlgebra p a)))))

instance scheme_finite (a : Γ(X, ⊤)) : IsFinite (scheme X p a).hom := by
  have : IsFinite (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, ⊤) (RootAlgebra p a)))) := by
    rw [IsFinite.SpecMap_iff]
    change (algebraMap Γ(X, ⊤) (RootAlgebra p a)).Finite
    rw [RingHom.finite_algebraMap]
    infer_instance
  exact inferInstanceAs (IsFinite (pullback.fst _ _))

lemma scheme_etale (a : Γ(X, ⊤)) (hp : (p : Γ(X, ⊤)) = 0) :
    Etale (scheme X p a).hom := by
  have := rootAlgebra_etale_of_cast_eq_zero p a hp
  have : Etale (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, ⊤) (RootAlgebra p a)))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    change (algebraMap Γ(X, ⊤) (RootAlgebra p a)).Etale
    rw [RingHom.etale_algebraMap]
    infer_instance
  exact inferInstanceAs (Etale (pullback.fst _ _))

instance scheme_surjective (a : Γ(X, ⊤)) : Surjective (scheme X p a).hom := by
  have : Surjective (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, ⊤) (RootAlgebra p a)))) :=
    ⟨spectrum_surjective p a⟩
  exact inferInstanceAs (Surjective (pullback.fst _ _))

/-- The original quotient algebra maps to the global functions of its actual cover. -/
def rootRingMap (a : Γ(X, ⊤)) : RootAlgebra p a →+* Γ((scheme X p a).left, ⊤) :=
  Group.RootsFiniteEtale.schemeHomRingEquiv _ _ (pullback.snd _ _)

omit [Fact p.Prime] in
lemma rootRingMap_comp (a : Γ(X, ⊤)) :
    (rootRingMap X p a).comp (algebraMap Γ(X, ⊤) (RootAlgebra p a)) =
      (scheme X p a).hom.appTop.hom := by
  rw [rootRingMap, ← Group.RootsFiniteEtale.schemeHomRingEquiv_spec,
    ← pullback.condition, Group.RootsFiniteEtale.schemeHomRingEquiv_comp,
    Group.RootsFiniteEtale.schemeHomRingEquiv_toSpecΓ, RingHom.comp_id]
  rfl

/-- The actual distinguished global section of the polynomial cover. -/
def rootSection (a : Γ(X, ⊤)) : Γ((scheme X p a).left, ⊤) :=
  rootRingMap X p a (AdjoinRoot.root (poly p a))

omit [Fact p.Prime] in
lemma rootSection_relation (a : Γ(X, ⊤)) :
    rootSection X p a ^ p - rootSection X p a = (scheme X p a).hom.appTop.hom a := by
  change (rootRingMap X p a) _ ^ p - (rootRingMap X p a) _ = _
  rw [← map_pow, ← map_sub, _root_.Algebra.ArtinSchreier.root_relation]
  exact DFunLike.congr_fun (rootRingMap_comp X p a) a

/-- Every global function acquires an Artin--Schreier root on a finite etale surjective cover. -/
theorem exists_finiteEtale_root (a : Γ(X, ⊤)) (hp : (p : Γ(X, ⊤)) = 0) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X), IsFinite f ∧ Etale f ∧ Surjective f ∧
      ∃ b : Γ(Y, ⊤), b ^ p - b = f.appTop.hom a :=
  ⟨(scheme X p a).left, (scheme X p a).hom, inferInstance, scheme_etale X p a hp,
    inferInstance, rootSection X p a, rootSection_relation X p a⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.ArtinSchreier
