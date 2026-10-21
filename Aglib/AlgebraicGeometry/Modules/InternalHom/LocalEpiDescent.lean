/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.Gluing

/-! # Descent forced by original local epimorphisms -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules.InternalHom

universe u v
variable {X : Scheme.{u}} {ι : Type v}
  (Y : ι → Scheme.{u}) (a : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (a i)]
  (hcover : ∀ x : X, ∃ (i : ι) (y : Y i), a i y = x)
  {M P N : X.Modules} (p : M ⟶ P) (t : M ⟶ N)
  (q : ∀ i, P.restrict (a i) ⟶ N.restrict (a i))
  [∀ i, Epi ((restrictFunctor (a i)).map p)]
  (hq : ∀ i, (restrictFunctor (a i)).map p ≫ q i = (restrictFunctor (a i)).map t)

include p t hq in
/-- Original local factorizations through epimorphisms automatically agree
on overlaps. No independent coefficient-map cocycle is assumed. -/
theorem restrictionHomCompatible_of_local_epi : RestrictionHomCompatible a P N q := by
  intro i k
  let L := restrictFunctor (pullback.fst (a i) (a k))
  let R := restrictFunctor (pullback.snd (a i) (a k))
  let e := overlapRestrictIso (a i) (a k)
  have hp : L.map ((restrictFunctor (a i)).map p) ≫ e.hom.app P =
      e.hom.app M ≫ R.map ((restrictFunctor (a k)).map p) := e.hom.naturality p
  have ht : L.map ((restrictFunctor (a i)).map t) ≫ e.hom.app N =
      e.hom.app M ≫ R.map ((restrictFunctor (a k)).map t) := e.hom.naturality t
  apply (cancel_epi (L.map ((restrictFunctor (a i)).map p))).mp
  change L.map ((restrictFunctor (a i)).map p) ≫ (L.map (q i) ≫ e.hom.app N) =
    L.map ((restrictFunctor (a i)).map p) ≫ (e.hom.app P ≫ R.map (q k))
  rw [← Category.assoc, ← L.map_comp, hq i, ht, ← Category.assoc, hp,
    Category.assoc, ← R.map_comp, hq k]

include hcover hq in
/-- Local original factorizations through an epimorphism produce an actual
global factorization with the unchanged local maps. -/
theorem exists_factorization_of_local_epi :
    ∃ g : P ⟶ N, p ≫ g = t ∧ ∀ i, (restrictFunctor (a i)).map g = q i := by
  let hcomp := restrictionHomCompatible_of_local_epi Y a p t q hq
  let g := glueRestrictionHom Y a hcover P N q hcomp
  have hg (i : ι) : (restrictFunctor (a i)).map g = q i :=
    glueRestrictionHom_restrict Y a hcover P N q hcomp i
  refine ⟨g, ?_, hg⟩
  have htcomp : RestrictionHomCompatible a M N (fun i => (restrictFunctor (a i)).map t) := by
    intro i k
    exact (overlapRestrictIso (a i) (a k)).hom.naturality t
  exact (glueRestrictionHom_unique Y a hcover M N _ htcomp (p ≫ g) (by
      intro i
      rw [Functor.map_comp, hg, hq])).trans
    (glueRestrictionHom_unique Y a hcover M N _ htcomp t (by intro i; rfl)).symm

end AlgebraicGeometry.Scheme.Modules.InternalHom
