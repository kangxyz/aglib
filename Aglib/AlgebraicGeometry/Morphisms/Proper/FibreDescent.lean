/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Geometry.RingedSpace.Stalks
public import Mathlib.Topology.ContinuousMap.Basic

/-!
# Descent of an actual morphism constant on proper fibres

A proper surjection is a quotient on underlying topological spaces. If the
actual structure map `f.c` is invertible, its inverse descends the structural
map of any actual morphism constant on the point fibres. The descended map
on stalks is local because its composite with the original stalk map is local
and the source has a point over every target point.

Uniqueness compares the full structural map, cancelling the pushforward of
`f.c` after the underlying maps agree. No separation hypothesis on the target
of the descended morphism is needed.

This is the given-contraction universal-property step of Stacks Tag 0C5J;
it does not construct a contraction or prove a point-blowup factorization.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme

universe u

private theorem existsUnique_presheafedSpace_factor_of_isIso_c
    {X Y Z : PresheafedSpace CommRingCat.{u}} (f : X ⟶ Y) [IsIso f.c]
    (g : X ⟶ Z) (b : (Y : TopCat.{u}) ⟶ (Z : TopCat.{u}))
    (hb : f.base ≫ b = g.base) :
    ∃! h : Y ⟶ Z, h.base = b ∧ f ≫ h = g := by
  rcases g with ⟨gb, gc⟩
  change f.base ≫ b = gb at hb
  subst gb
  let P := TopCat.Presheaf.pushforward CommRingCat.{u} b
  let h : Y ⟶ Z := { base := b, c := gc ≫ P.map (inv f.c) }
  refine ⟨h, ⟨rfl, ?_⟩, ?_⟩
  · change ({ base := f.base ≫ b, c := (gc ≫ P.map (inv f.c)) ≫ P.map f.c } : X ⟶ Z) =
      { base := f.base ≫ b, c := gc }
    apply congrArg (fun c : Z.presheaf ⟶
      (TopCat.Presheaf.pushforward CommRingCat.{u} (f.base ≫ b)).obj X.presheaf =>
        ({ base := f.base ≫ b, c := c } : X ⟶ Z))
    erw [Category.assoc, ← P.map_comp, IsIso.inv_hom_id, P.map_id, Category.comp_id]
  · intro k hk
    rcases k with ⟨kb, kc⟩
    rcases hk with ⟨hkb, hkfac⟩
    change kb = b at hkb
    subst kb
    have hkc : kc ≫ P.map f.c = gc := by
      apply NatTrans.ext
      funext U
      change kc.app U ≫ f.c.app (op ((Opens.map b).obj (unop U))) = gc.app U
      have hu := PresheafedSpace.congr_app hkfac U
      erw [PresheafedSpace.comp_c_app, eqToHom_refl,
        CategoryTheory.Functor.map_id, Category.comp_id] at hu
      exact hu
    have hkc' : kc = gc ≫ P.map (inv f.c) := by
      calc
        kc = kc ≫ 𝟙 (P.obj Y.presheaf) := (Category.comp_id kc).symm
        _ = kc ≫ P.map f.c ≫ P.map (inv f.c) := by
          rw [← P.map_comp, IsIso.hom_inv_id, P.map_id]
        _ = gc ≫ P.map (inv f.c) := by rw [← Category.assoc, hkc]
    exact congrArg (fun c : Z.presheaf ⟶ P.obj Y.presheaf =>
      ({ base := b, c := c } : Y ⟶ Z)) hkc'

private theorem isLocalHom_stalkMap_of_surjective_factorization
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) [Surjective f] (g : X ⟶ Z)
    (h : Y.toPresheafedSpace ⟶ Z.toPresheafedSpace)
    (hfac : f.toPshHom ≫ h = g.toPshHom) :
    ∀ y : Y, IsLocalHom (h.stalkMap y).hom := by
  have hlocal : ∀ x : X, IsLocalHom ((f.toPshHom ≫ h).stalkMap x).hom := by
    rw [hfac]
    exact g.prop
  intro y
  obtain ⟨x, rfl⟩ := f.surjective y
  change IsLocalHom (h.stalkMap (f.toPshHom.base x)).hom
  let : IsLocalHom ((f.toPshHom.stalkMap x).hom.comp
      (h.stalkMap (f.toPshHom.base x)).hom) := by
    have hx := hlocal x
    rw [PresheafedSpace.stalkMap.comp] at hx
    simpa only [CommRingCat.hom_comp] using hx
  exact isLocalHom_of_comp (h.stalkMap (f.toPshHom.base x)).hom
    (f.toPshHom.stalkMap x).hom

/-- An actual morphism constant on the point fibres of a proper surjection
with invertible actual structure-sheaf map descends uniquely as a scheme morphism.
There are no Noetherian, normality or separation assumptions. -/
theorem existsUnique_factor_of_isProper_of_isIso_c
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [Surjective f] [IsIso f.c]
    (g : X ⟶ Z)
    (hconst : ∀ x₁ x₂ : X, f x₁ = f x₂ → g x₁ = g x₂) :
    ∃! h : Y ⟶ Z, f ≫ h = g := by
  have hquot : Topology.IsQuotientMap f.base.hom :=
    f.isClosedMap.isQuotientMap f.continuous f.surjective
  have hpoints : Function.FactorsThrough g f := fun {_ _} h => hconst _ _ h
  let b : Y.carrier ⟶ Z.carrier := TopCat.ofHom (hquot.lift g.base.hom hpoints)
  have hb : f.base ≫ b = g.base := by
    ext x
    exact DFunLike.congr_fun (hquot.lift_comp g.base.hom hpoints) x
  obtain ⟨hP, ⟨_, hPfac⟩, hPunique⟩ :=
    existsUnique_presheafedSpace_factor_of_isIso_c f.toPshHom g.toPshHom b hb
  let h : Y ⟶ Z :=
    ⟨{ toHom := hP
       prop := isLocalHom_stalkMap_of_surjective_factorization f g hP hPfac }⟩
  have hfac : f ≫ h = g := by
    apply Scheme.Hom.ext'
    apply LocallyRingedSpace.Hom.ext'
    exact hPfac
  refine ⟨h, hfac, ?_⟩
  intro k hk
  apply Scheme.Hom.ext'
  apply LocallyRingedSpace.Hom.ext'
  apply hPunique k.toPshHom
  refine ⟨?_, ?_⟩
  · ext y
    obtain ⟨x, rfl⟩ := f.surjective y
    have hkx : k (f x) = g x := congrArg (fun t : X ⟶ Z => t x) hk
    have hbx : b (f x) = g x := congrArg (fun t : X.carrier ⟶ Z.carrier => t x) hb
    exact hkx.trans hbx.symm
  · exact congrArg (fun t : X ⟶ Z => t.toPshHom) hk

end AlgebraicGeometry.Scheme
