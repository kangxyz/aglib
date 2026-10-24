/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Picard.IdentityComponent

/-! Focused consumer of the identity component of a scheme representing the fppf Picard sheaf of
a scheme over a field on locally Noetherian test schemes (Kleiman, Prop. 5.3, p. 37), with the fit
test of the group law against the identity component, and axiom guards. -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry Scheme.RelativePicard Scheme.Group
open scoped CategoryTheory.MonObj CategoryTheory.Obj

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
  (P : Scheme.LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  (e : ((Scheme.locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf p).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- Fit test: with `S = Spec (.of k)` and the group law of the representing scheme, the group
structure of the identity component is found by instance search. -/
example : letI := picardCommGrpObj p P e; GrpObj (identityComponentOver P.obj) := by
  let := picardCommGrpObj p P e
  infer_instance

/-- With the group law, the identity component is geometrically irreducible and of finite type
by instance search. -/
example :
    letI := picardCommGrpObj p P e
    GeometricallyIrreducible (identityComponentOver P.obj).hom ∧
      QuasiCompact (identityComponentOver P.obj).hom ∧
      LocallyOfFiniteType (identityComponentOver P.obj).hom := by
  let := picardCommGrpObj p P e
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- `Pic⁰_{X/k}`: an open and closed group subscheme of finite type, geometrically irreducible
(Kleiman, Prop. 5.3, p. 37). -/
theorem picardIdentityComponent_properties :
    (letI := picardCommGrpObj p P e; IsClopen (identityComponent P.obj : Set P.obj.left)) ∧
      QuasiCompact (picardIdentityComponent p P e).hom ∧
      LocallyOfFiniteType (picardIdentityComponent p P e).hom ∧
      GeometricallyIrreducible (picardIdentityComponent p P e).hom :=
  ⟨isClopen_picardIdentityComponent p P e, inferInstance, inferInstance, inferInstance⟩

/-- `Pic⁰_{X/k}` is a group scheme and its inclusion is a monoid morphism. -/
example : GrpObj (picardIdentityComponent p P e) := inferInstance

example :
    letI := picardCommGrpObj p P e
    IsMonHom (picardIdentityComponentι p P e) :=
  isMonHom_picardIdentityComponentι p P e

/-- The identity component of the base change `P_K` is the preimage of `Pic⁰_{X/k}`. -/
example (K : Type u) [Field K] [Algebra k K] :
    letI := picardCommGrpObj p P e
    identityComponent ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj P.obj) =
      pullback.fst P.obj.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⁻¹ᵁ
        identityComponent P.obj :=
  picardIdentityComponent_pullback p P e K

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.geometricallyIrreducible_picardIdentityComponent_hom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.geometricallyIrreducible_picardIdentityComponent_hom

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.quasiCompact_picardIdentityComponent_hom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.quasiCompact_picardIdentityComponent_hom

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.picardIdentityComponent_pullback' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.picardIdentityComponent_pullback

/-- info: 'picardIdentityComponent_properties' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms picardIdentityComponent_properties
