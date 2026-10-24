/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Scheme.FieldProperties

/-!
# Consumer checks for the Picard scheme over a field

For a closed subscheme `X` of `P^N_k`, flat with geometrically integral fibres, and its Picard
scheme `picardScheme h` (Kleiman, *The Picard scheme*, arXiv:math/0504020v1, Thm 4.8): the fit of
the group law and of the identity component at `picardScheme h`, the object `Over.mk p`, the
tangent space at the unit `T_0 = H^1(X, 𝒪_X)` (Thm 5.11, p. 42) and its Zariski form, the unit
point, `Pic⁰_{X/k}` (Prop. 5.3, p. 37) and its formation under field extension, with the target-5
proof `Strata.fineStrataRepresentableByHQuasiProjective i e`; axiom guards.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.OverField AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.Scheme.RelativePicard AlgebraicGeometry.Scheme.RelativePicard.Strata
open AlgebraicGeometry.Scheme.Group

universe u

namespace AglibTest.PicardSchemeFieldProperties

variable {k : Type u} [Field k] {ι : Type u} {X : Scheme.{u}}
  {i : X ⟶ ProjectiveSpace k ι} [IsClosedImmersion i] [Flat (i ≫ toSpec k ι)]
  [GeometricallyIntegral (i ≫ toSpec k ι)] {N : ℕ} {e : ι ≃ Fin (N + 1)}
  (h : FineStrataRepresentableByHQuasiProjective i N e)

/-- The object `Over.mk p`: its structure morphism is `p` and its scheme is `X`, by definition. -/
example : (Over.mk (i ≫ toSpec k ι) : FScheme k).hom = i ≫ toSpec k ι :=
  rfl

example : (Over.mk (i ≫ toSpec k ι) : FScheme k).left = X :=
  rfl

/-- Properness of `p` from the closed immersion. -/
example (e : ι ≃ Fin (N + 1)) : IsProper (Over.mk (i ≫ toSpec k ι) : FScheme k).hom :=
  isProper_comp_toSpec_of_isClosedImmersion i e

/-- Fit test: with `letI` of the group law of `picardScheme h`, the group structure of its identity
component is found by instance search. -/
example :
    letI := picardCommGrpObj (i ≫ toSpec k ι) (picardScheme h) (picardSchemeRepresentableBy h)
    GrpObj (identityComponentOver (picardScheme h).obj) := by
  let := picardCommGrpObj (i ≫ toSpec k ι) (picardScheme h) (picardSchemeRepresentableBy h)
  infer_instance

/-- `Pic⁰_{X/k}` of the Picard scheme is a group scheme, by instance search. -/
example :
    GrpObj (picardIdentityComponent (i ≫ toSpec k ι) (picardScheme h)
      (picardSchemeRepresentableBy h)) :=
  inferInstance

/-- **`T_0 Pic_{X/k} = H^1(X, 𝒪_X)`** at the Picard scheme, `k`-linearly for `a • t = F(µ_a) t`. -/
example :
    letI := tangentKernelModule (picardSchemeRepresentableBy h) k
    tangentKernel (fppfPicardSheaf (i ≫ toSpec k ι)).obj k ≃ₗ[k]
      structureCohomology k (Over.mk (i ≫ toSpec k ι)) 1 :=
  picardSchemeTangentKernelLinearEquiv h

/-- The same with the target-5 proof: no premise beyond the setting. -/
example (e : ι ≃ Fin (N + 1)) :
    letI := tangentKernelModule
      (picardSchemeRepresentableBy (fineStrataRepresentableByHQuasiProjective i e)) k
    tangentKernel (fppfPicardSheaf (i ≫ toSpec k ι)).obj k ≃ₗ[k]
      structureCohomology k (Over.mk (i ≫ toSpec k ι)) 1 :=
  picardSchemeTangentKernelLinearEquiv (fineStrataRepresentableByHQuasiProjective i e)

/-- The Zariski form: `(𝔪/𝔪²)^∨ ≃ₗ[k] H^1(X, 𝒪_X)` at the unit point of the Picard scheme. -/
example :
    letI := unitStalkAlgebra (picardSchemeRepresentableBy h)
    Module.Dual k (CotangentSpace (unitStalk (picardSchemeRepresentableBy h))) ≃ₗ[k]
      structureCohomology k (Over.mk (i ≫ toSpec k ι)) 1 :=
  picardSchemeCotangentSpaceDualLinearEquiv h

/-- The point of the Zariski form is the unit point of the group law. -/
example :
    unitPoint (picardSchemeRepresentableBy h) =
      (letI := picardCommGrpObj (i ≫ toSpec k ι) (picardScheme h)
          (picardSchemeRepresentableBy h);
        Group.unitPoint (picardScheme h).obj) :=
  unitPoint_eq_unitPoint_picardCommGrpObj _ _ _

/-- `H^1(X, 𝒪_X)` is finite-dimensional, by transport of `finite_tangentKernel`. -/
example : Module.Finite k (structureCohomology k (Over.mk (i ≫ toSpec k ι)) 1) := by
  let := tangentKernelModule (picardSchemeRepresentableBy h) k
  have := finite_tangentKernel (picardSchemeRepresentableBy h) k
  exact Module.Finite.equiv (picardSchemeTangentKernelLinearEquiv h)

/-- **`Pic⁰_{X/k}` of the Picard scheme** (Kleiman, Prop. 5.3, p. 37): open and closed, a group
subscheme, of finite type, geometrically irreducible. -/
example :
    (letI := picardCommGrpObj (i ≫ toSpec k ι) (picardScheme h) (picardSchemeRepresentableBy h);
      IsClopen (identityComponent (picardScheme h).obj : Set (picardScheme h).obj.left) ∧
        IsMonHom (identityComponentι (picardScheme h).obj)) ∧
      QuasiCompact (picardIdentityComponent (i ≫ toSpec k ι) (picardScheme h)
        (picardSchemeRepresentableBy h)).hom ∧
      LocallyOfFiniteType (picardIdentityComponent (i ≫ toSpec k ι) (picardScheme h)
        (picardSchemeRepresentableBy h)).hom ∧
      GeometricallyIrreducible (picardIdentityComponent (i ≫ toSpec k ι) (picardScheme h)
        (picardSchemeRepresentableBy h)).hom :=
  ⟨⟨isClopen_picardIdentityComponent _ _ _, isMonHom_picardIdentityComponentι _ _ _⟩,
    inferInstance, inferInstance, inferInstance⟩

/-- **`Pic⁰` and field extension**: the identity component of the Picard scheme `P_K` of `X_K`,
for the group law of its representation by base change, is the preimage of `Pic⁰_{X/k}`. -/
example (K : Type u) [Field K] [Algebra k K] :
    (letI := picardCommGrpObj
        (pullback.snd (i ≫ toSpec k ι) (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        (LocallyNoetherianOver.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))
          (picardScheme h))
        (baseChangeRepresentableBy (i ≫ toSpec k ι)
          (Spec.map (CommRingCat.ofHom (algebraMap k K))) (picardScheme h)
          (picardSchemeRepresentableBy h));
      identityComponent (LocallyNoetherianOver.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) (picardScheme h)).obj) =
      pullback.fst (picardScheme h).obj.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⁻¹ᵁ
        (letI := picardCommGrpObj (i ≫ toSpec k ι) (picardScheme h)
            (picardSchemeRepresentableBy h);
          identityComponent (picardScheme h).obj) :=
  identityComponent_baseChangeRepresentableBy _ _ _ K

/-- `(Pic⁰_{X/k})_K ≅ Pic⁰_{X_K/K}` as schemes. -/
example (K : Type u) [Field K] [Algebra k K] :
    (pullback (picardIdentityComponent (i ≫ toSpec k ι) (picardScheme h)
        (picardSchemeRepresentableBy h)).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}) ≅
      (picardIdentityComponent
        (pullback.snd (i ≫ toSpec k ι) (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        (LocallyNoetherianOver.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))
          (picardScheme h))
        (baseChangeRepresentableBy (i ≫ toSpec k ι)
          (Spec.map (CommRingCat.ofHom (algebraMap k K))) (picardScheme h)
          (picardSchemeRepresentableBy h))).left :=
  picardIdentityComponentBaseChangeIso _ _ _ K

/-- The collected statement of target 6 over a field. -/
example (e : ι ≃ Fin (N + 1)) := exists_representableBy_fppfPicardSheaf_fieldProperties i e

end AglibTest.PicardSchemeFieldProperties

/--
info: 'AlgebraicGeometry.ProjectiveSpace.isProper_comp_toSpec_of_isClosedImmersion' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.isProper_comp_toSpec_of_isClosedImmersion

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.unitPoint_eq_unitPoint_picardCommGrpObj' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.unitPoint_eq_unitPoint_picardCommGrpObj

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.identityComponent_baseChangeRepresentableBy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.identityComponent_baseChangeRepresentableBy

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.picardIdentityComponentBaseChangeIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.picardIdentityComponentBaseChangeIso

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.picardSchemeTangentKernelLinearEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.picardSchemeTangentKernelLinearEquiv

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.picardSchemeCotangentSpaceDualLinearEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.picardSchemeCotangentSpaceDualLinearEquiv

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.exists_representableBy_fppfPicardSheaf_fieldProperties' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.exists_representableBy_fppfPicardSheaf_fieldProperties
