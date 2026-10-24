/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Tangent.StructureCohomology

/-! Focused consumer of the tangent space at the unit of the Picard scheme (Kleiman,
arXiv:math/0504020v1, Thm 5.11, p. 42): for `X` proper and flat over a field with geometrically
integral fibres and a representation `e` of `Pic_{X/k,(fppf)}` on locally Noetherian test schemes,
`ker(F(k[ε]) → F(k)) ≃ₗ[k] H^1(X, 𝒪_X)`, its Zariski form, the dimension formula, Kleiman's `v`
and the field-extension step; axiom guards. -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing AlgebraicGeometry Scheme
open AlgebraicGeometry.Scheme.OverField AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.Scheme.RelativePicard

universe u

variable {k : Type u} [Field k] (X : FScheme k) [IsProper X.hom] [Flat X.hom]
  [GeometricallyIntegral X.hom] {P : LocallyNoetherianOver (Spec (.of k))}
  (e : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- **`T_0 Pic_{X/k} = H^1(X, 𝒪_X)`**, `k`-linearly for `a • t = F(µ_a) t`. -/
example :
    letI := tangentKernelModule e k
    tangentKernel (fppfPicardSheaf X.hom).obj k ≃ₗ[k] structureCohomology k X 1 :=
  tangentKernelLinearEquivStructureCohomologyOfIsProperOfFlatOfGeometricallyIntegral X e

/-- The scalar action on the tangent kernel is `F(µ_a)`, independently of `e`. -/
example (a : k) (t : tangentKernel (fppfPicardSheaf X.hom).obj k) :
    letI := tangentKernelModule e k
    a • t = squareZeroKernelMap (fppfPicardSheaf X.hom).obj (a • LinearMap.id) t :=
  rfl

/-- The inverse is Kleiman's `v` on the cover by all affine opens. -/
example [X.left.IsSeparated] (c : structureCohomology k X 1) :
    ((tangentKernelLinearEquivStructureCohomologyOfIsProperOfFlatOfGeometricallyIntegral
        X e).symm c :
        (fppfPicardSheaf X.hom).obj.obj (op (specOver k (TrivSqZeroExt k k)))) =
      (DualNumbers.cohomologyToFppfPicardKer X (fun j : X.left.affineOpens => (j : X.left.Opens))
        (iSup_affineOpens_eq_top _) (fun j => j.2) c :
        (fppfPicardSheaf X.hom).obj.obj (op (Over.mk (DualNumbers.dualMap k)))) :=
  tangentKernelLinearEquivStructureCohomologyOfIsProperOfFlatOfGeometricallyIntegral_symm_apply
    X e c

/-- The Zariski form: `(𝔪/𝔪²)^∨ ≃ₗ[k] H^1(X, 𝒪_X)`. -/
example : Module.Dual k (CotangentSpace (unitStalk e)) ≃ₗ[k] structureCohomology k X 1 :=
  cotangentSpaceDualLinearEquivStructureCohomologyOfIsProperOfFlatOfGeometricallyIntegral X e

/-- `dim_k H^1(X, 𝒪_X)` is the embedding dimension of `P` at the unit. -/
example : Module.finrank k (structureCohomology k X 1) =
    Module.finrank k (CotangentSpace (unitStalk e)) :=
  finrank_structureH1_eq_finrank_cotangentSpace_of_isProper_of_flat_of_geometricallyIntegral X e

/-- Kleiman's `v` on any affine cover is injective and bijective. -/
example [X.left.IsSeparated] {ι : Type u} (U : ι → X.left.Opens) (hU : iSup U = ⊤)
    (hU₁ : ∀ j, IsAffineOpen (U j)) :
    Function.Bijective (structureCohomologyToTangentKernel X e U hU hU₁) :=
  structureCohomologyToTangentKernel_bijective_of_isProper_of_flat_of_geometricallyIntegral
    X e U hU hU₁

/-- The field-extension step: with a section of `X_K ⟶ Spec K`,
`ker(F(K[ε]) → F(K)) ≃ₗ[K] H^1(X_K, 𝒪)`. -/
example (K : Type u) [Field K] [Algebra k K] [IsSplitEpi (fieldBaseChange K X).hom]
    [(fieldBaseChange K X).left.IsSeparated] {ι : Type u}
    (U : ι → (fieldBaseChange K X).left.Opens) (hU : iSup U = ⊤)
    (hU₁ : ∀ j, IsAffineOpen (U j)) :
    letI := tangentKernelModule e K
    tangentKernel (fppfPicardSheaf X.hom).obj K ≃ₗ[K]
      structureCohomology K (fieldBaseChange K X) 1 :=
  tangentKernelLinearEquivFieldBaseChangeOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral
    X e K U hU hU₁

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.tangentKernelLinearEquivStructureCohomologyOfIsProperOfFlatOfGeometricallyIntegral' depends
  on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms tangentKernelLinearEquivStructureCohomologyOfIsProperOfFlatOfGeometricallyIntegral

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.cotangentSpaceDualLinearEquivStructureCohomologyOfIsProperOfFlatOfGeometricallyIntegral'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cotangentSpaceDualLinearEquivStructureCohomologyOfIsProperOfFlatOfGeometricallyIntegral

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.structureCohomologyToTangentKernel_bijective_of_isProper_of_flat_of_geometricallyIntegral'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms structureCohomologyToTangentKernel_bijective_of_isProper_of_flat_of_geometricallyIntegral
