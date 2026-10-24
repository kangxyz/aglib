/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Tangent.Cech.Equiv
public import Aglib.AlgebraicGeometry.Picard.Tangent.DualNumbers
public import Aglib.AlgebraicGeometry.Cohomology.Cech.DegreeOnePairs
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.CechComparison

/-!
# The kernel of `Pic X[ε] → Pic X` is `H^1(X, 𝒪_X)`, by Čech cocycles

Let `X[ε] = X ×_{Spec k} Spec k[ε]` with closed fibre `i : X ⟶ X[ε]` (`DualNumbers.inclusion`).

* `DualNumbers.picardKerEquivPairCohomology`: for a commutative ring `k`, a scheme `X` over
  `Spec k` and a cover `U` of `X` by affine opens with affine pairwise intersections,
  `ker(i^* : Pic X[ε] → Pic X)` is the pair cohomology of `𝒪_X` on `U`; the class of a pair
  cocycle `b` corresponds to the line bundle glued from the transition units `1 + ε b`.
* `DualNumbers.picardKerEquivCech`: for a field `k`, `X : FScheme k` separated and a cover `U`
  of `X` by affine opens, `ker(i^* : Pic X[ε] → Pic X) ≃+ H^1(X, 𝒪_X)`
  (`structureCohomology k X 1`), through the Čech comparison
  `Cohomology.structureCechCohomologyLinearEquiv`. This has the type of the conditional
  `DualNumbers.picardKerEquiv` and needs no unit-cohomology comparison.

Kleiman's Square (5.11.4) (arXiv:math/0504020v1, proof of Thm 5.11, p. 43) has top row
`H^1(𝒪^*_{X_ε}) → H^1(𝒪^*_X)` and tacitly identifies it with `Pic(X_ε) → Pic(X)`. Here the
kernel of `Pic(X_ε) → Pic(X)` is computed directly by Čech cocycles on a fixed affine cover
(compare Stacks, Tag 0B8R, for torsors trivial on a cover). No finiteness of the cover is
needed.
-/

@[expose] public section

noncomputable section


open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Modules.Invertible.PullbackTensor.Local

universe u

namespace AlgebraicGeometry.Scheme.DualNumbers

section Ring

variable (k : Type u) [CommRing k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

-- The base-change stability of `IsAffineHom` is found only after unfolding the property.
set_option backward.isDefEq.respectTransparency false in
/-- The projection `X[ε] ⟶ X` is affine, as a base change of `Spec k[ε] ⟶ Spec k`. -/
instance isAffineHom_projection : IsAffineHom (projection k sX) :=
  MorphismProperty.pullback_fst _ _ inferInstance

variable {ι : Type u} (U : ι → X.Opens) (hU : iSup U = ⊤) (hU₁ : ∀ j, IsAffineOpen (U j))
  (hU₂ : ∀ j l, IsAffineOpen (U j ⊓ U l))

/-- `ker(i^* : Pic X[ε] → Pic X)` is the pair cohomology of `𝒪_X` on a cover by affine opens
with affine pairwise intersections. -/
def picardKerEquivPairCohomology : (pullbackHom (inclusion k sX)).ker ≃+ PairCohomology U :=
  ((dualIdealGenerator k sX).pairCohomologyEquivKer U hU hU₁ (fun j => (hU₁ j).preimage _)
    hU₂).symm

/-- The class of a pair cocycle `b` is the line bundle glued from `1 + ε b`. -/
theorem picardKerEquivPairCohomology_symm_mk (b : pairCocycles U) :
    ((picardKerEquivPairCohomology k sX U hU hU₁ hU₂).symm (QuotientAddGroup.mk b) :
        PicardGroup (dualScheme k sX)) =
      (dualIdealGenerator k sX).cocycleClass U hU b :=
  rfl

end Ring

section Field

variable {k : Type u} [Field k] (X : FScheme k) [X.left.IsSeparated] {ι : Type u}
  (U : ι → X.left.Opens) (hU : iSup U = ⊤) (hU₁ : ∀ j, IsAffineOpen (U j))

/-- `ker(i^* : Pic X[ε] → Pic X) ≃+ H^1(X, 𝒪_X)` for a separated scheme over a field and a
cover by affine opens, by Čech cocycles `1 + ε b`. -/
def picardKerEquivCech :
    (pullbackHom (inclusion k X.hom)).ker ≃+ structureCohomology k X 1 :=
  (picardKerEquivPairCohomology k X.hom U hU hU₁ fun j l => (hU₁ j).inf (hU₁ l)).trans
    ((Cohomology.pairCohomologyEquivCech X U).trans
      (Cohomology.structureCechCohomologyLinearEquiv X U hU
        (Cohomology.isAffineOpen_cechTuple U hU₁) (injectiveResolution _) 0).toAddEquiv)

/-- On the class of the line bundle glued from `1 + ε b`, the comparison is the Čech class
of the pair cocycle `b`. -/
theorem picardKerEquivCech_cocycleClass (b : pairCocycles U) :
    picardKerEquivCech X U hU hU₁ ⟨(dualIdealGenerator k X.hom).cocycleClass U hU b,
        AddMonoidHom.mem_ker.mpr ((dualIdealGenerator k X.hom).pullbackHom_cocycleClass U hU b)⟩ =
      Cohomology.structureCechCohomologyLinearEquiv X U hU
        (Cohomology.isAffineOpen_cechTuple U hU₁) (injectiveResolution _) 0
        (Cohomology.pairCohomologyEquivCech X U (QuotientAddGroup.mk b)) := by
  have hb : (⟨(dualIdealGenerator k X.hom).cocycleClass U hU b,
      AddMonoidHom.mem_ker.mpr ((dualIdealGenerator k X.hom).pullbackHom_cocycleClass U hU b)⟩ :
        (pullbackHom (inclusion k X.hom)).ker) =
      (picardKerEquivPairCohomology k X.hom U hU hU₁ fun j l => (hU₁ j).inf (hU₁ l)).symm
        (QuotientAddGroup.mk b) :=
    Subtype.ext (picardKerEquivPairCohomology_symm_mk k X.hom U hU hU₁ _ b).symm
  rw [hb]
  change Cohomology.structureCechCohomologyLinearEquiv X U hU
      (Cohomology.isAffineOpen_cechTuple U hU₁) (injectiveResolution _) 0
      (Cohomology.pairCohomologyEquivCech X U
        ((picardKerEquivPairCohomology k X.hom U hU hU₁ fun j l => (hU₁ j).inf (hU₁ l))
          ((picardKerEquivPairCohomology k X.hom U hU hU₁ fun j l => (hU₁ j).inf (hU₁ l)).symm
            (QuotientAddGroup.mk b)))) = _
  rw [AddEquiv.apply_symm_apply]

end Field

end AlgebraicGeometry.Scheme.DualNumbers
