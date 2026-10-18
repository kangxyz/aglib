/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Charts
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Twisting.Frames
public import Aglib.AlgebraicGeometry.Modules.Invertible.Gluing.Pullback
public import Aglib.AlgebraicGeometry.Modules.Invertible.PullbackTensor.Local

/-!
# Base change of the twisting sheaves

For every ring map `φ : R →+* S`, every coordinate type `ι` and every `d : ℤ`, the twisting
sheaf `O(d)` on `P_R` pulls back along `π = ProjectiveSpace.map φ ι : P_S ⟶ P_R` to `O(d)` on
`P_S` (`twistingPullbackIso`). On every subopen of the `i` chart the isomorphism sends the
pulled-back frame `Xᵢ^d` to the frame `Xᵢ^d` (`twistingPullbackIso_hom_generator`); on sections,
its inverse multiplies the frame coefficient by the pulled-back frame
(`twistingPullbackIso_inv_app`). Consequently pullback commutes with twisting,
`π^*(O_R(d) ⊗ M) ≅ O_S(d) ⊗ π^* M` (`twistingTensorPullbackIso`).

The proof applies the gluing pullback `UnitCocycle.pullbackIso`. The inverse images of the
standard charts are the standard charts (`map_preimage_coordinateOpen`), and the transition unit
`Xᵢ / Xⱼ` on `D₊(Xᵢ Xⱼ)` pulls back to the same fraction over `S`
(`appLE_coordinateTransitionOn`, from Mathlib's `Proj.awayToSection_comp_appLE`). No hypothesis
on `φ`, on the rings, or on `ι` is used.

The statement is the polynomial case `S[Xᵢ] = S ⊗_R R[Xᵢ]` of part (3) of
[Stacks Project, Lemma 27.11.6](https://stacks.math.columbia.edu/tag/01N2), which is stated for
the twisting sheaves of a graded algebra. Here `O(d)` is the sheaf glued from the coordinate
cocycle in `ProjectiveSpace/Twisting.lean`, and the proof does not use that source.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite MvPolynomial HomogeneousLocalization
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Restricted homogeneous fractions agree when their denominators and numerators agree. -/
theorem sectionRestrict_awayToSection_congr (ι : Type u) {s t : MvPolynomial ι S} (hst : s = t)
    {a b : MvPolynomial ι S} (hab : a = b) {d n : ℕ}
    (hs : s ∈ homogeneousSubmodule ι S d) (ht : t ∈ homogeneousSubmodule ι S d)
    (ha : a ∈ homogeneousSubmodule ι S (n • d)) (hb : b ∈ homogeneousSubmodule ι S (n • d))
    {V : (ProjectiveSpace S ι).Opens} (hVs : V ≤ Proj.basicOpen (homogeneousSubmodule ι S) s)
    (hVt : V ≤ Proj.basicOpen (homogeneousSubmodule ι S) t) :
    sectionRestrict (ProjectiveSpace S ι) hVs
        ((Proj.awayToSection (homogeneousSubmodule ι S) s).hom (Away.mk _ hs n a ha)) =
      sectionRestrict (ProjectiveSpace S ι) hVt
        ((Proj.awayToSection (homogeneousSubmodule ι S) t).hom (Away.mk _ ht n b hb)) := by
  subst hst hab
  rfl

/-- Over a basic open, the projective coefficient morphism acts on homogeneous fractions by the
coefficient map. -/
theorem awayToSection_comp_appLE_map (φ : R →+* S) (ι : Type u) (s : MvPolynomial ι R) {n : ℕ}
    (hs : s ∈ homogeneousSubmodule ι R n) :
    Proj.awayToSection (homogeneousSubmodule ι R) s ≫
        (map φ ι).appLE (Proj.basicOpen (homogeneousSubmodule ι R) s)
          (Proj.basicOpen (homogeneousSubmodule ι S) (gradedMap φ s)) le_rfl =
      CommRingCat.ofHom (Away.map (gradedMap φ) s) ≫
        Proj.awayToSection (homogeneousSubmodule ι S) (gradedMap φ s) :=
  Proj.awayToSection_comp_appLE (gradedMap φ) _ hs

-- `Away.map_mk` must match the coefficient map through its graded and ring-hom coercions.
set_option backward.isDefEq.respectTransparency false in
/-- The coordinate transition unit `Xᵢ / Xⱼ` pulls back to the same fraction over `S`, on every
pair of compatible subopens. -/
theorem appLE_coordinateTransitionOn (φ : R →+* S) (ι : Type u) (i j : ι)
    {W : (ProjectiveSpace R ι).Opens} {V : (ProjectiveSpace S ι).Opens}
    (hi : W ≤ coordinateOpen R ι i) (hj : W ≤ coordinateOpen R ι j)
    (hi' : V ≤ coordinateOpen S ι i) (hj' : V ≤ coordinateOpen S ι j)
    (e : V ≤ map φ ι ⁻¹ᵁ W) :
    ((map φ ι).appLE W V e).hom
        (coordinateTransitionOn R ι i j hi hj : Γ(ProjectiveSpace R ι, W)) =
      (coordinateTransitionOn S ι i j hi' hj' : Γ(ProjectiveSpace S ι, V)) := by
  have hs : X i * X j ∈ homogeneousSubmodule ι R (1 + 1) :=
    (isHomogeneous_X R i).mul (isHomogeneous_X R j)
  have hW := le_basicOpen_coordinate_mul R ι i j hi hj
  have hV : V ≤ Proj.basicOpen (homogeneousSubmodule ι S) (gradedMap φ (X i * X j)) :=
    fun x hx => hW (e hx)
  have h₁ := congrArg (fun g => g.hom ((Proj.awayToSection (homogeneousSubmodule ι R)
      (X i * X j)).hom (coordinateOverlapRatio R ι i j i)))
    (Scheme.Hom.map_appLE (map φ ι) e (homOfLE hW).op)
  have h₂ := congrArg (fun g => g.hom ((Proj.awayToSection (homogeneousSubmodule ι R)
      (X i * X j)).hom (coordinateOverlapRatio R ι i j i)))
    (Scheme.Hom.appLE_map (map φ ι)
      (le_rfl : Proj.basicOpen (homogeneousSubmodule ι S) (gradedMap φ (X i * X j)) ≤
        map φ ι ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule ι R) (X i * X j)) (homOfLE hV).op)
  have h₃ := ConcreteCategory.congr_hom (awayToSection_comp_appLE_map φ ι (X i * X j) hs)
    (coordinateOverlapRatio R ι i j i)
  change ((map φ ι).appLE W V e).hom ((ProjectiveSpace R ι).presheaf.map (homOfLE hW).op |>.hom
      ((Proj.awayToSection (homogeneousSubmodule ι R) (X i * X j)).hom
        (coordinateOverlapRatio R ι i j i))) = _
  refine h₁.trans (h₂.symm.trans ?_)
  change sectionRestrict (ProjectiveSpace S ι) hV
      (((Proj.awayToSection (homogeneousSubmodule ι R) (X i * X j) ≫
        (map φ ι).appLE (Proj.basicOpen (homogeneousSubmodule ι R) (X i * X j))
          (Proj.basicOpen (homogeneousSubmodule ι S) (gradedMap φ (X i * X j))) le_rfl).hom)
        (coordinateOverlapRatio R ι i j i)) = _
  rw [h₃]
  change sectionRestrict (ProjectiveSpace S ι) hV
      ((Proj.awayToSection (homogeneousSubmodule ι S) (gradedMap φ (X i * X j))).hom
        (Away.map (gradedMap φ) (X i * X j) (coordinateOverlapRatio R ι i j i))) =
    sectionRestrict (ProjectiveSpace S ι) (le_basicOpen_coordinate_mul S ι i j hi' hj')
      ((Proj.awayToSection (homogeneousSubmodule ι S) (X i * X j)).hom
        (coordinateOverlapRatio S ι i j i))
  rw [coordinateOverlapRatio, coordinateOverlapRatio, Away.map_mk]
  exact sectionRestrict_awayToSection_congr ι (by simp) (by simp) _ _ _ _ hV _

/-- The standard transition units of `P_S` are the pullbacks of those of `P_R`. -/
theorem transitionPullback_coordinateUnitCocycle (φ : R →+* S) (ι : Type u) :
    UnitCocycle.TransitionPullback (map φ ι) (coordinateUnitCocycle R ι)
      (coordinateUnitCocycle S ι) := by
  intro i j e
  apply Units.ext
  exact appLE_coordinateTransitionOn φ ι i j inf_le_left inf_le_right inf_le_left inf_le_right e

/-- **Base change of the twisting sheaves**: `π^* O_R(d) ≅ O_S(d)` for
`π = ProjectiveSpace.map φ ι`, for every ring map `φ`, coordinate type `ι` and degree `d`
([Stacks Project, Lemma 27.11.6 (3)](https://stacks.math.columbia.edu/tag/01N2), polynomial
case). -/
def twistingPullbackIso (φ : R →+* S) (ι : Type u) (d : ℤ) :
    (Scheme.Modules.pullback (map φ ι)).obj (twistingSheaf R ι d) ≅ twistingSheaf S ι d :=
  ((coordinateUnitCocycle R ι).zpow (-d)).pullbackIso (map φ ι)
    ((coordinateUnitCocycle S ι).zpow (-d)) (map_preimage_coordinateOpen φ ι)
    ((transitionPullback_coordinateUnitCocycle φ ι).zpow (-d)) (iSup_coordinateOpen_eq_top R ι)

/-- The pullback of the frame `Xᵢ^d` of `O_R(d)`, on a subopen of the `i` chart of `P_S`: the
adjunction-unit image of the frame on `D₊(Xᵢ)`, restricted along `V ≤ π⁻¹ D₊(Xᵢ) = D₊(Xᵢ)`. -/
def twistingPullbackGenerator (φ : R →+* S) (ι : Type u) (d : ℤ) (i : ι)
    {V : (ProjectiveSpace S ι).Opens} (hV : V ≤ coordinateOpen S ι i) :
    Γ((Scheme.Modules.pullback (map φ ι)).obj (twistingSheaf R ι d), V) :=
  ((coordinateUnitCocycle R ι).zpow (-d)).pullbackGenerator (map φ ι) i
    (hV.trans (map_preimage_coordinateOpen φ ι i).ge)

/-- The pulled-back frame, written with the original frame and adjunction unit. -/
theorem twistingPullbackGenerator_eq (φ : R →+* S) (ι : Type u) (d : ℤ) (i : ι)
    {V : (ProjectiveSpace S ι).Opens} (hV : V ≤ coordinateOpen S ι i) :
    twistingPullbackGenerator φ ι d i hV =
      ((Scheme.Modules.pullback (map φ ι)).obj (twistingSheaf R ι d)).val.map
        (homOfLE (hV.trans (map_preimage_coordinateOpen φ ι i).ge)).op
        (((pullbackPushforwardAdjunction (map φ ι)).unit.app (twistingSheaf R ι d)).val.app
          (op (coordinateOpen R ι i)) (twistingGenerator R ι d i le_rfl)) :=
  rfl

/-- On every subopen of the `i` chart, the base-change isomorphism sends the pulled-back frame
`Xᵢ^d` to the frame `Xᵢ^d`. -/
@[simp]
theorem twistingPullbackIso_hom_generator (φ : R →+* S) (ι : Type u) (d : ℤ) (i : ι)
    {V : (ProjectiveSpace S ι).Opens} (hV : V ≤ coordinateOpen S ι i) :
    (twistingPullbackIso φ ι d).hom.val.app (op V) (twistingPullbackGenerator φ ι d i hV) =
      twistingGenerator S ι d i hV :=
  UnitCocycle.pullbackIso_hom_pullbackGenerator _ _ _ _ _ _ i hV

/-- The inverse base-change isomorphism sends the frame `Xᵢ^d` to the pulled-back frame. -/
@[simp]
theorem twistingPullbackIso_inv_generator (φ : R →+* S) (ι : Type u) (d : ℤ) (i : ι)
    {V : (ProjectiveSpace S ι).Opens} (hV : V ≤ coordinateOpen S ι i) :
    (twistingPullbackIso φ ι d).inv.val.app (op V) (twistingGenerator S ι d i hV) =
      twistingPullbackGenerator φ ι d i hV :=
  UnitCocycle.pullbackIso_inv_generator _ _ _ _ _ _ i hV

-- The frame equivalence is applied on `Γ(P_S, V)`, presented through the sheaf of rings.
set_option backward.isDefEq.respectTransparency false in
/-- On every subopen of the `i` chart, the inverse base-change isomorphism is the frame
coefficient times the pulled-back frame. -/
theorem twistingPullbackIso_inv_app (φ : R →+* S) (ι : Type u) (d : ℤ) (i : ι)
    {V : (ProjectiveSpace S ι).Opens} (hV : V ≤ coordinateOpen S ι i)
    (s : Γ(twistingSheaf S ι d, V)) :
    (twistingPullbackIso φ ι d).inv.val.app (op V) s =
      twistingSectionsEquiv S ι d i hV s • twistingPullbackGenerator φ ι d i hV := by
  conv_lhs => rw [← twistingSectionsEquiv_smul_generator S ι d i hV s]
  rw [_root_.map_smul, twistingPullbackIso_inv_generator]

-- The `IsIso` instance of the tensor comparison matches only up to the presentations of the
-- module-sheaf tensor.
set_option backward.isDefEq.respectTransparency false in
/-- **Twisting commutes with base change**: `π^*(O_R(d) ⊗ M) ≅ O_S(d) ⊗ π^* M`. The first map
is the canonical tensor comparison `pullbackTensorMap`, invertible because `O_R(d)` is locally of
rank one; the second is `twistingPullbackIso` on the first factor. -/
def twistingTensorPullbackIso (φ : R →+* S) (ι : Type u) (d : ℤ)
    (M : (ProjectiveSpace R ι).Modules) :
    (Scheme.Modules.pullback (map φ ι)).obj
        ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).obj M) ≅
      (moduleTensorLeftFunctor (ProjectiveSpace S ι) (twistingSheaf S ι d)).obj
        ((Scheme.Modules.pullback (map φ ι)).obj M) :=
  haveI := PullbackTensor.Local.pullbackTensorMap_isIso (map φ ι) (twistingSheaf R ι d) M
    (isLocallyRankOne_twistingSheaf R ι d)
  asIso (pullbackTensorMap (map φ ι) (twistingSheaf R ι d) M) ≪≫
    (moduleTensorRightFunctor (ProjectiveSpace S ι)
      ((Scheme.Modules.pullback (map φ ι)).obj M)).mapIso (twistingPullbackIso φ ι d)

/-- The twisted-module comparison is the canonical tensor comparison followed by
`twistingPullbackIso` on the twisting factor. -/
theorem twistingTensorPullbackIso_hom (φ : R →+* S) (ι : Type u) (d : ℤ)
    (M : (ProjectiveSpace R ι).Modules) :
    (twistingTensorPullbackIso φ ι d M).hom =
      pullbackTensorMap (map φ ι) (twistingSheaf R ι d) M ≫
        (moduleTensorCoefficientMap (ProjectiveSpace S ι) (twistingPullbackIso φ ι d).hom).app
          ((Scheme.Modules.pullback (map φ ι)).obj M) :=
  rfl

end AlgebraicGeometry.ProjectiveSpace
