/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ConstructibleAffineGenericOpen
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Basic.GenericLocallyConstant
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Basic.PullbackPartition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteStratification.GenericProperty

/-! # Finite direct-image constructibility over an affine Noetherian base

The original Noetherian partition induction is applied to finite local
constancy of the original inverse-image coefficients. For each integral
affine immersion, finite base change and the actual generic-open producer
give constructibility on a nonempty open. A genuine affine neighborhood and
its original generic stratum then give finite local constancy. The resulting
actual partition proves constructibility of the original finite direct image.
No proper-base-change or smooth-base-change theorem is an input.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

universe u

attribute [local instance] hasSheafifyLarge

/-- Complete generic finite-local-constancy construction for a variable
original finite morphism, before any concrete pullback is substituted. -/
theorem exists_nonempty_finiteLocallyConstant_open_of_finite
    {Y X : Scheme.{u}} [IsAffine X] [IsIntegral X] [IsNoetherian X]
    (f : Y ⟶ X) [IsFinite f]
    {F : AbelianSheaf.{u, u + 1} Y} (hF : Constructible.IsConstructible F) :
    ∃ (V : Scheme.{u}) (j : V ⟶ X), IsOpenImmersion j ∧ Nonempty V ∧
      IsFiniteLocallyConstant ((inverseImage j).obj ((directImage f).obj F)) := by
  obtain ⟨S, a, ha, hS, hImage⟩ := exists_nonempty_constructible_open_of_finite f hF
  have : IsOpenImmersion a := ha
  have : Nonempty S := hS
  have : IsIntegral S := isIntegral_of_isOpenImmersion a
  let x : S := Classical.choice hS
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ (⊤ : S.Opens) from trivial)
  have : Nonempty U.toScheme := ⟨⟨x, hx⟩⟩
  have : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  obtain ⟨t⟩ := hImage ⟨U, hU⟩
  obtain ⟨V, b, hb, hV, hloc⟩ :=
    Constructible.exists_nonempty_finiteLocallyConstant_open_of_partition t
  have : IsOpenImmersion b := hb
  let j := (b ≫ U.ι) ≫ a
  let e : (inverseImage j).obj ((directImage f).obj F) ≅
      (inverseImage b).obj ((inverseImage U.ι).obj
        ((inverseImage a).obj ((directImage f).obj F))) :=
    ((inverseImageComp a (b ≫ U.ι)).app ((directImage f).obj F)) ≪≫
      ((inverseImageComp U.ι b).app ((inverseImage a).obj ((directImage f).obj F)))
  exact ⟨V, j, inferInstance, hV, (isFiniteLocallyConstant_iff_of_iso e).mpr hloc⟩

/-- Construct and transport the genuine generic FLC open across an original
variable Cartesian square, including the original mate and composition iso.
Finite local constancy is produced, not an additional input certificate. -/
theorem exists_nonempty_finiteLocallyConstant_open_of_finite_baseChange
    {Y X Y' T : Scheme.{u}} [IsAffine Y]
    [IsAffine T] [IsIntegral T] [IsNoetherian T]
    (f : Y ⟶ X) (f' : Y' ⟶ T) (i : T ⟶ X) (k : Y' ⟶ Y)
    [IsFinite f] (H : IsPullback k f' f i)
    {F : AbelianSheaf.{u, u + 1} Y} (hF : Constructible.IsConstructible F) :
    ∃ (V : Scheme.{u}) (j : V ⟶ T), IsOpenImmersion j ∧ Nonempty V ∧
      IsFiniteLocallyConstant ((inverseImage (j ≫ i)).obj ((directImage f).obj F)) := by
  have : IsFinite f' := MorphismProperty.of_isPullback H (inferInstance : IsFinite f)
  have hFk : Constructible.IsConstructible ((inverseImage k).obj F) :=
    Constructible.isConstructible_pullback_of_isAffine k hF
  obtain ⟨V, j, hj, hV, hloc⟩ :=
    exists_nonempty_finiteLocallyConstant_open_of_finite f' hFk
  have : IsIso ((baseChangeMap f f' i k H.w.symm).app F) :=
    finiteBaseChange_app_isIso f f' i k H F
  let e : (inverseImage (j ≫ i)).obj ((directImage f).obj F) ≅
      (inverseImage j).obj ((directImage f').obj ((inverseImage k).obj F)) :=
    ((inverseImageComp i j).app ((directImage f).obj F)) ≪≫
      (inverseImage j).mapIso (asIso ((baseChangeMap f f' i k H.w.symm).app F))
  exact ⟨V, j, hj, hV, (isFiniteLocallyConstant_iff_of_iso e).mpr hloc⟩

/-- A finite morphism over an affine Noetherian scheme preserves original
finite-abelian constructibility under its original direct image. -/
theorem isConstructible_directImage_of_isAffine_of_isNoetherian
    {Y X : Scheme.{u}} [IsAffine X] [IsNoetherian X]
    (f : Y ⟶ X) [IsFinite f]
    {F : AbelianSheaf.{u, u + 1} Y} (hF : Constructible.IsConstructible F) :
    Constructible.IsConstructible ((directImage f).obj F) := by
  have : IsAffine Y := isAffine_of_isAffineHom f
  have hgeneric : ∀ (T : Scheme.{u}) [IsNoetherian T] [IsAffine T] [IsIntegral T]
      (i : T ⟶ X) [IsImmersion i],
      ∃ (S : Scheme.{u}) (j : S ⟶ T), IsOpenImmersion j ∧ Nonempty S ∧
        IsFiniteLocallyConstant ((inverseImage (j ≫ i)).obj ((directImage f).obj F)) := by
    intro T _ _ _ i _
    exact exists_nonempty_finiteLocallyConstant_open_of_finite_baseChange
      f (pullback.snd f i) i (pullback.fst f i) (IsPullback.of_hasPullback f i) hF
  obtain ⟨p, hp⟩ := Constructible.exists_finitePartition_of_generic_open
    (fun {_} i => IsFiniteLocallyConstant ((inverseImage i).obj ((directImage f).obj F)))
    hgeneric
  exact Constructible.isConstructible_of_partition
    { toFiniteLocallyClosedPartition := p, locally_constant := hp }

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
