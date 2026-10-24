/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.QuasiProjective
public import Aglib.AlgebraicGeometry.ProjectiveSpace.LinearEmbedding
public import Aglib.AlgebraicGeometry.ProjectiveSpace.FiniteEmbedding
public import Aglib.CategoryTheory.Limits.FiniteCoproductMaps

/-!
# Finite disjoint unions of quasi-projective schemes over an affine base

Let `R` be a commutative ring and `J` a finite type. For H-quasi-projective morphisms
`f j : Y j ⟶ Spec R` (`IsHQuasiProjective`), the induced morphism `Sigma.desc f : ∐ Y ⟶ Spec R`
from the disjoint union is H-quasi-projective (`AlgebraicGeometry.isHQuasiProjective_sigmaDesc`),
and likewise for H-projective morphisms (`AlgebraicGeometry.isHProjective_sigmaDesc`). The binary
forms are `isHQuasiProjective_coprodDesc` and `isHProjective_coprodDesc`; an empty scheme is
H-projective (`isHProjective_of_isEmpty`). The same holds for any colimit cofan of a finite family
(`IsHQuasiProjective.of_isColimit`, `IsHProjective.of_isColimit`), in particular for a scheme
covered by finitely many pairwise disjoint opens
(`IsHQuasiProjective.of_iSup_eq_top_of_pairwise_disjoint`,
`IsHProjective.of_iSup_eq_top_of_pairwise_disjoint`, through Mathlib's
`nonempty_isColimit_cofanMk_of`).

Proof. The disjoint union `P(ι)_R ⨿ P(κ)_R` of two projective spaces with finitely many coordinates
is H-projective (`ProjectiveSpace.isHProjective_coprodDesc_toSpec`): the linear embeddings of
`P(ι)_R` and `P(κ)_R` into `P(Option (ι ⊕ κ))_R` (`ProjectiveSpace.linearEmbedding`) are closed
immersions, so the induced morphism from the disjoint union is finite (Mathlib's binary
`IsFinite (coprod.desc _ _)`; Stacks, Lemma 29.45.13, Tag 0CYI), and the source of a finite
morphism to projective space with finitely many, and at least one, coordinates has a closed
immersion into some `P^n_R` over `Spec R`
(`ProjectiveSpace.FiniteEmbedding.exists_closedImmersion_of_isFinite`; the coordinate `none` makes
`Option (ι ⊕ κ)` nonempty). No disjointness of the images is needed. For quasi-compact immersions
`X ⟶ P(ι)_R`, `Y ⟶ P(κ)_R` the morphism `coprod.map` is a quasi-compact immersion (Mathlib's
`IsZariskiLocalAtTarget.coprodMap`), which gives the binary case; the finite case follows by
induction on `J` (`CategoryTheory.Limits.Sigma.desc_induction`).

Source: the Stacks Project states the result over a base with an ample invertible sheaf, such as an
affine base (Properties, Lemma 28.28.1, Tag 01QE): More on Morphisms, Lemma 37.49.2 (4), Tag 0B43,
for quasi-projective schemes, which over such a base are the H-quasi-projective ones
(Lemma 37.49.1, Tag 0B42), and Lemma 37.50.2 (4), Tag 0B46, for projective, equivalently
H-projective, schemes (Lemma 37.50.1, Tag 0B45). Its proof goes through ample invertible sheaves,
with details omitted; the argument here is direct and uses no ampleness. Nitsure, *Construction of
Hilbert and Quot schemes*, arXiv:math/0504590v1, proof of Theorem 6.8, p. 33, uses that the finite
disjoint union of the open subschemes `Hilb^{Φ,L}_{X/S}` is quasi-projective over `S` without
argument; Kleiman, *The Picard scheme*, arXiv:math/0504020v1, Answer 4.11, p. 67, likewise ("But Z
has only finitely many components Z′. Therefore, Z is quasi-projective."). The notions are those of
Stacks, Definition 29.41.1 (Tag 01VW) and Definition 29.44.1 (Tag 01W8) over the affine base
`Spec R`, see `Aglib.AlgebraicGeometry.ProjectiveSpace.QuasiProjective`. No hypothesis on `R` is
needed; the index type `J` may lie in any universe. Consumers (Picard plan, decision D12): the
finite union of Hilbert schemes `H_F = ∐_{Φ ∈ F} Hilb^Φ_Z` (task HQ10) and the
H-quasi-projectivity of `Pic^φ_m` (task F17-11).
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

namespace ProjectiveSpace

variable (A : Type u) [CommRing A] (ι κ : Type u)

/-- **The disjoint union of two projective spaces is H-projective**: the linear embeddings of
`P(ι)_A` and `P(κ)_A` into `P(Option (ι ⊕ κ))_A` induce a finite morphism from `P(ι)_A ⨿ P(κ)_A`,
so `P(ι)_A ⨿ P(κ)_A` has a closed immersion into some `P^n_A` over `Spec A`
(`FiniteEmbedding.exists_closedImmersion_of_isFinite`). -/
instance isHProjective_coprodDesc_toSpec [Finite ι] [Finite κ] :
    IsHProjective (coprod.desc (toSpec A ι) (toSpec A κ)) := by
  let l₁ := linearEmbedding A ((Option.some_injective (ι ⊕ κ)).comp Sum.inl_injective)
  let l₂ := linearEmbedding A ((Option.some_injective (ι ⊕ κ)).comp Sum.inr_injective)
  obtain ⟨n, e, he, hes⟩ := FiniteEmbedding.exists_closedImmersion_of_isFinite (coprod.desc l₁ l₂)
  refine ⟨ULift.{u} (Fin (n + 1)), inferInstance, e, he, hes.trans ?_⟩
  apply coprod.hom_ext <;> simp [l₁, l₂]

end ProjectiveSpace

variable {R : CommRingCat.{u}} {X Y : Scheme.{u}}

/-- An empty scheme is H-projective over `Spec R`. -/
instance (priority := low) isHProjective_of_isEmpty [IsEmpty X] (f : X ⟶ Spec R) :
    IsHProjective f :=
  ⟨PUnit, inferInstance, isInitialOfIsEmpty.to _, inferInstance, isInitialOfIsEmpty.hom_ext _ _⟩

-- Instance search for `IsZariskiLocalAtTarget @QuasiCompact` (through `HasAffineProperty`) fails
-- at instance transparency under the default `respectTransparency` setting.
set_option backward.isDefEq.respectTransparency false in
/-- **A disjoint union of two H-quasi-projective schemes is H-quasi-projective**: for quasi-compact
immersions `i : X ⟶ P(ι)_R` and `j : Y ⟶ P(κ)_R`, `coprod.map i j` is a quasi-compact immersion into
the H-projective scheme `P(ι)_R ⨿ P(κ)_R`. -/
instance isHQuasiProjective_coprodDesc (f : X ⟶ Spec R) (g : Y ⟶ Spec R) [IsHQuasiProjective f]
    [IsHQuasiProjective g] : IsHQuasiProjective (coprod.desc f g) := by
  obtain ⟨ι, _, i, _, _, rfl⟩ := IsHQuasiProjective.exists_isImmersion (f := f)
  obtain ⟨κ, _, j, _, _, rfl⟩ := IsHQuasiProjective.exists_isImmersion (f := g)
  have : IsImmersion (coprod.map i j) := IsZariskiLocalAtTarget.coprodMap i j ‹_› ‹_›
  have : QuasiCompact (coprod.map i j) := IsZariskiLocalAtTarget.coprodMap i j ‹_› ‹_›
  rw [show coprod.desc (i ≫ ProjectiveSpace.toSpec R ι) (j ≫ ProjectiveSpace.toSpec R κ) =
      coprod.map i j ≫ coprod.desc (ProjectiveSpace.toSpec R ι) (ProjectiveSpace.toSpec R κ) by
    apply coprod.hom_ext <;> simp]
  infer_instance

/-- **A disjoint union of two H-projective schemes is H-projective**: for closed immersions
`i : X ⟶ P(ι)_R` and `j : Y ⟶ P(κ)_R`, `coprod.map i j` is a closed immersion into the H-projective
scheme `P(ι)_R ⨿ P(κ)_R`. -/
instance isHProjective_coprodDesc (f : X ⟶ Spec R) (g : Y ⟶ Spec R) [IsHProjective f]
    [IsHProjective g] : IsHProjective (coprod.desc f g) := by
  obtain ⟨ι, _, i, _, rfl⟩ := IsHProjective.exists_isClosedImmersion (f := f)
  obtain ⟨κ, _, j, _, rfl⟩ := IsHProjective.exists_isClosedImmersion (f := g)
  have : IsClosedImmersion (coprod.map i j) := IsZariskiLocalAtTarget.coprodMap i j ‹_› ‹_›
  rw [show coprod.desc (i ≫ ProjectiveSpace.toSpec R ι) (j ≫ ProjectiveSpace.toSpec R κ) =
      coprod.map i j ≫ coprod.desc (ProjectiveSpace.toSpec R ι) (ProjectiveSpace.toSpec R κ) by
    apply coprod.hom_ext <;> simp]
  infer_instance

/-- **A finite disjoint union of H-quasi-projective schemes is H-quasi-projective**: for a finite
type `J` and H-quasi-projective `f j : Y j ⟶ Spec R`, the morphism `Sigma.desc f : ∐ Y ⟶ Spec R` is
H-quasi-projective. By induction on `J` from the binary case. -/
instance isHQuasiProjective_sigmaDesc {J : Type v} [Finite J] {Y : J → Scheme.{u}}
    (f : ∀ j, Y j ⟶ Spec R) [∀ j, IsHQuasiProjective (f j)] :
    IsHQuasiProjective (Sigma.desc f) :=
  Sigma.desc_induction (X := Spec R) (fun _ h => IsHQuasiProjective h)
    (fun _ _ e h (_ : IsHQuasiProjective h) =>
      show IsHQuasiProjective (e.hom ≫ h) from inferInstance)
    (fun W h hW => show IsHQuasiProjective h by
      have : IsEmpty W := isInitial_iff_isEmpty.mp ⟨hW⟩
      infer_instance)
    (fun _ _ h₁ h₂ (_ : IsHQuasiProjective h₁) (_ : IsHQuasiProjective h₂) =>
      show IsHQuasiProjective (coprod.desc h₁ h₂) from inferInstance)
    f fun j => show IsHQuasiProjective (f j) from inferInstance

/-- **A finite disjoint union of H-projective schemes is H-projective**: for a finite type `J` and
H-projective `f j : Y j ⟶ Spec R`, the morphism `Sigma.desc f : ∐ Y ⟶ Spec R` is H-projective. By
induction on `J` from the binary case. -/
instance isHProjective_sigmaDesc {J : Type v} [Finite J] {Y : J → Scheme.{u}}
    (f : ∀ j, Y j ⟶ Spec R) [∀ j, IsHProjective (f j)] : IsHProjective (Sigma.desc f) :=
  Sigma.desc_induction (X := Spec R) (fun _ h => IsHProjective h)
    (fun _ _ e h (_ : IsHProjective h) => show IsHProjective (e.hom ≫ h) from inferInstance)
    (fun W h hW => show IsHProjective h by
      have : IsEmpty W := isInitial_iff_isEmpty.mp ⟨hW⟩
      infer_instance)
    (fun _ _ h₁ h₂ (_ : IsHProjective h₁) (_ : IsHProjective h₂) =>
      show IsHProjective (coprod.desc h₁ h₂) from inferInstance)
    f fun j => show IsHProjective (f j) from inferInstance

/-- **A scheme that is a finite coproduct of H-quasi-projective pieces is H-quasi-projective**: if
`c` is a colimit cofan of a finite family and every `c.inj j ≫ g` is H-quasi-projective, then
`g : c.pt ⟶ Spec R` is H-quasi-projective. -/
theorem IsHQuasiProjective.of_isColimit {J : Type v} [Finite J] {Y : J → Scheme.{u}}
    {c : Cofan Y} (hc : IsColimit c) (g : c.pt ⟶ Spec R)
    (hg : ∀ j, IsHQuasiProjective (c.inj j ≫ g)) : IsHQuasiProjective g := by
  have h : g = (hc.coconePointUniqueUpToIso (coproductIsCoproduct Y)).hom ≫
      Sigma.desc fun j => c.inj j ≫ g := by
    refine Cofan.IsColimit.hom_ext hc _ _ fun j => ?_
    change c.inj j ≫ g = c.ι.app ⟨j⟩ ≫ _
    rw [IsColimit.comp_coconePointUniqueUpToIso_hom_assoc]
    simp
  rw [h]
  exact isHQuasiProjective_comp _ _

/-- **A scheme that is a finite coproduct of H-projective pieces is H-projective**: if `c` is a
colimit cofan of a finite family and every `c.inj j ≫ g` is H-projective, then
`g : c.pt ⟶ Spec R` is H-projective. -/
theorem IsHProjective.of_isColimit {J : Type v} [Finite J] {Y : J → Scheme.{u}}
    {c : Cofan Y} (hc : IsColimit c) (g : c.pt ⟶ Spec R)
    (hg : ∀ j, IsHProjective (c.inj j ≫ g)) : IsHProjective g := by
  have h : g = (hc.coconePointUniqueUpToIso (coproductIsCoproduct Y)).hom ≫
      Sigma.desc fun j => c.inj j ≫ g := by
    refine Cofan.IsColimit.hom_ext hc _ _ fun j => ?_
    change c.inj j ≫ g = c.ι.app ⟨j⟩ ≫ _
    rw [IsColimit.comp_coconePointUniqueUpToIso_hom_assoc]
    simp
  rw [h]
  exact isHProjective_comp _ _

/-- **A finite disjoint open decomposition into H-quasi-projective pieces**: if finitely many
pairwise disjoint opens `U j` cover `X` and every `(U j).ι ≫ g` is H-quasi-projective, then
`g : X ⟶ Spec R` is H-quasi-projective. -/
theorem IsHQuasiProjective.of_iSup_eq_top_of_pairwise_disjoint {J : Type v} [Finite J]
    (U : J → X.Opens) (hU : ⨆ j, U j = ⊤) (hd : Pairwise (Function.onFun Disjoint U))
    (g : X ⟶ Spec R) (hg : ∀ j, IsHQuasiProjective ((U j).ι ≫ g)) : IsHQuasiProjective g :=
  IsHQuasiProjective.of_isColimit (c := Cofan.mk X fun j => (U j).ι)
    (nonempty_isColimit_cofanMk_of (fun j => (U j).ι) (by simpa using hU)
      (by simpa [Function.onFun] using hd)).some g hg

/-- **A finite disjoint open decomposition into H-projective pieces**: if finitely many pairwise
disjoint opens `U j` cover `X` and every `(U j).ι ≫ g` is H-projective, then `g : X ⟶ Spec R` is
H-projective. -/
theorem IsHProjective.of_iSup_eq_top_of_pairwise_disjoint {J : Type v} [Finite J]
    (U : J → X.Opens) (hU : ⨆ j, U j = ⊤) (hd : Pairwise (Function.onFun Disjoint U))
    (g : X ⟶ Spec R) (hg : ∀ j, IsHProjective ((U j).ι ≫ g)) : IsHProjective g :=
  IsHProjective.of_isColimit (c := Cofan.mk X fun j => (U j).ι)
    (nonempty_isColimit_cofanMk_of (fun j => (U j).ι) (by simpa using hU)
      (by simpa [Function.onFun] using hd)).some g hg

end AlgebraicGeometry
