/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Structure
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Quasi-projective and projective schemes over an affine base

Let `R` be a commutative ring. A morphism `f : X ⟶ Spec R` is

* **H-quasi-projective** (`IsHQuasiProjective f`) if it factors as a quasi-compact immersion
  `X ⟶ P(ι)_R` into projective space with finitely many homogeneous coordinates `ι`, followed by
  the structure morphism `ProjectiveSpace.toSpec R ι`;
* **H-projective** (`IsHProjective f`) if it factors as a closed immersion into some `P(ι)_R`,
  `ι` finite, followed by the structure morphism.

These are Stacks, Definition 29.41.1 (Tag 01VW) and Definition 29.44.1 (Tag 01W8) for the base
`S = Spec R`: there `P^n_S` is the base change of `P^n_ℤ = Proj ℤ[T₀, …, Tₙ]` (Definition 27.13.2,
Tag 01NF), here the polynomial `Proj` over `R` itself, `ProjectiveSpace R ι`, with a finite
coordinate type in place of `Fin (n + 1)`. Every immersion into a locally Noetherian scheme is
quasi-compact (Stacks, Lemma 28.5.3, Tag 01OX;
`quasiCompact_of_isImmersion_of_isLocallyNoetherian`), so over a Noetherian ring `f` is
H-quasi-projective exactly when `X` admits an immersion into some `P(ι)_R` over `Spec R`
(`isHQuasiProjective_iff_exists_isImmersion`). This is quasi-projectivity "in the strongest
sense" of Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §5, p. 23 (a
locally closed embedding into `P^n_S`), that is, strong quasi-projectivity (a locally closed
embedding into `P(E)` for a vector bundle `E` on the base) with `E` trivial; over an affine base
the notions agree (cf. p. 23, Exercise (iii)). The Picard plan calls it "quasi-projective over
`Spec A`".

Closure and comparison:

* Projective space `P(ι)_R` with `ι` finite is H-projective (`isHProjective_toSpec`).
* H-projective implies H-quasi-projective (Stacks, Lemma 29.44.3, Tag 01W9) and proper (closed
  immersions and `P(ι)_R ⟶ Spec R` are proper). An H-quasi-projective morphism is separated,
  quasi-compact and locally of finite type (Stacks, Lemma 29.41.4, Tag 01VX). A proper
  H-quasi-projective morphism is H-projective (`IsHProjective.of_isHQuasiProjective_of_isProper`,
  through Mathlib's `IsClosedImmersion.iff_isProper_and_mono`); hence
  `isHProjective_iff_isHQuasiProjective_and_isProper` (Stacks, Lemma 29.44.13, Tag 0BCL, for an
  affine base).
* A quasi-compact immersion into an H-quasi-projective scheme is H-quasi-projective
  (`isHQuasiProjective_comp`), and a closed immersion into an H-projective scheme is H-projective
  (`isHProjective_comp`): compositions of immersions are immersions (Stacks, Lemma 26.24.3,
  Tag 02V0). Over a Noetherian ring every immersion qualifies
  (`IsHQuasiProjective.comp_of_isImmersion`).
* Over a Noetherian ring, H-quasi-projective schemes are Noetherian
  (`IsHQuasiProjective.isNoetherian`; Stacks, Lemma 29.15.6, Tag 01T6).

Mathlib has no notion of projective or quasi-projective morphism at the pinned revision. Further
closure results are in separate leaves: products by the Segre embedding
(`Aglib.AlgebraicGeometry.ProjectiveSpace.Segre.QuasiProjective`), affine schemes of finite type
(`Aglib.AlgebraicGeometry.ProjectiveSpace.AffineImmersion.QuasiProjective`), the Grassmannian by
the Plücker embedding (`Aglib.AlgebraicGeometry.Grassmannian.QuasiProjective`) and the Hilbert
scheme of `P^n_A` (`Aglib.AlgebraicGeometry.HilbertScheme.QuasiProjective`).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An immersion into a locally Noetherian scheme is quasi-compact: it is a closed immersion
followed by an open immersion, and open immersions into locally Noetherian schemes are
quasi-compact. -/
theorem quasiCompact_of_isImmersion_of_isLocallyNoetherian {X Y : Scheme.{u}} (i : X ⟶ Y)
    [IsImmersion i] [IsLocallyNoetherian Y] : QuasiCompact i := by
  rw [← i.liftCoborder_ι]
  infer_instance

variable {R : CommRingCat.{u}} {X Y : Scheme.{u}}

/-- **H-quasi-projective over `Spec R`** (Stacks, Definition 29.41.1, Tag 01VW, over an affine
base): `f : X ⟶ Spec R` factors as a quasi-compact immersion into projective space `P(ι)_R` with
finitely many homogeneous coordinates, followed by the structure morphism. -/
class IsHQuasiProjective (f : X ⟶ Spec R) : Prop where
  /-- A quasi-compact immersion into projective space over `Spec R` factoring `f`. -/
  exists_isImmersion : ∃ (ι : Type u) (_ : Finite ι) (i : X ⟶ ProjectiveSpace R ι),
    IsImmersion i ∧ QuasiCompact i ∧ i ≫ ProjectiveSpace.toSpec R ι = f

/-- **H-projective over `Spec R`** (Stacks, Definition 29.44.1, Tag 01W8, over an affine base):
`f : X ⟶ Spec R` factors as a closed immersion into projective space `P(ι)_R` with finitely many
homogeneous coordinates, followed by the structure morphism. -/
class IsHProjective (f : X ⟶ Spec R) : Prop where
  /-- A closed immersion into projective space over `Spec R` factoring `f`. -/
  exists_isClosedImmersion : ∃ (ι : Type u) (_ : Finite ι) (i : X ⟶ ProjectiveSpace R ι),
    IsClosedImmersion i ∧ i ≫ ProjectiveSpace.toSpec R ι = f

/-- Projective space with finitely many homogeneous coordinates is H-projective. -/
instance isHProjective_toSpec (A : Type u) [CommRing A] (ι : Type u) [Finite ι] :
    IsHProjective (ProjectiveSpace.toSpec A ι) :=
  ⟨ι, inferInstance, 𝟙 _, inferInstance, Category.id_comp _⟩

/-- An H-projective morphism is H-quasi-projective. -/
instance (priority := 900) IsHProjective.isHQuasiProjective (f : X ⟶ Spec R) [IsHProjective f] :
    IsHQuasiProjective f := by
  obtain ⟨ι, _, i, _, h⟩ := IsHProjective.exists_isClosedImmersion (f := f)
  exact ⟨ι, inferInstance, i, inferInstance, inferInstance, h⟩

/-- An H-projective morphism is proper: projective space with finitely many coordinates is proper
over `Spec R`. -/
instance (priority := 900) IsHProjective.isProper (f : X ⟶ Spec R) [IsHProjective f] :
    IsProper f := by
  obtain ⟨ι, _, i, _, rfl⟩ := IsHProjective.exists_isClosedImmersion (f := f)
  infer_instance

/-- An H-quasi-projective morphism is separated: immersions are monomorphisms. -/
instance (priority := 900) IsHQuasiProjective.isSeparated (f : X ⟶ Spec R)
    [IsHQuasiProjective f] : IsSeparated f := by
  obtain ⟨ι, _, i, _, _, rfl⟩ := IsHQuasiProjective.exists_isImmersion (f := f)
  infer_instance

/-- An H-quasi-projective morphism is quasi-compact. -/
instance (priority := 900) IsHQuasiProjective.quasiCompact (f : X ⟶ Spec R)
    [IsHQuasiProjective f] : QuasiCompact f := by
  obtain ⟨ι, _, i, _, _, rfl⟩ := IsHQuasiProjective.exists_isImmersion (f := f)
  infer_instance

/-- An H-quasi-projective morphism is locally of finite type. -/
instance (priority := 900) IsHQuasiProjective.locallyOfFiniteType (f : X ⟶ Spec R)
    [IsHQuasiProjective f] : LocallyOfFiniteType f := by
  obtain ⟨ι, _, i, _, _, rfl⟩ := IsHQuasiProjective.exists_isImmersion (f := f)
  infer_instance

/-- **A proper H-quasi-projective morphism is H-projective**: the immersion into projective space
is proper, since projective space is separated, hence a closed immersion
(`IsClosedImmersion.iff_isProper_and_mono`). -/
theorem IsHProjective.of_isHQuasiProjective_of_isProper (f : X ⟶ Spec R) [IsHQuasiProjective f]
    [IsProper f] : IsHProjective f := by
  obtain ⟨ι, _, i, _, _, rfl⟩ := IsHQuasiProjective.exists_isImmersion (f := f)
  have : IsProper i := IsProper.of_comp i (ProjectiveSpace.toSpec R ι)
  exact ⟨ι, inferInstance, i, (IsClosedImmersion.iff_isProper_and_mono i).mpr
    ⟨inferInstance, inferInstance⟩, rfl⟩

/-- **H-projective is H-quasi-projective and proper.** -/
theorem isHProjective_iff_isHQuasiProjective_and_isProper (f : X ⟶ Spec R) :
    IsHProjective f ↔ IsHQuasiProjective f ∧ IsProper f :=
  ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ =>
    IsHProjective.of_isHQuasiProjective_of_isProper f⟩

/-- **A quasi-compact immersion into an H-quasi-projective scheme is H-quasi-projective.** -/
instance isHQuasiProjective_comp (i : X ⟶ Y) (g : Y ⟶ Spec R) [IsImmersion i] [QuasiCompact i]
    [IsHQuasiProjective g] : IsHQuasiProjective (i ≫ g) := by
  obtain ⟨ι, _, j, _, _, rfl⟩ := IsHQuasiProjective.exists_isImmersion (f := g)
  exact ⟨ι, inferInstance, i ≫ j, inferInstance, inferInstance, (Category.assoc _ _ _).symm⟩

/-- **A closed immersion into an H-projective scheme is H-projective.** -/
instance isHProjective_comp (i : X ⟶ Y) (g : Y ⟶ Spec R) [IsClosedImmersion i]
    [IsHProjective g] : IsHProjective (i ≫ g) := by
  obtain ⟨ι, _, j, _, rfl⟩ := IsHProjective.exists_isClosedImmersion (f := g)
  exact ⟨ι, inferInstance, i ≫ j, inferInstance, (Category.assoc _ _ _).symm⟩

/-- Over a Noetherian ring, an H-quasi-projective scheme is locally Noetherian. -/
theorem IsHQuasiProjective.isLocallyNoetherian [IsNoetherianRing R] (f : X ⟶ Spec R)
    [IsHQuasiProjective f] : IsLocallyNoetherian X :=
  LocallyOfFiniteType.isLocallyNoetherian f

/-- Over a Noetherian ring, an H-quasi-projective scheme is Noetherian. -/
theorem IsHQuasiProjective.isNoetherian [IsNoetherianRing R] (f : X ⟶ Spec R)
    [IsHQuasiProjective f] : IsNoetherian X :=
  have := IsHQuasiProjective.isLocallyNoetherian f
  have := QuasiCompact.compactSpace_of_compactSpace f
  {}

/-- **Immersions into H-quasi-projective schemes over a Noetherian ring**: every immersion into an
H-quasi-projective scheme over a Noetherian ring is quasi-compact, so the source is
H-quasi-projective. -/
theorem IsHQuasiProjective.comp_of_isImmersion [IsNoetherianRing R] (i : X ⟶ Y) (g : Y ⟶ Spec R)
    [IsImmersion i] [IsHQuasiProjective g] : IsHQuasiProjective (i ≫ g) :=
  have := IsHQuasiProjective.isLocallyNoetherian g
  have := quasiCompact_of_isImmersion_of_isLocallyNoetherian i
  inferInstance

/-- **Quasi-projective over a Noetherian ring**: over a Noetherian ring `R`, `f : X ⟶ Spec R` is
H-quasi-projective if and only if `X` admits an immersion into projective space `P(ι)_R` with
finitely many homogeneous coordinates over `Spec R`. -/
theorem isHQuasiProjective_iff_exists_isImmersion [IsNoetherianRing R] (f : X ⟶ Spec R) :
    IsHQuasiProjective f ↔ ∃ (ι : Type u) (_ : Finite ι) (i : X ⟶ ProjectiveSpace R ι),
      IsImmersion i ∧ i ≫ ProjectiveSpace.toSpec R ι = f := by
  refine ⟨fun ⟨ι, hι, i, hi, _, h⟩ => ⟨ι, hι, i, hi, h⟩, fun ⟨ι, hι, i, hi, h⟩ => ?_⟩
  have := quasiCompact_of_isImmersion_of_isLocallyNoetherian i
  exact ⟨ι, hι, i, hi, inferInstance, h⟩

end AlgebraicGeometry
