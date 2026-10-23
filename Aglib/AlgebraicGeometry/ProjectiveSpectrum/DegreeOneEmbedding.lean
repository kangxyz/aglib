/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpectrum.ClosedImmersion
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Structure

/-!
# Closed projective embeddings from original degree-one generators

The chosen family spans the first graded component and its powers are the
original graded components, including degree zero. Evaluation gives an
actual degreewise-surjective polynomial graded map. Its native Proj map is
a closed immersion with the original coefficient-ring structural triangle.

The coordinate family need not be finite for closedness. A finite family
gives a finite-coordinate projective embedding. No injectivity of the
coefficient-ring map, flatness or Noetherianity is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory HomogeneousLocalization Graded

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.Proj.DegreeOneEmbedding

variable {R C κ : Type u} [CommRing R] [CommRing C] [Algebra R C]
  (G : ℕ → Submodule R C) [GradedAlgebra G] (g : κ → C)

omit [GradedAlgebra G] in
/-- Every original graded component is the image of homogeneous polynomials
of the same degree under the actual generator evaluation. -/
theorem map_homogeneousSubmodule
    (hg : Submodule.span R (Set.range g) = G 1)
    (hpow : ∀ n : ℕ, (G 1) ^ n = G n) (n : ℕ) :
    (MvPolynomial.homogeneousSubmodule κ R n).map (MvPolynomial.aeval g).toLinearMap =
      G n := by
  have h1 : (MvPolynomial.homogeneousSubmodule κ R 1).map
      (MvPolynomial.aeval g).toLinearMap = G 1 := by
    simpa only [MvPolynomial.homogeneousSubmodule_one_eq_span_X, Submodule.map_span,
      ← Set.range_comp, Function.comp_def, AlgHom.toLinearMap_apply,
      MvPolynomial.aeval_X] using hg
  rw [← MvPolynomial.homogeneousSubmodule_one_pow, Submodule.map_pow, h1, hpow]

/-- The original degree-one generator evaluation as a graded ring map. -/
def presentation
    (hg : Submodule.span R (Set.range g) = G 1)
    (hpow : ∀ n : ℕ, (G 1) ^ n = G n) : MvPolynomial.homogeneousSubmodule κ R →+*ᵍ G where
  __ := (MvPolynomial.aeval g).toRingHom
  map_mem {n} {p} hp := by
    rw [← map_homogeneousSubmodule G g hg hpow n]
    exact Submodule.mem_map.mpr ⟨p, hp, rfl⟩

omit [GradedAlgebra G] in
/-- The chosen generator map is surjective in each original degree. -/
theorem presentation_degreewise_surjective
    (hg : Submodule.span R (Set.range g) = G 1)
    (hpow : ∀ n : ℕ, (G 1) ^ n = G n) (n : ℕ) :
    Function.Surjective ((presentation G g hg hpow).gradedAddHom n) := by
  intro c
  have hc : (c : C) ∈ (MvPolynomial.homogeneousSubmodule κ R n).map
      (MvPolynomial.aeval g).toLinearMap := by
    rw [map_homogeneousSubmodule G g hg hpow n]
    exact c.property
  obtain ⟨p, hp, he⟩ := Submodule.mem_map.mp hc
  exact ⟨⟨p, hp⟩, Subtype.ext he⟩

/-- Positive homogeneous lifts give the original irrelevant-ideal condition. -/
theorem irrelevant_le_map
    (hg : Submodule.span R (Set.range g) = G 1)
    (hpow : ∀ n : ℕ, (G 1) ^ n = G n) : HomogeneousIdeal.irrelevant G ≤
    (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule κ R)).map
      (presentation G g hg hpow) := by
  apply toIdeal_le_toIdeal_iff.mp
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro n hn p hp
  obtain ⟨a, ha⟩ := presentation_degreewise_surjective G g hg hpow n ⟨p, hp⟩
  have he : presentation G g hg hpow (a : MvPolynomial κ R) = p :=
    congrArg Subtype.val ha
  rw [← he]
  exact Ideal.mem_map_of_mem _
    (HomogeneousIdeal.mem_irrelevant_of_mem _ hn a.property)

/-- The actual native Proj map defined by the chosen generators. -/
def embedding
    (hg : Submodule.span R (Set.range g) = G 1)
    (hpow : ∀ n : ℕ, (G 1) ^ n = G n) : Proj G ⟶ ProjectiveSpace R κ :=
  Proj.map (presentation G g hg hpow) (irrelevant_le_map G g hg hpow)

/-- The actual generator-induced Proj map is a closed immersion. -/
theorem embedding_isClosedImmersion
    (hg : Submodule.span R (Set.range g) = G 1)
    (hpow : ∀ n : ℕ, (G 1) ^ n = G n) : IsClosedImmersion (embedding G g hg hpow) :=
  Proj.map_isClosedImmersion_of_degreewise_surjective _ _
    (presentation_degreewise_surjective G g hg hpow)

/-- The original structural morphism for the given coefficient-ring action. -/
def structureMap : Proj G ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero G ≫ Spec.map (CommRingCat.ofHom (algebraMap R (G 0)))

/-- The closed immersion retains the original coefficient-ring action. -/
@[reassoc]
theorem embedding_toSpec
    (hg : Submodule.span R (Set.range g) = G 1)
    (hpow : ∀ n : ℕ, (G 1) ^ n = G n) :
    embedding G g hg hpow ≫ ProjectiveSpace.toSpec R κ = structureMap G := by
  let F := presentation G g hg hpow
  let hF := irrelevant_le_map G g hg hpow
  apply (Proj.mapAffineOpenCover F hF).openCover.hom_ext
  intro s
  change (n : ℕ+) × ↥(MvPolynomial.homogeneousSubmodule κ R (n : ℕ)) at s
  rcases s with ⟨⟨n, hn⟩, ⟨r, hr⟩⟩
  change r ∈ MvPolynomial.homogeneousSubmodule κ R n at hr
  change Proj.awayι _ (F r) (F.map_mem hr) hn ≫
      Proj.map F hF ≫ ProjectiveSpace.toSpec R κ =
    Proj.awayι _ (F r) (F.map_mem hr) hn ≫ structureMap G
  refine (Proj.awayι_comp_map_assoc F hF hn r hr (ProjectiveSpace.toSpec R κ)).trans ?_
  simp only [ProjectiveSpace.toSpec, structureMap, Category.assoc,
    Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  apply congrArg (fun q : CommRingCat.of R ⟶ CommRingCat.of (Away G (F r)) => Spec.map q)
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change Away.map F r (fromZeroRingHom _ _ (MvPolynomial.toHomogeneousSubmoduleZero R κ a)) =
    fromZeroRingHom _ _ (algebraMap R (G 0) a)
  apply HomogeneousLocalization.val_injective
  change (Localization.mk (F (MvPolynomial.C a)) ⟨F 1, _⟩ :
      Localization (Submonoid.powers (F r))) =
    Localization.mk (algebraMap R C a) ⟨1, _⟩
  simp only [map_one]
  congr 1
  exact (MvPolynomial.aeval g).commutes a

end AlgebraicGeometry.Proj.DegreeOneEmbedding
