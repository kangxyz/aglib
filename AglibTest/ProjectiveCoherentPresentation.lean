module

import Aglib.AlgebraicGeometry.Modules.Coherent.Projective.Presentation

/-! Public consumers of the actual projective coherent presentation. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.QuasiCoherent Scheme.Modules.Coherent.Projective
universe u

namespace AglibTest.ProjectiveCoherentPresentation

/-- The common twist is strictly negative even over a non-Noetherian base. -/
example (R : Type u) [CommRing R] (ι : Type u) [Finite ι]
    {X : Scheme.{u}} (i : X ⟶ ProjectiveSpace R ι) [IsClosedImmersion i]
    (M : X.Modules) (hM : affineLocallyFiniteType X M) :
    ∃ d : ℤ, d < 0 ∧ ∃ (I : Type u) (_ : Finite I)
      (π : (∐ fun _ : I =>
        (Scheme.Modules.pullback i).obj (ProjectiveSpace.twistingSheaf R ι d)) ⟶ M),
      Epi π := by
  obtain ⟨N, hN, I, hI, π, hπ, _⟩ :=
    exists_uniformNegativeTwistEpimorphism R ι i M hM 0
  refine ⟨-(N : ℤ), ?_, I, hI, π, hπ⟩
  exact neg_neg_of_pos (by exact_mod_cast hN)

/-- A coherent sheaf is covered by an actual object of the native vector-bundle category.
Local Noetherianity comes from the given closed embedding, without a regularity input. -/
example (R : Type u) [CommRing R] [IsNoetherianRing R] (ι : Type u) [Finite ι]
    {X : Scheme.{u}} (i : X ⟶ ProjectiveSpace R ι) [IsClosedImmersion i] :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian i
    ∀ M : Scheme.CoherentSheaf X, ∃ E : FiniteLocallyFree X,
      ∃ π : E.obj ⟶ M.obj, Epi π := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian i
  intro M
  obtain ⟨N, _, I, hI, π, hπ, hfree⟩ :=
    exists_coherent_uniformNegativeTwistEpimorphism R ι i M 0
  let := hI
  exact ⟨⟨_, hfree⟩, π, hπ⟩

end AglibTest.ProjectiveCoherentPresentation
