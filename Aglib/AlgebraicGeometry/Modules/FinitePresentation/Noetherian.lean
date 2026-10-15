/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.FinitePresentation.AffineTransport
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.FinitePresentation
public import Mathlib.AlgebraicGeometry.Noetherian
/-!
# Finite presentations from Noetherian finite-type data

Finite modules over Noetherian rings admit actual finite generator and
relation data after applying tilde. Transporting those presentations along
the affine-open cover gives finite presentation of a finite-type
quasicoherent module sheaf over a locally Noetherian scheme.

These statements use the actual chart predicate and require neither a
coherent category nor its abelian or exact structures.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- A finite module over a noetherian ring has an actual finite global
presentation after applying tilde. -/
theorem exists_finite_presentation_tilde (R : CommRingCat.{u}) [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    ∃ P : (tilde M).Presentation, P.IsFinite := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := M)
  let f : ((s : Set M) →₀ R) →ₗ[R] M := Finsupp.linearCombination R (fun x : (s : Set M) => x.1)
  obtain ⟨t, ht⟩ := IsNoetherian.noetherian (LinearMap.ker f)
  let P := presentationTilde M (s : Set M) hs (t : Set ((s : Set M) →₀ R)) ht
  exact ⟨P, { isFiniteType_generators := ⟨inferInstanceAs (Finite (s : Set M))⟩
              isFiniteType_relations := ⟨inferInstanceAs (Finite (t : Set ((s : Set M) →₀ R)))⟩ }⟩


/-- A finite module over a noetherian ring gives a genuinely finitely presented
sheaf on its spectrum. -/
theorem finitePresentation_tilde (R : CommRingCat.{u}) [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    (tilde M).IsFinitePresentation := by
  obtain ⟨P, hP⟩ := exists_finite_presentation_tilde R M
  let := hP
  exact finitePresentation_of_presentation P

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent

/-- The actual affine finite-quasicoherent property supplies a finite global
presentation of the given sheaf. -/
theorem affineFiniteSheaf_exists_presentation (R : CommRingCat.{u}) [IsNoetherianRing R]
    {M : (Spec R).Modules} (hM : affineFiniteSheaf R M) :
    ∃ P : M.Presentation, P.IsFinite := by
  have : M.IsQuasicoherent := hM.1
  have : Module.Finite R (moduleSpecΓFunctor.obj M) := hM.2
  have : IsIso M.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  obtain ⟨P, hP⟩ := exists_finite_presentation_tilde R (moduleSpecΓFunctor.obj M)
  exact ⟨P.ofIsIso M.fromTildeΓ, inferInstance⟩

/-- Over a locally Noetherian scheme, the chart-based finite-type
quasicoherent predicate supplies a genuine finite local presentation. -/
theorem affineLocallyFiniteType_finitePresentation {X : Scheme.{u}} [IsLocallyNoetherian X]
    {M : X.Modules} (hM : affineLocallyFiniteType X M) : M.IsFinitePresentation := by
  classical
  have h (U : X.affineOpens) : ∃ P : (M.restrict U.2.fromSpec).Presentation, P.IsFinite := by
    let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    exact affineFiniteSheaf_exists_presentation Γ(X, U.1) (hM _ U.2.fromSpec)
  choose P hP using h
  let q : M.QuasicoherentData :=
    { I := X.affineOpens
      X := fun U => U.1
      coversTop := by
        rw [Opens.coversTop_iff, IsOpenCover]
        exact iSup_affineOpens_eq_top X
      presentation U := affinePresentationToOver M U (P U) }
  refine SheafOfModules.IsFinitePresentation.mk (M := M) ⟨q, ?_⟩
  constructor
  intro U
  have := hP U
  exact affinePresentationToOver_isFinite M U (P U)

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent
