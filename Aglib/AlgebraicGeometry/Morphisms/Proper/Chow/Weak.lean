/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Proper.Chow.Basic
public import Aglib.AlgebraicGeometry.Morphisms.Proper.Chow.GraphProduct.Immersion
public import Aglib.AlgebraicGeometry.ProjectiveSpace.AffineImmersion.OpenChart

/-!
# Weak Chow modifications over Noetherian affine bases

Every separated finite-type scheme over a Noetherian affine base admits an
actual proper surjective modification immersive in a finite native product of
polynomial projective spaces. The source need not be proper. The construction
retains the original graph product, its structural equation, its closed pair
of projections, and its dense isomorphism open.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Chow

variable (R : Type u) [CommRing R]

/-- A separated finite-type scheme over a Noetherian affine base has a proper
surjective modification immersive in an actual finite projective product. -/
theorem exists_immersion_projective_product_modification [IsNoetherianRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (m : ℕ) (σ : Fin m → Type u) (_ : ∀ i, Fintype (σ i))
      (Y : Scheme.{u}) (p : Y ⟶ X) (q : Y ⟶ (projectiveProductOver R σ).left)
      (V : X.Opens) (comm : p ≫ f = q ≫ (projectiveProductOver R σ).hom),
      IsProper p ∧ Surjective p ∧ IsImmersion q ∧ Dense (V : Set X) ∧
        IsIso (p ∣_ V) ∧ IsClosedImmersion (pullback.lift p q comm) := by
  classical
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : IsNoetherian X := ⟨⟩
  obtain ⟨ι, hι, U₀, hU₀, hcover₀, -⟩ := X.exists_finite_dense_affine_cover
  let := hι
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let U : Fin (Fintype.card ι) → X.Opens := fun i => U₀ (e.symm i)
  have hU (i : Fin (Fintype.card ι)) :
      IsAffineOpen (U i) ∧ Dense (U i : Set X) ∧ genericPoints X ⊆ U i :=
    hU₀ (e.symm i)
  have hcover : (⨆ i, U i) = ⊤ := by
    apply top_unique
    intro x _
    have hx : x ∈ ⨆ i, U₀ i := by rw [hcover₀]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    exact Opens.mem_iSup.mpr ⟨e i, by simpa [U] using hi⟩
  have hemb (i : Fin (Fintype.card ι)) :
      ∃ (I : Type u) (_ : Fintype I)
        (j : (U i).toScheme ⟶ (ProjectiveSpace.coordinateOpen R (Option I) none).toScheme),
        IsClosedImmersion j ∧
          (j ≫ (ProjectiveSpace.coordinateOpen R (Option I) none).ι) ≫
            ProjectiveSpace.toSpec R (Option I) = (U i).ι ≫ f :=
    ProjectiveSpace.exists_projectiveChart_closedImmersion_of_isAffineOpen R f (U i) (hU i).1
  choose σ hσ j hj hcomp using hemb
  let (i : Fin (Fintype.card ι)) : Fintype (σ i) := hσ i
  let P : Fin (Fintype.card ι) → Over (Spec (CommRingCat.of R)) :=
    fun i => Over.mk (ProjectiveSpace.toSpec R (Option (σ i)))
  let W (i : Fin (Fintype.card ι)) : (P i).left.Opens :=
    ProjectiveSpace.coordinateOpen R (Option (σ i)) none
  let h (i : Fin (Fintype.card ι)) : (U i).toScheme ⟶ (P i).left := j i ≫ (W i).ι
  have w (i : Fin (Fintype.card ι)) : (U i).ι ≫ f = h i ≫ (P i).hom :=
    (hcomp i).symm
  have (i : Fin (Fintype.card ι)) : IsProper (P i).hom := by
    dsimp [P]
    infer_instance
  have (i : Fin (Fintype.card ι)) : QuasiCompact (U i).ι := inferInstance
  have (i : Fin (Fintype.card ι)) : IsClosedImmersion (j i) := hj i
  let V : X.Opens := ⨅ i, U i
  have hdense : Dense (V : Set X) := by
    apply Dense.mono ?_ (dense_iff_closure_eq.mpr (genericPoints.closure (α := X)))
    intro x hx
    change x ∈ (((⨅ i, U i) : X.Opens) : Set X)
    rw [Opens.coe_iInf]
    exact Set.mem_iInter.mpr fun i => (hU i).2.2 hx
  refine ⟨Fintype.card ι, σ, hσ, GraphProduct.model f P U h w,
    GraphProduct.toSource f P U h w, GraphProduct.toTarget f P U h w, V,
    GraphProduct.toSource_comp f P U h w, inferInstance, ?_, ?_, hdense, ?_, ?_⟩
  · exact GraphProduct.toSource_surjective f P U h w (fun i => (hU i).2.1)
  · exact GraphProduct.toTarget_isImmersion f P U h w W j (fun _ => rfl) hcover
  · exact GraphProduct.isIso_toSource_commonOpen f P U h w
  · exact GraphProduct.pair_isClosedImmersion f P U h w

end AlgebraicGeometry.Scheme.Chow
