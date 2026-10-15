/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.Finiteness
public import Aglib.AlgebraicGeometry.Cohomology.Cech.Pushforward
public import Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.ClosedImmersion.GeneralPushforward

/-!
# Coherent finiteness through an actual projective embedding

A closed immersion into actual polynomial projective space has affine preimages of the
standard affine charts and their tuple intersections. The original geometric direct-image
cohomology map is consequently an equivalence. The proved coherent pushforward and
projective-space finiteness theorem give finite original cohomology on the source, with
the structural action of the original factored map to the base spectrum.

The actual closed immersion, dimension labeling and factorization are explicit. No native
projective-morphism predicate or general proper-finiteness family is assumed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] (ι : Type u)

/-- Original tuple intersections of the projective coordinate cover are affine. -/
theorem isAffineOpen_projectiveCoordinateTuple (p : ℕ) (a : Fin (p + 1) → ι) :
    IsAffineOpen (∏ᶜ fun k => coordinateOpen R ι (a k)) := by
  have he : (∏ᶜ fun k => coordinateOpen R ι (a k)) =
      ⨅ k, coordinateOpen R ι (a k) := by
    apply le_antisymm
    · exact le_iInf fun k => leOfHom (Pi.π _ k)
    · exact leOfHom (Pi.lift fun k => homOfLE (iInf_le _ k))
  rw [he]
  exact IsAffineOpen.iInf (fun k => isAffineOpen_coordinateOpen R ι (a k))

variable {X : Scheme.{u}} (i : X ⟶ ProjectiveSpace R ι) [IsClosedImmersion i]

/-- The native product comparison identifies every original preimage tuple intersection
with the affine preimage of the corresponding projective tuple intersection. -/
theorem isAffineOpen_projectiveEmbeddingTuple (p : ℕ) (a : Fin (p + 1) → ι) :
    IsAffineOpen (∏ᶜ fun k => i ⁻¹ᵁ coordinateOpen R ι (a k)) := by
  let e := PreservesProduct.iso (Opens.map i.base) (fun k => coordinateOpen R ι (a k))
  have he : (∏ᶜ fun k => i ⁻¹ᵁ coordinateOpen R ι (a k)) =
      i ⁻¹ᵁ (∏ᶜ fun k => coordinateOpen R ι (a k)) :=
    le_antisymm (leOfHom e.inv) (leOfHom e.hom)
  rw [he]
  exact (isAffineOpen_projectiveCoordinateTuple R ι p a).preimage i

/-- The actual direct-image cohomology equivalence along a projective embedding, with
the original base-ring action and its actual pullback on global functions. -/
def projectiveEmbeddingCohomologyLinearEquiv
    (M : X.Modules) [M.IsQuasicoherent]
    [((Scheme.Modules.pushforward i).obj M).IsQuasicoherent] (q : ℕ) :
    let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
      (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α
      ((Scheme.Modules.pushforward i).obj M) q
    letI := moduleCohomologyModuleOfHom X (i.appTop.hom.comp α) M q
    Sheaf.H.{u + 1}
        (moduleAddSheaf (ProjectiveSpace R ι) ((Scheme.Modules.pushforward i).obj M)) q ≃ₗ[R]
      Sheaf.H.{u + 1} (moduleAddSheaf X M) q :=
  moduleCohomologyPushforwardLinearEquiv i M (coordinateOpen R ι)
    (iSup_coordinateOpen_eq_top R ι)
    (i.iSup_preimage_eq_top (iSup_coordinateOpen_eq_top R ι))
    (isAffineOpen_projectiveCoordinateTuple R ι)
    (isAffineOpen_projectiveEmbeddingTuple R ι i)
    ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) q

/-- The projective-embedding equivalence has exactly the original geometric cohomology
map associated with the identity on the actual direct image. -/
theorem projectiveEmbeddingCohomologyLinearEquiv_apply
    (M : X.Modules) [M.IsQuasicoherent]
    [((Scheme.Modules.pushforward i).obj M).IsQuasicoherent] (q : ℕ)
    (x : Sheaf.H.{u + 1}
      (moduleAddSheaf (ProjectiveSpace R ι) ((Scheme.Modules.pushforward i).obj M)) q) :
    projectiveEmbeddingCohomologyLinearEquiv R ι i M q x =
      moduleCohomologyMapAlong i (𝟙 ((Scheme.Modules.pushforward i).obj M)) q x := rfl

omit [IsClosedImmersion i] in
/-- The structural ring map of the original factored morphism is exactly the pullback
of the projective structural ring map. -/
theorem projectiveEmbedding_structuralScalars :
    (i ≫ toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom =
      i.appTop.hom.comp
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) := by
  rw [Scheme.Hom.comp_appTop]
  rfl

/-- Coherent cohomology is finite on every actual closed subscheme of projective `n`-space
over a Noetherian ring, for the structural action of its original map to the base. -/
theorem projectiveEmbeddingCohomology_finite [IsNoetherianRing R]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (M : X.Modules)
    (hM : affineLocallyFiniteType X M) (q : ℕ) :
    let α : R →+* Γ(X, ⊤) :=
      (i ≫ toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom X α M q
    Module.Finite R (Sheaf.H.{u + 1} (moduleAddSheaf X M) q) := by
  let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  have hP := Modules.Coherent.Pushforward.ClosedImmersion.affineLocallyFiniteType_pushforward i hM
  let : M.IsQuasicoherent := quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
  let : ((Scheme.Modules.pushforward i).obj M).IsQuasicoherent :=
    quasicoherent_of_affineCharts _ (fun A j _ => (hP A j).1)
  have hf : letI := moduleCohomologyModuleOfHom X (i.appTop.hom.comp α) M q
      Module.Finite R (Sheaf.H.{u + 1} (moduleAddSheaf X M) q) := by
    let := moduleCohomologyModuleOfHom X (i.appTop.hom.comp α) M q
    let := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α
      ((Scheme.Modules.pushforward i).obj M) q
    let : Module.Finite R (Sheaf.H.{u + 1}
        (moduleAddSheaf (ProjectiveSpace R ι) ((Scheme.Modules.pushforward i).obj M)) q) :=
      projectiveCohomology_finite R ι n e _ hP q
    exact Module.Finite.equiv (projectiveEmbeddingCohomologyLinearEquiv R ι i M q)
  simpa only [projectiveEmbedding_structuralScalars] using hf

/-- The embedded-projective finiteness theorem for an independently specified structural
morphism, retaining its original ring action and the exact projective factorization. -/
theorem moduleCohomology_finite_of_projectiveEmbedding [IsNoetherianRing R]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (f : X ⟶ Spec (.of R))
    (hf : i ≫ toSpec R ι = f) (M : X.Modules)
    (hM : affineLocallyFiniteType X M) (q : ℕ) :
    let α : R →+* Γ(X, ⊤) := f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom X α M q
    Module.Finite R (Sheaf.H.{u + 1} (moduleAddSheaf X M) q) := by
  subst f
  exact projectiveEmbeddingCohomology_finite R ι i n e M hM q

end AlgebraicGeometry.Scheme.Cohomology
