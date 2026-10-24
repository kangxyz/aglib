/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GaloisInstances
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Graph
public import Mathlib.CategoryTheory.Galois.GaloisObjects

/-!
# The original self-overlap of a finite étale Galois cover

For a native Galois object `Y` over a connected scheme `X`, the canonical map
from the finite coproduct indexed by `Aut Y` to `Y ×_X Y` is an isomorphism.
The summand indexed by `σ` is the literal graph `(id, σ.hom)`. Both original
scheme projections are retained. Thus a contravariant coefficient action uses
restriction along `σ.inv`, rather than silently reversing the graph convention.

The proof uses the actual point-lift fibre, finite-coproduct preservation, native
Galois evaluation, and geometric reflection of isomorphisms. No coefficient
finiteness, monodromy equivalence, or sheaf-descent assertion is used.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale

open ProperResidue (productCover productFirst productSecond)

universe u
variable {X : Scheme.{u}}
variable (Y : Scheme.FiniteEtale X)

/-- The graph with first coordinate the identity and second coordinate `σ`. -/
def galoisOverlapGraph (σ : Aut Y) : Y ⟶ productCover Y Y :=
  ObjectProperty.homMk (Over.homMk
    (pullback.lift (𝟙 Y.obj.left) σ.hom.hom.left (by
      simpa only [Category.id_comp] using (Over.w σ.hom.hom).symm)) (by
        change pullback.lift _ _ _ ≫ pullback.fst _ _ ≫ Y.obj.hom = Y.obj.hom
        simp))

@[reassoc (attr := simp)]
theorem galoisOverlapGraph_fst (σ : Aut Y) :
    galoisOverlapGraph Y σ ≫ productFirst Y Y = 𝟙 Y := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem galoisOverlapGraph_snd (σ : Aut Y) :
    galoisOverlapGraph Y σ ≫ productSecond Y Y = σ.hom := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact pullback.lift_snd _ _ _

variable [ConnectedSpace X] [IsGalois Y]

/-- The canonical self-overlap map in the actual finite étale category. -/
def galoisOverlapMap : (∐ fun _ : Aut Y => Y) ⟶ productCover Y Y :=
  Sigma.desc (galoisOverlapGraph Y)

@[reassoc (attr := simp)]
theorem galoisOverlapMap_ι (σ : Aut Y) :
    Sigma.ι (fun _ : Aut Y => Y) σ ≫ galoisOverlapMap Y = galoisOverlapGraph Y σ :=
  Sigma.ι_comp_desc _ _

section Fiber

variable {K : Type u} [Field K]
variable (s : Spec (CommRingCat.of K) ⟶ X)

omit [ConnectedSpace X] [IsGalois Y] in
private theorem galoisOverlapGraph_fiber_fst (σ : Aut Y) (a : Fiber s Y) :
    ((fiberToFinite s).map (galoisOverlapGraph Y σ) a) ≫ (productFirst Y Y).hom = a := by
  apply Over.OverMorphism.ext
  change (a.left ≫ pullback.lift _ _ _) ≫ pullback.fst _ _ = a.left
  simp

omit [ConnectedSpace X] [IsGalois Y] in
private theorem galoisOverlapGraph_fiber_snd (σ : Aut Y) (a : Fiber s Y) :
    ((fiberToFinite s).map (galoisOverlapGraph Y σ) a) ≫ (productSecond Y Y).hom =
      (fiberToFinite s).map σ.hom a := by
  apply Over.OverMorphism.ext
  change (a.left ≫ pullback.lift _ _ _) ≫ pullback.snd _ _ = a.left ≫ σ.hom.hom.left
  simp

private theorem galoisOverlapMap_fiber_ι (σ : Aut Y) (a : Fiber s Y) :
    (fiberToFinite s).map (galoisOverlapMap Y)
      ((fiber s).map (Sigma.ι (fun _ : Aut Y => Y) σ) a) =
        (fiberToFinite s).map (galoisOverlapGraph Y σ) a := by
  change (a ≫ (Sigma.ι (fun _ : Aut Y => Y) σ).hom) ≫ (galoisOverlapMap Y).hom =
    a ≫ (galoisOverlapGraph Y σ).hom
  rw [Category.assoc]
  exact congrArg (fun f : Y ⟶ productCover Y Y => a ≫ f.hom) (galoisOverlapMap_ι Y σ)

omit [ConnectedSpace X] [IsGalois Y] in
private theorem galoisOverlap_fiber_ext {p q : Fiber s (productCover Y Y)}
    (h₁ : p ≫ (productFirst Y Y).hom = q ≫ (productFirst Y Y).hom)
    (h₂ : p ≫ (productSecond Y Y).hom = q ≫ (productSecond Y Y).hom) : p = q := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact congrArg (fun f : Fiber s Y => f.left) h₁
  · exact congrArg (fun f : Fiber s Y => f.left) h₂

variable [IsSepClosed K]

/-- Native Galois evaluation proves bijectivity on the original point-lift fibre. -/
theorem galoisOverlapMap_fiber_bijective :
    Function.Bijective ((fiberToFinite s).map (galoisOverlapMap Y)) := by
  have hc := isColimitOfHasCoproductOfPreservesColimit (fiber s) (fun _ : Aut Y => Y)
  constructor
  · intro p q hpq
    obtain ⟨σ, a, rfl⟩ := Cofan.inj_jointly_surjective_of_isColimit hc p
    obtain ⟨τ, b, rfl⟩ := Cofan.inj_jointly_surjective_of_isColimit hc q
    change (fiberToFinite s).map (galoisOverlapMap Y)
        ((fiber s).map (Sigma.ι (fun _ : Aut Y => Y) σ) a) =
      (fiberToFinite s).map (galoisOverlapMap Y)
        ((fiber s).map (Sigma.ι (fun _ : Aut Y => Y) τ) b) at hpq
    rw [galoisOverlapMap_fiber_ι, galoisOverlapMap_fiber_ι] at hpq
    have hab := congrArg (fun p : Fiber s (productCover Y Y) =>
      p ≫ (productFirst Y Y).hom) hpq
    rw [galoisOverlapGraph_fiber_fst, galoisOverlapGraph_fiber_fst] at hab
    subst b
    have hστ := congrArg (fun p : Fiber s (productCover Y Y) =>
      p ≫ (productSecond Y Y).hom) hpq
    rw [galoisOverlapGraph_fiber_snd, galoisOverlapGraph_fiber_snd] at hστ
    have he : σ = τ := (evaluation_aut_bijective_of_isGalois (fiberToFinite s) Y a).1 hστ
    subst τ
    rfl
  · intro p
    let a : Fiber s Y := p ≫ (productFirst Y Y).hom
    let b : Fiber s Y := p ≫ (productSecond Y Y).hom
    obtain ⟨σ, hσ⟩ := (evaluation_aut_bijective_of_isGalois (fiberToFinite s) Y a).2 b
    refine ⟨(fiber s).map (Sigma.ι (fun _ : Aut Y => Y) σ) a, ?_⟩
    rw [galoisOverlapMap_fiber_ι]
    apply galoisOverlap_fiber_ext Y s
    · exact galoisOverlapGraph_fiber_fst Y s σ a
    · exact (galoisOverlapGraph_fiber_snd Y s σ a).trans hσ

include s in
/-- The actual geometric fibre functor reflects this canonical graph map. -/
theorem galoisOverlapMap_isIso_at : IsIso (galoisOverlapMap Y) :=
  isIso_of_bijective_fiber s (galoisOverlapMap Y) (galoisOverlapMap_fiber_bijective Y s)

end Fiber

instance galoisOverlapMap_isIso : IsIso (galoisOverlapMap Y) :=
  galoisOverlapMap_isIso_at Y
    (algebraicClosureResiduePoint X (Classical.choice (inferInstance : Nonempty X)))

/-- The Galois self-overlap decomposition in the native finite étale category. -/
def galoisOverlapIso : (∐ fun _ : Aut Y => Y) ≅ productCover Y Y :=
  asIso (galoisOverlapMap Y)

/-- The same canonical map on the coproduct of the original underlying schemes. -/
def galoisOverlapSchemeMap :
    (∐ fun _ : Aut Y => Y.obj.left) ⟶ pullback Y.obj.hom Y.obj.hom :=
  Sigma.desc (fun σ => (galoisOverlapGraph Y σ).hom.left)

omit [ConnectedSpace X] [IsGalois Y] in
@[reassoc (attr := simp)]
theorem galoisOverlapSchemeMap_ι (σ : Aut Y) :
    Sigma.ι (fun _ : Aut Y => Y.obj.left) σ ≫ galoisOverlapSchemeMap Y =
      pullback.lift (𝟙 Y.obj.left) σ.hom.hom.left
        (by simpa only [Category.id_comp] using (Over.w σ.hom.hom).symm) :=
  Sigma.ι_comp_desc _ _

/-- Forgetting the cover coproduct gives the original scheme graph map, not a substitute map. -/
theorem galoisOverlapSchemeMap_comparison :
    (PreservesCoproduct.iso (forgetToScheme X) (fun _ : Aut Y => Y)).hom ≫
      galoisOverlapSchemeMap Y = (galoisOverlapMap Y).hom.left := by
  have hc := isColimitOfHasCoproductOfPreservesColimit (forgetToScheme X)
    (fun _ : Aut Y => Y)
  apply hc.hom_ext
  rintro ⟨σ⟩
  change (Sigma.ι (fun _ : Aut Y => Y) σ).hom.left ≫
      ((PreservesCoproduct.iso (forgetToScheme X) (fun _ : Aut Y => Y)).hom ≫
        galoisOverlapSchemeMap Y) =
    (Sigma.ι (fun _ : Aut Y => Y) σ).hom.left ≫ (galoisOverlapMap Y).hom.left
  have hι : (Sigma.ι (fun _ : Aut Y => Y) σ).hom.left ≫
      (PreservesCoproduct.iso (forgetToScheme X) (fun _ : Aut Y => Y)).hom =
        Sigma.ι (fun _ : Aut Y => Y.obj.left) σ := by
    have h := map_ι_comp_inv_sigmaComparison (forgetToScheme X) (fun _ : Aut Y => Y) σ
    change (forgetToScheme X).map (Sigma.ι (fun _ : Aut Y => Y) σ) ≫
        (PreservesCoproduct.iso (forgetToScheme X) (fun _ : Aut Y => Y)).hom =
      Sigma.ι (fun _ : Aut Y => (forgetToScheme X).obj Y) σ
    simpa only [← PreservesCoproduct.inv_hom, IsIso.Iso.inv_inv] using h
  rw [← Category.assoc, hι, galoisOverlapSchemeMap_ι]
  exact (congrArg (fun f : Y ⟶ productCover Y Y => f.hom.left)
    (galoisOverlapMap_ι Y σ)).symm

instance galoisOverlapSchemeMap_isIso : IsIso (galoisOverlapSchemeMap Y) := by
  have : IsIso (galoisOverlapMap Y).hom.left := by
    change IsIso ((forgetToScheme X).map (galoisOverlapMap Y))
    infer_instance
  have : IsIso ((PreservesCoproduct.iso (forgetToScheme X) (fun _ : Aut Y => Y)).hom ≫
      galoisOverlapSchemeMap Y) := by
    rw [galoisOverlapSchemeMap_comparison]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (PreservesCoproduct.iso (forgetToScheme X) (fun _ : Aut Y => Y)).hom
    (galoisOverlapSchemeMap Y)

omit [ConnectedSpace X] [IsGalois Y] in
/-- The original first projection is the identity on every summand. -/
@[reassoc]
theorem galoisOverlapSchemeMap_fst :
    galoisOverlapSchemeMap Y ≫ pullback.fst Y.obj.hom Y.obj.hom =
      Sigma.desc (fun _ : Aut Y => 𝟙 Y.obj.left) := by
  apply Sigma.hom_ext
  intro σ
  simp only [galoisOverlapSchemeMap_ι_assoc, pullback.lift_fst, Sigma.ι_comp_desc]

omit [ConnectedSpace X] [IsGalois Y] in
/-- The original second projection is the deck map on its indexed summand. -/
@[reassoc]
theorem galoisOverlapSchemeMap_snd :
    galoisOverlapSchemeMap Y ≫ pullback.snd Y.obj.hom Y.obj.hom =
      Sigma.desc (fun σ : Aut Y => σ.hom.hom.left) := by
  apply Sigma.hom_ext
  intro σ
  simp only [galoisOverlapSchemeMap_ι_assoc, pullback.lift_snd, Sigma.ι_comp_desc]

/-- The scheme isomorphism from copies indexed by the native deck group to the original overlap. -/
def galoisOverlapSchemeIso :
    (∐ fun _ : Aut Y => Y.obj.left) ≅ pullback Y.obj.hom Y.obj.hom :=
  asIso (galoisOverlapSchemeMap Y)

@[reassoc (attr := simp)]
theorem galoisOverlapSchemeIso_hom_ι (σ : Aut Y) :
    Sigma.ι (fun _ : Aut Y => Y.obj.left) σ ≫ (galoisOverlapSchemeIso Y).hom =
      pullback.lift (𝟙 Y.obj.left) σ.hom.hom.left
        (by simpa only [Category.id_comp] using (Over.w σ.hom.hom).symm) :=
  galoisOverlapSchemeMap_ι Y σ

@[reassoc]
theorem galoisOverlapSchemeIso_hom_fst :
    (galoisOverlapSchemeIso Y).hom ≫ pullback.fst Y.obj.hom Y.obj.hom =
      Sigma.desc (fun _ : Aut Y => 𝟙 Y.obj.left) :=
  galoisOverlapSchemeMap_fst Y

@[reassoc]
theorem galoisOverlapSchemeIso_hom_snd :
    (galoisOverlapSchemeIso Y).hom ≫ pullback.snd Y.obj.hom Y.obj.hom =
      Sigma.desc (fun σ : Aut Y => σ.hom.hom.left) :=
  galoisOverlapSchemeMap_snd Y

/-- The literal deck graphs jointly cover the original self-overlap. -/
theorem galoisOverlapGraph_jointly_surjective (z : (productCover Y Y).obj.left) :
    ∃ (σ : Aut Y) (y : Y.obj.left), (galoisOverlapGraph Y σ).hom.left y = z := by
  obtain ⟨σ, y, hy⟩ :=
    ((sigmaOpenCover (fun _ : Aut Y => Y.obj.left)).pushforwardIso
      (galoisOverlapSchemeIso Y).hom).exists_eq z
  refine ⟨σ, y, ?_⟩
  change (Sigma.ι (fun _ : Aut Y => Y.obj.left) σ ≫ (galoisOverlapSchemeIso Y).hom) y = z at hy
  rw [galoisOverlapSchemeIso_hom_ι] at hy
  exact hy

end AlgebraicGeometry.Scheme.FiniteEtale
