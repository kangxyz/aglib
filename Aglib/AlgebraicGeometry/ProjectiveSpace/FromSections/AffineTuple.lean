/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.FromSections.AffineChart
public import Aglib.AlgebraicGeometry.Modules.Pullback.UnitMultiplication

/-!
# Projective maps of affine tuples on arbitrary schemes

A finite tuple of actual global sections gives the projective homogeneous
family `(1,s)`. Its map is natural under every scheme morphism, retaining the
original base map and the actual pullback of each section. On spectra it is
identified with the existing affine-chart family and chart map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.ProjectiveSpace.FromSections.AffineTuple

variable (X : Scheme.{u}) {I : Type u}

/-- The actual unit-sheaf coordinate family on an arbitrary scheme. -/
def family (s : I → Γ(X, ⊤)) (i : Option I) :
    SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf :=
  unitMul X (Option.elim i 1 s)

/-- The distinguished coordinate is literally the identity, so generation
requires no condition on the tuple. -/
instance family_epi (s : I → Γ(X, ⊤)) : Epi (Sigma.desc (family X s)) := by
  have h : Sigma.ι (fun _ : Option I ↦ SheafOfModules.unit X.ringCatSheaf) none ≫
      Sigma.desc (family X s) = 𝟙 _ := by
    rw [Sigma.ι_comp_desc]
    exact unitMul_one X
  exact epi_of_epi_fac h

/-- The structure module has its canonical local rank-one frame. -/
theorem unit_locallyRankOne : IsLocallyRankOne X (SheafOfModules.unit X.ringCatSheaf) := by
  rw [isLocallyRankOne_iff_local_unit]
  intro x
  exact ⟨⊤, trivial, ⟨Iso.refl _⟩⟩

variable {X} {Y : Scheme.{u}}

/-- The pulled family has exactly the original pulled global sections. -/
theorem family_pullback (g : Y ⟶ X) (s : I → Γ(X, ⊤)) (i : Option I) :
    pulledFamily g (family X s) i ≫ (pullbackUnitIso g).hom =
      family Y (g.appTop ∘ s) i := by
  change (pullbackUnitIso g).inv ≫ (Scheme.Modules.pullback g).map
      (unitMul X (Option.elim i 1 s)) ≫ (pullbackUnitIso g).hom = _
  rw [unitMul_pullback, Iso.inv_hom_id_assoc]
  cases i with
  | none => simp only [Option.elim_none, map_one, family]
  | some i => rfl

variable {R : Type u} [CommRing R] [Finite I]

/-- The original finite affine tuple as an actual projective scheme morphism. -/
def map (p : X ⟶ Spec (.of R)) (s : I → Γ(X, ⊤)) : X ⟶ ProjectiveSpace R (Option I) := by
  letI : Epi (Sigma.desc (family X s)) := family_epi X s
  exact mapOfFiniteFamily p (SheafOfModules.unit X.ringCatSheaf)
    (unit_locallyRankOne X) (family X s)

@[reassoc]
theorem map_toSpec (p : X ⟶ Spec (.of R)) (s : I → Γ(X, ⊤)) :
    map p s ≫ ProjectiveSpace.toSpec R (Option I) = p := by
  let : Epi (Sigma.desc (family X s)) := family_epi X s
  exact mapOfFiniteFamily_toSpec _ _ _ _

/-- Equality of actual scheme morphisms under arbitrary pullback, not merely
of their projective coordinate classes. -/
theorem map_naturality (g : Y ⟶ X) (p : X ⟶ Spec (.of R)) (s : I → Γ(X, ⊤)) :
    g ≫ map p s = map (g ≫ p) (g.appTop ∘ s) := by
  let : Epi (Sigma.desc (family X s)) := family_epi X s
  let : Epi (Sigma.desc (family Y (g.appTop ∘ s))) := family_epi Y (g.appTop ∘ s)
  have heq : (fun i ↦ pulledFamily g (family X s) i ≫ (pullbackUnitIso g).hom) =
      family Y (g.appTop ∘ s) := funext (family_pullback g s)
  unfold map
  simpa only [heq] using mapOfFiniteFamily_pullback_iso g p
    (SheafOfModules.unit X.ringCatSheaf) (unit_locallyRankOne X)
    (family X s) (SheafOfModules.unit Y.ringCatSheaf) (pullbackUnitIso g)

variable {S : Type u} [CommRing S]

omit [Finite I] in
/-- The spectrum specialization is the existing affine-chart family, with
its original scalar identification by the canonical global-sections iso. -/
theorem family_spec (s : I → S) :
    family (Spec (.of S)) ((Scheme.ΓSpecIso (.of S)).inv ∘ s) = AffineChart.family s := by
  funext i
  cases i with
  | none =>
    simp only [family, AffineChart.family, AffineChart.coordinates, Option.elim_none, map_one]
  | some i => rfl

/-- The arbitrary-scheme tuple map recovers the original standard affine
chart map over the actual ring homomorphism. -/
theorem map_spec (φ : R →+* S) (s : I → S) :
    map (Spec.map (CommRingCat.ofHom φ)) ((Scheme.ΓSpecIso (.of S)).inv ∘ s) =
      AffineChart.map φ s := by
  let : Epi (Sigma.desc (family (Spec (.of S)) ((Scheme.ΓSpecIso (.of S)).inv ∘ s))) :=
    family_epi _ _
  unfold map
  refine (@mapOfFiniteFamily_iso R _ (Option I) (Spec (.of S))
    (Spec.map (CommRingCat.ofHom φ))
    (SheafOfModules.unit (Spec (.of S)).ringCatSheaf)
    (SheafOfModules.unit (Spec (.of S)).ringCatSheaf)
    (unit_locallyRankOne _) (unit_locallyRankOne _) inferInstance
    (family (Spec (.of S)) ((Scheme.ΓSpecIso (.of S)).inv ∘ s))
    (AffineChart.family s) (family_epi _ _) (AffineChart.family_epi s)
    (Iso.refl _) (fun i ↦ ?_)).trans ?_
  · exact (Category.comp_id _).trans (congrFun (family_spec s) i)
  · exact AffineChart.mapOfFiniteFamily_eq φ s (unit_locallyRankOne _)

end AlgebraicGeometry.ProjectiveSpace.FromSections.AffineTuple
