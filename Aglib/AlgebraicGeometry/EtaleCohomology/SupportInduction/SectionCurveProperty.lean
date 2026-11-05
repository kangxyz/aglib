/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.SupportInduction.PointedCurveProperty
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.AffineTargetReturn

/-! # Applying the pointed curve property to the original section component

Geometric connectedness need not be assumed for the original smooth family.
Its actual open section component supplies that hypothesis over a Noetherian
base. The given rank property then produces the target zero, and Cartesian
pasting returns it to the same original class and section mark.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u

attribute [local instance] hasSheafifyLarge hasSheafifyModules HasExt.standard

/-- A proved rank property applies to a possibly disconnected original family
through its whole original section. It is the only vanishing producer used. -/
theorem exists_pointed_H1_refinement_of_section_of_rank_property
    (d : ℕ) (ih : PointedCurveModuleInjectiveH1Effacement.{u} d)
    (R S : Type u) [CommRing R] [CommRing S] [IsNoetherianRing R]
    (hR : IsNagataRing.{u, 0} R) (hS : IsNagataRing.{u, 0} S)
    (hd : ringKrullDim S ≤ d)
    {G Y : Scheme.{u}} (p : G ⟶ Spec (.of R))
    [SmoothOfRelativeDimension 1 p] [QuasiCompact p] [QuasiSeparated p]
    (σ : Spec (.of R) ⟶ G) (hσ : σ ≫ p = 𝟙 _)
    (haff : ∀ (F : Type u) [Field F] (f : Spec (.of F) ⟶ Spec (.of R)),
      IsAffine (pullback p f : Scheme.{u}))
    (β : Spec (.of S) ⟶ Spec (.of R))
    (a : Y ⟶ G) (b : Y ⟶ Spec (.of S)) (H : IsPullback a b p β)
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : R))
    (I : ModuleSheaf (Spec (.of S)) (ULift.{u + 1} (ZMod n))) [Injective I]
    (c : Sheaf.H.{u + 2} ((inverseImage b).obj
      ((SheafOfModules.toSheaf (constantRing (Spec (.of S))
        (ULift.{u + 1} (ZMod n)))).obj I)) 1)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ Spec (.of R)) :
    ∃ (U : G.Etale) (xU : Spec (.of Ω) ⟶ U.left),
      xU ≫ U.hom = x ≫ σ ∧
      cohomologyPullback.{u, u + 2, u + 2} (pullback.snd U.hom a) _ 1 c = 0 := by
  obtain ⟨W, τ, _, hτ, hτp, hsm, hqc, hqs, hgc, hWaff⟩ :=
    exists_noetherian_sectionComponent_restriction_affine_fibers R p 1 σ hσ haff
  let : SmoothOfRelativeDimension 1 (W.ι ≫ p) := hsm
  let : QuasiCompact (W.ι ≫ p) := hqc
  let : QuasiSeparated (W.ι ≫ p) := hqs
  let : GeometricallyConnected (W.ι ≫ p) := hgc
  let aW := pullback.fst W.ι a
  let v := pullback.snd W.ι a
  let F := (SheafOfModules.toSheaf (constantRing (Spec (.of S))
    (ULift.{u + 1} (ZMod n)))).obj I
  let cW := Sheaf.H.map ((inverseImageComp b v).inv.app F) 1
    (cohomologyPullback.{u, u + 2, u + 2} v ((inverseImage b).obj F) 1 c)
  have HW : IsPullback aW (v ≫ b) (W.ι ≫ p) β :=
    (IsPullback.of_hasPullback W.ι a).paste_vert H
  obtain ⟨U, z, hz, hc⟩ := ih R S hR hS hd (W.ι ≫ p) τ hτp hWaff
    β aW (v ≫ b) HW n hn hunit I cW Ω x
  let V : G.Etale := Scheme.Etale.mk (U.hom ≫ W.ι)
  refine ⟨V, z, ?_, ?_⟩
  · change z ≫ U.hom ≫ W.ι = x ≫ σ
    rw [← Category.assoc, hz, Category.assoc, hτ]
  · exact Finite.target_composite_zero_of_coefficient_restriction_zero
      W.ι a U.hom b F 1 c hc

end AlgebraicGeometry.Scheme.EtaleCohomology
