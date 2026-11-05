/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.ProperSubalgebraModel
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.FiniteTypeBaseChangeLimit
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ConstructibleModels
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.Pullback
public import Aglib.CategoryTheory.Over.PullbackMapSquare

/-! # Proper Noetherian models with the original constructible coefficient

The original proper finitely presented morphism is first modeled geometrically.
Constructible coefficient descent is then applied to the actual source limit
of that same model. The result retains a Cartesian square with the original
morphism and an actual inverse-image isomorphism to the original coefficient.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

attribute [local instance] ModuleCat.Sheaf.hasSheafify

variable (Λ : Type (u + 1)) [Ring Λ] [IsNoetherianRing Λ]

open Constructible
open Continuity.NativeModule Continuity.NativeModule.ModelDescent
open Constructible.Modules
open Scheme.FiniteTypeSubalgebraLimit Algebra.FiniteTypeSubalgebraLimit

private def moduleInverseImageIsoCancel {X Y : Scheme.{u}} (e : X ≅ Y)
    (F : ModuleSheaf Λ X) :
    (moduleInverseImage Λ e.hom).obj ((moduleInverseImage Λ e.inv).obj F) ≅ F :=
  ((moduleInverseImageComp Λ e.inv e.hom).app F).symm ≪≫
    eqToIso (congrArg (fun a : X ⟶ X => (moduleInverseImage Λ a).obj F) e.hom_inv_id) ≪≫
      ((schemeAdjunctionData Λ).leftIdIso (op X)).app F

/-- An actual constructible native module coefficient and its proper finitely
presented morphism over an arbitrary spectrum descend together to a proper
Noetherian model. No coefficient-model certificate is an input. -/
theorem exists_proper_noetherian_constructible_module_model
    (R : Type u) [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsProper f] [LocallyOfFinitePresentation f]
    (F : ModuleSheaf Λ X) (hF : Constructible.Modules.IsConstructible F) :
    ∃ (Y T : Scheme.{u}) (g : Y ⟶ T) (a : Spec (.of R) ⟶ T) (p : X ⟶ Y),
      IsNoetherian T ∧ IsProper g ∧ IsPullback p f g a ∧
      ∃ G : ModuleSheaf Λ Y,
        Constructible.Modules.IsConstructible G ∧
          Nonempty ((moduleInverseImage Λ p).obj G ≅ F) := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  obtain ⟨s, M₀, hM₀⟩ :=
    exists_properModel_over_finiteTypeSubalgebra ℤ R f
  let B := stage ℤ R s
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℤ B
  let M : Scheme.FinitePresentationDescent.Model (Spec.algebraMap B R) f := M₀
  let : IsProper M.f := hM₀
  let D := schemeDiagram B R M.f
  let c := schemeCone B R M.f
  let hc := schemeConeIsLimit B R M.f
  let b : c.pt ⟶ Spec (.of R) := pullback.fst (Spec.algebraMap B R) M.f
  let : IsProper b := inferInstanceAs (IsProper (pullback.fst (Spec.algebraMap B R) M.f))
  let : CompactSpace c.pt := QuasiCompact.compactSpace_of_compactSpace b
  let : c.pt.IsSeparated := ⟨by rw [← terminal.comp_from b]; infer_instance⟩
  let e : X ≅ c.pt := M.rawIso
  let F' := (moduleInverseImage Λ e.inv).obj F
  have hF' : Constructible.Modules.IsConstructible F' :=
    Constructible.Modules.isConstructible_pullback (R := Λ) e.inv hF
  have (i : (Finset R)ᵒᵖ) : (D.obj i).IsSeparated := by
    let g : D.obj i ⟶ Spec (.of (stage B R i.unop)) :=
      pullback.fst (Spec.algebraMap B (stage B R i.unop)) M.f
    have : IsProper g :=
      inferInstanceAs (IsProper (pullback.fst (Spec.algebraMap B (stage B R i.unop)) M.f))
    constructor
    rw [← terminal.comp_from g]
    infer_instance
  have (i : (Finset R)ᵒᵖ) : CompactSpace (D.obj i) :=
    inferInstanceAs (CompactSpace ((schemeDiagram B R M.f).obj i))
  have {i j : (Finset R)ᵒᵖ} (q : i ⟶ j) : IsAffineHom (D.map q) :=
    inferInstanceAs (IsAffineHom ((schemeDiagram B R M.f).map q))
  obtain ⟨i, _, G₀, hG₀, ⟨eG⟩⟩ := exists_constructible_object_model Λ D c hc (op ∅) F' hF'
  let C := stage B R i.unop
  let : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing B C
  let g : D.obj i ⟶ Spec (.of C) := pullback.fst (Spec.algebraMap B C) M.f
  let a : Spec (.of R) ⟶ Spec (.of C) := Spec.algebraMap C R
  let p := e.hom ≫ c.π.app i
  have H₀ : IsPullback (c.π.app i) b g a :=
    (Over.pullback_map_isPullback M.f ((baseCone B R).π.app i)).flip
  have H : IsPullback p f g a :=
    H₀.of_iso' e (.refl _) (.refl _) (.refl _)
      (by simp [p]) (by
        dsimp only [e, b, Iso.refl_hom]
        rw [Category.comp_id]
        exact M.rawIso_hom_fst)
      (by simp) (by simp)
  let G := G₀
  let ep : (moduleInverseImage Λ p).obj G ≅ F :=
    (moduleInverseImageComp Λ (c.π.app i) e.hom).app G ≪≫
      (moduleInverseImage Λ e.hom).mapIso eG ≪≫ moduleInverseImageIsoCancel Λ e F
  refine ⟨D.obj i, Spec (.of C), g, a, p, inferInstance, ?_, H, G, hG₀, ⟨ep⟩⟩
  exact inferInstanceAs (IsProper (pullback.fst (Spec.algebraMap B C) M.f))

end AlgebraicGeometry.Scheme.EtaleCohomology
