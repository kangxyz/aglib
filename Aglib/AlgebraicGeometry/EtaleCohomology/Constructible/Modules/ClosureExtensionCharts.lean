/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ClosureCharts
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantFiniteGenerators

/-! # Actual finite-generator charts for module extensions

An epimorphism onto a constant finite module admits actual etale charts and
finite constant sources whose composites onto the quotient are epic. The
maps retain the native inverse image and the original quotient morphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable {R : Type r} [CommRing R] {X : Scheme.{u}}

/-- Finite quotient generators lift on actual etale charts, without a local
splitting or a free module in an enlarged value universe. -/
theorem exists_constant_generating_chart
    {N : ModuleCat.{u + 1} R} [Module.Finite R N] (F : ModuleSheaf R X)
    (p : F ⟶ (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj N)
    [Epi p] (x : X) :
    ∃ (U : X.Etale) (y : U.left), U.hom y = x ∧
      ∃ M : ModuleCat.{u + 1} R, Module.Finite R M ∧
        ∃ a : (constantSheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M ⟶
          (moduleInverseImage R U.hom).obj F,
          Epi (a ≫ (moduleInverseImage R U.hom).map p) := by
  obtain ⟨T, hT, h⟩ := ModuleCat.Sheaf.exists_cover_constant_generators
    X.smallEtaleTopology F p (etaleTerminal X)
  let P : MorphismProperty Scheme.{u} := fun {S T} (g : S ⟶ T) => Etale g
  have htop := congrArg
    (fun J : GrothendieckTopology X.Etale => T ∈ J (etaleTerminal X))
    (Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology X
      (P := P) (Q := P) le_rfl)
  have hpoints : ∀ z : X, ∃ (U : X.Etale) (f : U ⟶ etaleTerminal X) (y : U.left),
      T f ∧ Etale f.left ∧ (f.left : U.left ⟶ X) y = z :=
    (Scheme.mem_toGrothendieck_smallPretopology
      (P := P) (Q := P) (etaleTerminal X) T).mp (Eq.mp htop hT)
  obtain ⟨U, f, y, hf, _, hy⟩ := hpoints x
  obtain ⟨M, hM, a, ha⟩ := h f hf
  let E : Sheaf (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} R) ⥤
      ModuleSheaf R U.left := (moduleEtaleSliceEquivalence R U).inverse
  let e : X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} R) U ⋙ E ≅
      moduleInverseImage R U.hom :=
    moduleEtaleSliceRestrictionIso R U ≪≫ (moduleInverseImageEtaleIso R U.hom).symm
  let c : (constantSheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M ≅
      E.obj ((constantSheaf (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} R)).obj M) :=
    (moduleEtaleSliceConstantIso R U).app M
  let b := c.hom ≫ E.map a ≫ e.hom.app F
  refine ⟨U, y, ?_, M, hM, b, ?_⟩
  · have hf' : (f.left : U.left ⟶ X) = U.hom := by
      have hw := MorphismProperty.Over.w f
      change f.left ≫ 𝟙 X = U.hom at hw
      exact (Category.comp_id f.left).symm.trans hw
    exact (congrArg (fun k : U.left ⟶ X => k y) hf').symm.trans hy
  · let := ha
    let : E.PreservesEpimorphisms :=
      Functor.preservesEpimorphisms_of_adjunction
        (moduleEtaleSliceEquivalence R U).symm.toAdjunction
    have hb : b ≫ (moduleInverseImage R U.hom).map p =
        c.hom ≫ E.map (a ≫ (X.smallEtaleTopology.overPullback
          (ModuleCat.{u + 1} R) U).map p) ≫ e.hom.app _ := by
      simp only [b, Category.assoc, E.map_comp]
      exact congrArg
        (fun k : E.obj ((X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} R) U).obj F) ⟶
            (moduleInverseImage R U.hom).obj
              ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj N) =>
          c.hom ≫ E.map a ≫ k) (e.hom.naturality p).symm
    rw [hb]
    exact epi_comp' (IsIso.epi_of_iso c.hom)
      (epi_comp' (Functor.map_epi E _) (IsIso.epi_of_iso (e.hom.app
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj N))))

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
