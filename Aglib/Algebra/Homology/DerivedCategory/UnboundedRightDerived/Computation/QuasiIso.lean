/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.Computation.Cycles
public import Aglib.Algebra.Homology.MappingCone.Acyclicity
public import Aglib.Algebra.Homology.MappingCone.QuasiIso

/-! # Finite-dimensional computation preserves the original quasi-isomorphisms

Apply dimension shifting to the actual signed cone. No alternative resolution
or alternative derived functor is constructed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex

universe s u v w u' v' w'

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [IsGrothendieckAbelian.{s} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]

/-- Original quasi-isomorphisms between complexes of acyclic coefficients remain
quasi-isomorphisms under termwise application of a finite-dimensional functor. -/
theorem quasiIso_map_of_acyclic_terms_of_bound
    {K L : CochainComplex C ℤ} (f : K ⟶ L) [QuasiIso f]
    (hK : ∀ i : ℤ, ∀ n : ℕ, IsZero ((F.rightDerived (n + 1)).obj (K.X i)))
    (hL : ∀ i : ℤ, ∀ n : ℕ, IsZero ((F.rightDerived (n + 1)).obj (L.X i)))
    (N : ℕ) (hbound : ∀ M : C, IsZero ((F.rightDerived (N + 1)).obj M)) :
    QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map f) := by
  have hterms (i : ℤ) (n : ℕ) :
      IsZero ((F.rightDerived (n + 1)).obj ((mappingCone f).X i)) := by
    let G := F.rightDerived (n + 1)
    let : G.Additive :=
      Functor.additive_of_iso (F.rightDerivedSingleHomologyIso (n + 1)).symm
    let : PreservesBinaryBiproducts G :=
      preservesBinaryBiproducts_of_preservesBiproducts G
    let e : G.obj ((mappingCone f).X i) ≅ G.obj (K.X (i + 1)) ⊞ G.obj (L.X i) :=
      G.mapIso (HomologicalComplex.homotopyCofiber.XIsoBiprod f i (i + 1) rfl) ≪≫
        G.mapBiprod _ _
    exact e.isZero_iff.mpr ((biprod_isZero_iff _ _).mpr ⟨hK _ _, hL _ _⟩)
  have h := F.acyclic_map_of_acyclic_terms_of_bound (mappingCone f)
    (mappingCone_acyclic_of_quasiIso f) hterms N hbound
  apply quasiIso_of_mappingCone_acyclic
  intro i
  exact (h i).of_iso (mappingCone.mapHomologicalComplexIso f F)

end CategoryTheory.Functor
