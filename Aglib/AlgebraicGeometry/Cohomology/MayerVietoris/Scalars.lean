/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Scalars.Open
public import Aglib.AlgebraicGeometry.Cohomology.MayerVietoris.GeometricTop
public import Mathlib.Algebra.Homology.ShortComplex.ConcreteCategory

/-! # The native Mayer–Vietoris sequence over a structural ring

The existing coefficient scalar action makes the actual native open-Ext
Mayer–Vietoris sequence a sequence of modules. Forgetting scalars identifies
its maps and exactness with the original native additive sequence. The
whole-space linear comparison retains the unchanged `Sheaf.H` action.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open CategoryTheory.Abelian CategoryTheory.ComposableArrows

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts

namespace AlgebraicGeometry.Scheme.Cohomology

variable (X : Scheme.{u}) {R : Type u} [CommRing R]
  (α : R →+* Γ(X, ⊤)) (M : X.Modules)

/-- The original native whole-space comparison is linear for the actual coefficient action. -/
def moduleHPrimeTopLinearEquivOfHom (n : ℕ) :
    letI := moduleHPrimeModuleOfHom X α M n ⊤
    letI := moduleCohomologyModuleOfHom X α M n
    Sheaf.H'.{u + 1} (moduleAddSheaf X M) n ⊤ ≃ₗ[R]
      Sheaf.H.{u + 1} (moduleAddSheaf X M) n := by
  letI := moduleHPrimeModuleOfHom X α M n ⊤
  letI := moduleCohomologyModuleOfHom X α M n
  exact {
    __ := sheafHPrimeTopAddEquiv X (moduleAddSheaf X M) n
    map_smul' := fun a x =>
      sheafHPrimeTopAddEquiv_naturality X (moduleScalarOfGlobal X M (α a)) n x }

/-- The signed native Mayer–Vietoris connecting map, retaining the structural scalars. -/
def moduleMayerVietorisDelta (U V : X.Opens) (n : ℕ) :
    (moduleHPrimePresheaf X α M n).obj (op (U ⊓ V)) ⟶
      (moduleHPrimePresheaf X α M (n + 1)).obj (op (U ⊔ V)) := by
  letI := moduleHPrimeModuleOfHom X α M n (U ⊓ V)
  letI := moduleHPrimeModuleOfHom X α M (n + 1) (U ⊔ V)
  refine ModuleCat.ofHom {
    __ := ((Opens.mayerVietorisSquare U V).δ (moduleAddSheaf X M) n (n + 1) rfl).hom
    map_smul' := fun a x => ?_ }
  exact (ConcreteCategory.congr_hom
    (mayerVietoris_delta_coefficient U V (moduleScalarOfGlobal X M (α a)) n) x).symm

/-- The original sum of native restrictions, with structural scalars retained. -/
def moduleMayerVietorisToBiprod (U V : X.Opens) (n : ℕ) :
    (moduleHPrimePresheaf X α M n).obj (op (U ⊔ V)) ⟶
      (moduleHPrimePresheaf X α M n).obj (op U) ⊞
        (moduleHPrimePresheaf X α M n).obj (op V) :=
  biprod.lift
    ((moduleHPrimePresheaf X α M n).map (homOfLE (show U ≤ U ⊔ V from le_sup_left)).op)
    ((moduleHPrimePresheaf X α M n).map (homOfLE (show V ≤ U ⊔ V from le_sup_right)).op)

/-- The original difference of native restrictions, with structural scalars retained. -/
def moduleMayerVietorisFromBiprod (U V : X.Opens) (n : ℕ) :
    (moduleHPrimePresheaf X α M n).obj (op U) ⊞
        (moduleHPrimePresheaf X α M n).obj (op V) ⟶
      (moduleHPrimePresheaf X α M n).obj (op (U ⊓ V)) :=
  biprod.desc
    ((moduleHPrimePresheaf X α M n).map (homOfLE (show U ⊓ V ≤ U from inf_le_left)).op)
    (-((moduleHPrimePresheaf X α M n).map (homOfLE (show U ⊓ V ≤ V from inf_le_right)).op))

/-- The native six-term Mayer–Vietoris sequence with the actual structural ring action. -/
def moduleMayerVietorisSequence (U V : X.Opens) (n : ℕ) :
    ComposableArrows (ModuleCat.{u + 1} R) 5 :=
  mk₅ (moduleMayerVietorisToBiprod X α M U V n)
    (moduleMayerVietorisFromBiprod X α M U V n) (moduleMayerVietorisDelta X α M U V n)
    (moduleMayerVietorisToBiprod X α M U V (n + 1))
    (moduleMayerVietorisFromBiprod X α M U V (n + 1))

/-- Forgetting scalars recovers the original native Mayer–Vietoris sequence and all its maps. -/
def moduleMayerVietorisSequenceForgetIso (U V : X.Opens) (n : ℕ) :
    moduleMayerVietorisSequence X α M U V n ⋙
        forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1} ≅
      (Opens.mayerVietorisSquare U V).sequence (moduleAddSheaf X M) n (n + 1) rfl := by
  let G := forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}
  let P := moduleHPrimePresheaf X α M n
  let Q := moduleHPrimePresheaf X α M (n + 1)
  refine isoMk₅ (Iso.refl _) (G.mapBiprod (P.obj (op U)) (P.obj (op V)))
    (Iso.refl _) (Iso.refl _) (G.mapBiprod (Q.obj (op U)) (Q.obj (op V)))
    (Iso.refl _) ?_ ?_ ?_ ?_ ?_
  · erw [Category.id_comp]
    exact biprod.map_lift_mapBiprod G _ _ _ _
  · erw [Category.comp_id]
    symm
    change (G.mapBiprod (P.obj (op U)) (P.obj (op V))).hom ≫
      biprod.desc (G.map (P.map (homOfLE (show U ⊓ V ≤ U from inf_le_left)).op))
        (-(G.map (P.map (homOfLE (show U ⊓ V ≤ V from inf_le_right)).op))) =
      G.map (biprod.desc (P.map (homOfLE (show U ⊓ V ≤ U from inf_le_left)).op)
        (-(P.map (homOfLE (show U ⊓ V ≤ V from inf_le_right)).op)))
    rw [← G.map_neg]
    exact biprod.mapBiprod_hom_desc G _ _ _ _
  · erw [Category.id_comp, Category.comp_id]
    rfl
  · erw [Category.id_comp]
    exact biprod.map_lift_mapBiprod G _ _ _ _
  · erw [Category.comp_id]
    symm
    change (G.mapBiprod (Q.obj (op U)) (Q.obj (op V))).hom ≫
      biprod.desc (G.map (Q.map (homOfLE (show U ⊓ V ≤ U from inf_le_left)).op))
        (-(G.map (Q.map (homOfLE (show U ⊓ V ≤ V from inf_le_right)).op))) =
      G.map (biprod.desc (Q.map (homOfLE (show U ⊓ V ≤ U from inf_le_left)).op)
        (-(Q.map (homOfLE (show U ⊓ V ≤ V from inf_le_right)).op)))
    rw [← G.map_neg]
    exact biprod.mapBiprod_hom_desc G _ _ _ _

/-- Exactness of the original native Mayer–Vietoris sequence over the structural ring. -/
theorem moduleMayerVietorisSequence_exact (U V : X.Opens) (n : ℕ) :
    (moduleMayerVietorisSequence X α M U V n).Exact := by
  let S := moduleMayerVietorisSequence X α M U V n
  let G := forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}
  have hG : ComposableArrows.Exact (S ⋙ G) := exact_of_iso
    (moduleMayerVietorisSequenceForgetIso X α M U V n).symm
    ((Opens.mayerVietorisSquare U V).sequence_exact (moduleAddSheaf X M) n (n + 1) rfl)
  have hz : S.IsComplex := ⟨fun i hi => by
    apply G.map_injective
    rw [G.map_comp, G.map_zero]
    exact hG.toIsComplex.zero i hi⟩
  refine { toIsComplex := hz, exact := fun i hi => ?_ }
  exact ((S.sc hz i hi).exact_map_iff_of_faithful G).mp (hG.exact i hi)

end AlgebraicGeometry.Scheme.Cohomology
