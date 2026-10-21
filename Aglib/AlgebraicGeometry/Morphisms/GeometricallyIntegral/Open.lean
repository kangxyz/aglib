/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.GlobalSections
public import Aglib.AlgebraicGeometry.Cohomology.Proper.H0Vanishing
public import Aglib.AlgebraicGeometry.Cohomology.Proper.StructureSheaf.Sections
public import Aglib.AlgebraicGeometry.Geometrically.Integral.GlobalSections
public import Aglib.AlgebraicGeometry.Geometrically.Integral.SmoothCurve
public import Aglib.AlgebraicGeometry.Morphisms.Proper.ConnectedFibres

/-!
# Geometrically integral fibres near the generic point of a smooth proper curve family

The actual degree-zero fibre cohomology, with its original residue-field scalar
action, determines the open neighbourhood. Properness and a nonempty generic
fibre give nonempty fibres everywhere. On the locus where the dimension is less
than two, the actual constants map is bijective; proper connected-fibre theory
and smooth relative dimension one then give geometric integrality.

The scope is smooth proper relative curves over a locally Noetherian integral
base. No unrestricted openness theorem for arbitrary flat families is asserted.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open scoped TensorProduct
open AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.OverField

universe u

namespace AlgebraicGeometry.Scheme

/-- Over a field, bijectivity of the actual constants map makes the entire
structure-sheaf map invertible. -/
theorem isIso_c_of_bijective_constants {K : Type u} [Field K]
    (X : FScheme K) (h : Function.Bijective (constants X)) : IsIso X.hom.c := by
  have htop : IsIso X.hom.appTop := by
    have hcomp : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ X.hom.appTop) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr h
    exact IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of K)).inv X.hom.appTop
  have happ (U : (Spec (.of K)).Opens) : IsIso (X.hom.app U) := by
    rcases U.eq_bot_or_top with rfl | rfl
    · apply (ConcreteCategory.isIso_iff_bijective _).mpr
      have : Subsingleton Γ(X.left, X.hom ⁻¹ᵁ (⊥ : (Spec (.of K)).Opens)) := by
        simp only [Scheme.Hom.preimage_bot]
        infer_instance
      exact ⟨Function.injective_of_subsingleton _, Function.surjective_to_subsingleton _⟩
    · exact htop
  have (U : (Spec (.of K)).Opensᵒᵖ) : IsIso (X.hom.c.app U) := happ U.unop
  exact NatIso.isIso_of_isIso_app X.hom.c

/-- The degree-zero cohomology of the pulled structure module is the actual
global-sections module of that same fibre, with the same structural scalars. -/
def pointFiberUnitH0SectionsEquiv {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) :
    let Z : FScheme (Y.residueField y) := Over.mk (f.fiberToSpecResidueField y)
    letI := globalSectionsModule Z
    modulePointFiberCohomology f (SheafOfModules.unit X.ringCatSheaf) 0 y ≃ₗ[Y.residueField y]
      Γ(Z.left, ⊤) := by
  let Z : FScheme (Y.residueField y) := Over.mk (f.fiberToSpecResidueField y)
  letI := globalSectionsModule Z
  let e : modulePointFiberCohomology f (SheafOfModules.unit X.ringCatSheaf) 0 y
      →ₗ[Y.residueField y] Γ(Z.left, ⊤) :=
    { __ := pullbackUnitSections (f.fiberι y)
      map_smul' := fun a x => pullbackUnitSections_scalar (f.fiberι y)
        ((f.fiberToSpecResidueField y).appTop ((Scheme.ΓSpecIso (Y.residueField y)).inv a)) x }
  exact LinearEquiv.ofBijective e (pullbackUnitSections_bijective (f.fiberι y))

/-- Properness makes every actual fibre nonempty when the generic fibre of an
irreducible base is nonempty. -/
theorem surjective_of_isProper_of_nonempty_generic_fiber {X Y : Scheme.{u}}
    [IrreducibleSpace Y] (f : X ⟶ Y) [IsProper f]
    [Nonempty (f.fiber (genericPoint Y))] : Surjective f := by
  obtain ⟨z⟩ := (inferInstance : Nonempty (f.fiber (genericPoint Y)))
  have hη : genericPoint Y ∈ Set.range f := by
    have hz := (f.range_fiberι (genericPoint Y)).le ⟨z, rfl⟩
    exact ⟨f.fiberι (genericPoint Y) z, hz⟩
  have hdense : DenseRange f := by
    rw [denseRange_iff_closure_range]
    apply Set.eq_univ_of_univ_subset
    rw [← genericPoint_closure (α := Y)]
    exact closure_mono (Set.singleton_subset_iff.mpr hη)
  let : IsDominant f := ⟨hdense⟩
  infer_instance

/-- Dimension one of the actual fibre H⁰ makes its constants map bijective.
Nonemptiness is explicit, so the field-to-sections map is injective. -/
theorem bijective_constants_of_pointFiberUnitH0_finrank_eq_one
    {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) [Nonempty (f.fiber y)]
    (hdim : modulePointFiberCohomologyDimension f
      (SheafOfModules.unit X.ringCatSheaf) 0 y = 1) :
    Function.Bijective (constants (Over.mk (f.fiberToSpecResidueField y))) := by
  let Z : FScheme (Y.residueField y) := Over.mk (f.fiberToSpecResidueField y)
  let := globalSectionsModule Z
  let : Nonempty (⊤ : Z.left.Opens) :=
    ⟨⟨Classical.choice (inferInstance : Nonempty (f.fiber y)), trivial⟩⟩
  have hdim' : Module.finrank (Y.residueField y) Γ(Z.left, ⊤) = 1 :=
    (pointFiberUnitH0SectionsEquiv f y).finrank_eq.symm.trans hdim
  let : Module.Finite (Y.residueField y) Γ(Z.left, ⊤) :=
    Module.finite_of_finrank_eq_succ hdim'
  let c : Y.residueField y →ₗ[Y.residueField y] Γ(Z.left, ⊤) :=
    { __ := (constants Z).toAddMonoidHom
      map_smul' := fun a b => (constants Z).map_mul a b }
  have hc : Function.Injective c := (constants Z).injective
  exact ⟨hc, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by simpa using hdim'.symm) (f := c)).mp hc⟩

/-- For a proper smooth relative curve, the actual nonempty fibre with H⁰
dimension one is geometrically integral. -/
theorem geometricallyIntegral_fiber_of_pointFiberUnitH0_finrank_eq_one
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (y : Y) [Nonempty (f.fiber y)]
    (hdim : modulePointFiberCohomologyDimension f
      (SheafOfModules.unit X.ringCatSheaf) 0 y = 1) :
    GeometricallyIntegral (f.fiberToSpecResidueField y) := by
  let q := f.fiberToSpecResidueField y
  let : IsProper q := MorphismProperty.pullback_snd _ _ inferInstance
  let : SmoothOfRelativeDimension 1 q := MorphismProperty.pullback_snd _ _ inferInstance
  let : Surjective q := ⟨Function.surjective_to_subsingleton q⟩
  let : IsIso q.c := isIso_c_of_bijective_constants (Over.mk q)
    (bijective_constants_of_pointFiberUnitH0_finrank_eq_one f y hdim)
  let : GeometricallyConnected q := geometricallyConnected_of_isProper_of_isIso_c q
  exact geometricallyIntegral_of_smoothOfRelativeDimension_one_of_geometricallyConnected q

/-- Geometric integrality of the actual proper fibre gives dimension one for
its actual structure-module cohomology with the original residue-field action. -/
theorem pointFiberUnitH0_finrank_eq_one_of_geometricallyIntegral
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (y : Y)
    [GeometricallyIntegral (f.fiberToSpecResidueField y)] :
    modulePointFiberCohomologyDimension f (SheafOfModules.unit X.ringCatSheaf) 0 y = 1 := by
  let Z : FScheme (Y.residueField y) := Over.mk (f.fiberToSpecResidueField y)
  let := globalSectionsModule Z
  let : IsProper Z.hom := MorphismProperty.pullback_snd _ _ inferInstance
  let : GeometricallyIntegral Z.hom :=
    inferInstanceAs (GeometricallyIntegral (f.fiberToSpecResidueField y))
  let c : Y.residueField y →ₗ[Y.residueField y] Γ(Z.left, ⊤) :=
    { __ := (constants Z).toAddMonoidHom
      map_smul' := fun a b => (constants Z).map_mul a b }
  let e := LinearEquiv.ofBijective c (constants_bijective_of_proper_geometricallyIntegral Z)
  calc
    _ = Module.finrank (Y.residueField y) Γ(Z.left, ⊤) :=
      (pointFiberUnitH0SectionsEquiv f y).finrank_eq
    _ = Module.finrank (Y.residueField y) (Y.residueField y) := e.finrank_eq.symm
    _ = 1 := Module.finrank_self _

/-- Geometric integrality on the original fibres over an open set implies
geometric integrality of the actual restricted morphism. -/
theorem geometricallyIntegral_morphismRestrict_of_fibers {X Y : Scheme.{u}}
    (f : X ⟶ Y) (U : Y.Opens)
    (hU : ∀ y ∈ U, GeometricallyIntegral (f.fiberToSpecResidueField y)) :
    GeometricallyIntegral (f ∣_ U) := by
  apply (GeometricallyIntegral.iff_geometricallyIntegral_fiber (f ∣_ U)).mpr
  intro y
  let : GeometricallyIntegral (f.fiberToSpecResidueField (U.ι y)) := hU y.1 y.2
  exact MorphismProperty.of_isPullback
    (isPullback_fiberToSpecResidueField_of_isPullback
      (isPullback_morphismRestrict f U).flip y) inferInstance

/-- In a proper smooth family of relative dimension one, over a locally
Noetherian integral base, a geometrically integral generic fibre has an actual
nonempty generic open neighbourhood with geometrically integral fibres.
The open is defined by the unchanged original fibre cohomology dimension. -/
theorem exists_generic_open_geometricallyIntegral_of_smoothProper
    {X Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] [SmoothOfRelativeDimension 1 f]
    [GeometricallyIntegral (f.fiberToSpecResidueField (genericPoint Y))] :
    ∃ U : Y.Opens, genericPoint Y ∈ U ∧ U ≠ ⊥ ∧
      GeometricallyIntegral (f ∣_ U) ∧
      (∀ y ∈ U, GeometricallyIntegral (f.fiberToSpecResidueField y)) := by
  let O := SheafOfModules.unit X.ringCatSheaf
  let d := modulePointFiberCohomologyDimension f O 0
  let : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  let : IsIntegral (f.fiber (genericPoint Y)) :=
    GeometricallyIntegral.isIntegral_of_subsingleton (f.fiberToSpecResidueField (genericPoint Y))
  let : Surjective f := surjective_of_isProper_of_nonempty_generic_fiber f
  have hO := Scheme.Modules.affineLocallyFiniteType_unit X
  have hflat := Scheme.Modules.relativeFlat_unit_of_flat f
  have hd : UpperSemicontinuous d :=
    upperSemicontinuous_modulePointFiberCohomologyDimension_of_proper f O hO hflat 0
  let U : Y.Opens := ⟨d ⁻¹' Set.Iio 2, hd.isOpen_preimage 2⟩
  have hη : genericPoint Y ∈ U := by
    change d (genericPoint Y) < 2
    have h := pointFiberUnitH0_finrank_eq_one_of_geometricallyIntegral f (genericPoint Y)
    change d (genericPoint Y) = 1 at h
    rw [h]
    decide
  have hfib (y : Y) (hy : y ∈ U) : GeometricallyIntegral (f.fiberToSpecResidueField y) := by
    let q := f.fiberToSpecResidueField y
    let : Surjective q := MorphismProperty.pullback_snd _ _ inferInstance
    let : Nonempty (f.fiber y) := by
      obtain ⟨z, _⟩ := q.surjective
        (Nonempty.some (inferInstance : Nonempty (Spec (Y.residueField y))))
      exact ⟨z⟩
    let Z : FScheme (Y.residueField y) := Over.mk q
    let := globalSectionsModule Z
    let : Module.Finite (Y.residueField y) (modulePointFiberCohomology f O 0 y) :=
      modulePointFiberCohomology_finite_of_proper f O hO 0 y
    let : Nonempty (⊤ : Z.left.Opens) :=
      ⟨⟨Classical.choice (inferInstance : Nonempty (f.fiber y)), trivial⟩⟩
    let e := pointFiberUnitH0SectionsEquiv f y
    let : Module.Finite (Y.residueField y) Γ(Z.left, ⊤) :=
      Module.Finite.of_surjective e.toLinearMap e.surjective
    have hpos : 0 < Module.finrank (Y.residueField y) Γ(Z.left, ⊤) := Module.finrank_pos
    have he : d y = Module.finrank (Y.residueField y) Γ(Z.left, ⊤) := e.finrank_eq
    have hdim : d y = 1 := by
      change d y < 2 at hy
      omega
    exact geometricallyIntegral_fiber_of_pointFiberUnitH0_finrank_eq_one f y hdim
  exact ⟨U, hη, U.ne_bot_iff_nonempty.mpr ⟨genericPoint Y, hη⟩,
    geometricallyIntegral_morphismRestrict_of_fibers f U hfib, hfib⟩

/-- For a proper smooth relative curve over a field, geometric integrality
is detected after any field extension. The proof uses the original canonical
H0 tensor map and the actual constants maps on both field schemes. -/
theorem geometricallyIntegral_of_smoothProper_of_fieldBaseChange
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (X : FScheme k) [IsProper X.hom] [SmoothOfRelativeDimension 1 X.hom]
    [GeometricallyIntegral (fieldBaseChange K X).hom] : GeometricallyIntegral X.hom := by
  let Z := fieldBaseChange K X
  let : IsProper Z.hom :=
    inferInstanceAs (IsProper (pullback.snd X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
  let : GeometricallyIntegral Z.hom :=
    inferInstanceAs (GeometricallyIntegral (fieldBaseChange K X).hom)
  let : IsIntegral Z.left := GeometricallyIntegral.isIntegral_of_subsingleton Z.hom
  let : Nonempty X.left := by
    obtain ⟨z⟩ := (inferInstance : Nonempty Z.left)
    exact ⟨pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) z⟩
  let : Nonempty (⊤ : X.left.Opens) :=
    ⟨⟨Classical.choice (inferInstance : Nonempty X.left), trivial⟩⟩
  let := globalSectionsModule X
  let := globalSectionsModule Z
  let cZ : K →ₗ[K] Γ(Z.left, ⊤) :=
    { __ := (constants Z).toAddMonoidHom
      map_smul' := fun a b => (constants Z).map_mul a b }
  let eZ := LinearEquiv.ofBijective cZ (constants_bijective_of_proper_geometricallyIntegral Z)
  have hdim : Module.finrank k Γ(X.left, ⊤) = 1 := by
    calc
      _ = Module.finrank k (structureCohomology k X 0) := (structureH0Equiv X).finrank_eq.symm
      _ = Module.finrank K (K ⊗[k] structureCohomology k X 0) :=
        (Module.finrank_baseChange (R := K) (S := k)).symm
      _ = Module.finrank K (structureCohomology K Z 0) :=
        (structureCohomologyBaseChangeEquiv₀ K X).finrank_eq
      _ = Module.finrank K Γ(Z.left, ⊤) := (structureH0Equiv Z).finrank_eq
      _ = Module.finrank K K := eZ.finrank_eq.symm
      _ = 1 := Module.finrank_self K
  let : Module.Finite k Γ(X.left, ⊤) := Module.finite_of_finrank_eq_succ hdim
  let cX : k →ₗ[k] Γ(X.left, ⊤) :=
    { __ := (constants X).toAddMonoidHom
      map_smul' := fun a b => (constants X).map_mul a b }
  have hcinj : Function.Injective cX := (constants X).injective
  have hc : Function.Bijective (constants X) :=
    ⟨hcinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by simpa using hdim.symm) (f := cX)).mp hcinj⟩
  let : IsIso X.hom.c := isIso_c_of_bijective_constants X hc
  let : Surjective X.hom := ⟨Function.surjective_to_subsingleton X.hom⟩
  let : GeometricallyConnected X.hom := geometricallyConnected_of_isProper_of_isIso_c X.hom
  exact geometricallyIntegral_of_smoothOfRelativeDimension_one_of_geometricallyConnected X.hom

end AlgebraicGeometry.Scheme
