/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.Trace.Sheaf
public import Aglib.AlgebraicGeometry.FunctionField.Trace.Transport
public import Aglib.AlgebraicGeometry.FunctionField.AffineCompatibility
public import Aglib.AlgebraicGeometry.Modules.Linear
public import Aglib.AlgebraicGeometry.Modules.Pullback.Unit
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Sections
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Algebra.BigOperators.Pi

/-!
# Original trace coordinates on a finite birational square

The original finite-morphism trace and the same fixed trace-lattice elements
construct maps between the literal direct image of the source structure module
and the native finite biproduct of target structure modules. Both composites
are multiplication by the pullback of the same base discriminant.

The basis and discriminant use the literal spectra function fields before
any model is supplied. Original scalar and generic squares are proved from
the actual diagram. Separability is used only for nonvanishing of the fixed
discriminant and monicity of the coordinate map. No local freeness or flatness
of the finite morphism is assumed, and no cohomology bound is asserted here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open AlgebraicGeometry TopologicalSpace Opposite Module Matrix
open scoped BigOperators

namespace AlgebraicGeometry.Scheme.Modules.FiniteTraceCoordinates

universe u

/-- The original structure sheaf, typed in the native scheme-module category. -/
abbrev structureModule (Z : Scheme.{u}) : Z.Modules :=
  SheafOfModules.unit Z.ringCatSheaf

/-- The literal direct image of the structure sheaf, in the native target category. -/
abbrev directImageStructure {X Y : Scheme.{u}} (π : Y ⟶ X) : X.Modules :=
  pushforwardStructureSheaf π

/-- The original module-sheaf category has its native finite biproducts. -/
local instance moduleFiniteBiproducts (Z : Scheme.{u}) : HasFiniteBiproducts Z.Modules :=
  CategoryTheory.Abelian.hasFiniteBiproducts (C := Z.Modules)

/-- The literal spectrum function field, with the original underlying ring. -/
abbrev spectrumField (R : Type u) [CommRing R] [IsDomain R] : CommRingCat.{u} :=
  (Spec (CommRingCat.of R)).functionField

/-- The native affine function-field algebra on its original unbundled base ring. -/
local instance (priority := 1100) spectrumFieldAlgebra (R : Type u) [CommRing R] [IsDomain R] :
    Algebra R (spectrumField R) :=
  _root_.AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (CommRingCat.of R)

/-- The same native affine function field is the fraction field of its original base. -/
local instance spectrumFieldFractionRing (R : Type u) [CommRing R] [IsDomain R] :
    IsFractionRing R (spectrumField R) :=
  functionField_isFractionRing_of_affine (CommRingCat.of R)

/-- The original structural ring homomorphism on global sections. -/
abbrev structureScalar {R : Type u} [CommRing R] {Z : Scheme.{u}}
    (c : Z ⟶ Spec (.of R)) : R →+* Γ(Z, ⊤) :=
  c.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom

section FixedAlgebra

variable (A B : Type u) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
  [Algebra A B] [Module.Finite A B] [FaithfulSMul A B] [IsIntegrallyClosed A]

/-- The original map of spectra of the supplied base algebra. -/
abbrev baseMap : Spec (.of B) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A B))

/-- Faithfulness of the original algebra action gives dominance of its spectrum map. -/
local instance baseMapDominant : IsDominant (baseMap A B) := by
  constructor
  change DenseRange (PrimeSpectrum.comap (algebraMap A B))
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot (algebraMap A B)).mp
      (FaithfulSMul.algebraMap_injective A B)]
  exact bot_le

/-- The original generic-stalk map supplies the fixed field-extension action. -/
local instance (priority := 1100) baseFieldAlgebra :
    Algebra (spectrumField A) (spectrumField B) :=
  functionFieldMapAlgebra (baseMap A B)

/-- The actual composite into the upper function field supplies the original base action. -/
local instance upperFieldAlgebra : Algebra A (spectrumField B) :=
  ((algebraMap B (spectrumField B)).comp (algebraMap A B)).toAlgebra

/-- The original upper-ring and upper-field scalar maps form a tower. -/
local instance upperFieldTower : IsScalarTower A B (spectrumField B) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- Original affine generic-stalk naturality gives the base-field scalar tower. -/
local instance baseFieldTower : IsScalarTower A (spectrumField A) (spectrumField B) :=
  IsScalarTower.of_algebraMap_eq fun r =>
    (DFunLike.congr_fun
      (Scheme.FunctionField.AffineCompatibility.fieldMap_spec_constants
        (.of B) (.of A) (CommRingCat.ofHom (algebraMap A B))) r).symm

/-- The degree of the same original fraction-field extension, independent of models. -/
abbrev degree : ℕ := Module.finrank (spectrumField A) (spectrumField B)

/-- The same trace-lattice discriminant, chosen before any finite diagram. -/
abbrev fixedDiscriminant : A :=
  Algebra.TraceLattice.discriminant A B (spectrumField A) (spectrumField B)

/-- The same original upper-ring basis elements, chosen before any finite diagram. -/
abbrev fixedBasisElement (i : Fin (degree A B)) : B :=
  Algebra.TraceLattice.basisElement A B (spectrumField A) (spectrumField B) i

/-- Columns of the same original trace-lattice adjugate expansion. -/
abbrev fixedAdjugateElement (i : Fin (degree A B)) : B :=
  Algebra.TraceLattice.adjugateExpansion A B (spectrumField A) (spectrumField B) (Pi.single i 1)

omit [IsIntegrallyClosed A] in
private theorem expansion_single (i : Fin (degree A B)) :
    Algebra.TraceLattice.expansion A B (spectrumField A) (spectrumField B) (Pi.single i 1) =
      fixedBasisElement A B i := by
  classical
  simp [Algebra.TraceLattice.expansion_apply]

private theorem adjugate_coordinates_basis (j : Fin (degree A B)) :
    Algebra.TraceLattice.adjugateExpansion A B (spectrumField A) (spectrumField B)
        (Algebra.TraceLattice.coordinates A B (spectrumField A) (spectrumField B)
          (fixedBasisElement A B j)) =
      fixedDiscriminant A B • fixedBasisElement A B j := by
  let T := Algebra.TraceLattice.gramMatrix A B (spectrumField A) (spectrumField B)
  let v : Fin (degree A B) → A := Pi.single j 1
  have hc : Algebra.TraceLattice.coordinates A B (spectrumField A) (spectrumField B)
      (fixedBasisElement A B j) = T *ᵥ v := by
    rw [← expansion_single A B j]
    exact Algebra.TraceLattice.coordinates_expansion A B (spectrumField A) (spectrumField B) v
  change Algebra.TraceLattice.expansion A B (spectrumField A) (spectrumField B)
    (T.adjugate *ᵥ Algebra.TraceLattice.coordinates A B (spectrumField A) (spectrumField B)
      (fixedBasisElement A B j)) = _
  rw [hc, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec,
    LinearMap.map_smul]
  exact congrArg (fun z : B => fixedDiscriminant A B • z) (expansion_single A B j)

private theorem adjugate_sum (v : Fin (degree A B) → A) :
    ∑ i, v i • fixedAdjugateElement A B i =
      Algebra.TraceLattice.adjugateExpansion A B (spectrumField A) (spectrumField B) v := by
  have h := congrArg
    (Algebra.TraceLattice.adjugateExpansion A B (spectrumField A) (spectrumField B))
    (pi_eq_sum_univ' v)
  simpa only [map_sum, LinearMap.map_smul] using h.symm

private theorem field_adjugate_sum (z : spectrumField B) :
    ∑ i, Algebra.trace (spectrumField A) (spectrumField B)
        (algebraMap B (spectrumField B) (fixedBasisElement A B i) * z) •
        algebraMap B (spectrumField B) (fixedAdjugateElement A B i) =
      algebraMap A (spectrumField A) (fixedDiscriminant A B) • z := by
  let F : spectrumField B →ₗ[spectrumField A] spectrumField B :=
    ∑ i : Fin (degree A B),
      (Algebra.traceForm (spectrumField A) (spectrumField B)
        (algebraMap B (spectrumField B) (fixedBasisElement A B i))).smulRight
          (algebraMap B (spectrumField B) (fixedAdjugateElement A B i))
  let l : B →ₗ[A] spectrumField B :=
    (IsScalarTower.toAlgHom A B (spectrumField B)).toLinearMap
  have hl (x : B) : l x = algebraMap B (spectrumField B) x := by
    change (IsScalarTower.toAlgHom A B (spectrumField B)).toLinearMap x = _
    exact (AlgHom.toLinearMap_apply _ _).trans
      (IsScalarTower.toAlgHom_apply A B (spectrumField B) x)
  have hmap (v : Fin (degree A B) → A) :
      ∑ i, algebraMap A (spectrumField A) (v i) •
          algebraMap B (spectrumField B) (fixedAdjugateElement A B i) =
        algebraMap B (spectrumField B)
          (Algebra.TraceLattice.adjugateExpansion A B (spectrumField A) (spectrumField B) v) := by
    have h := congrArg l (adjugate_sum A B v)
    simp only [map_sum, LinearMap.map_smul] at h
    simpa only [hl, IsScalarTower.algebraMap_smul (spectrumField A)] using h
  have hF_apply (w : spectrumField B) : F w =
      ∑ i, Algebra.trace (spectrumField A) (spectrumField B)
          (algebraMap B (spectrumField B) (fixedBasisElement A B i) * w) •
        algebraMap B (spectrumField B) (fixedAdjugateElement A B i) := by
    simp only [F, LinearMap.sum_apply, LinearMap.smulRight_apply, Algebra.traceForm_apply]
  have hF : F = algebraMap A (spectrumField A) (fixedDiscriminant A B) • LinearMap.id := by
    apply (Algebra.TraceLattice.fieldBasis A B (spectrumField A) (spectrumField B)).ext
    intro j
    change F (Algebra.TraceLattice.fieldBasis A B (spectrumField A) (spectrumField B) j) =
      algebraMap A (spectrumField A) (fixedDiscriminant A B) •
        Algebra.TraceLattice.fieldBasis A B (spectrumField A) (spectrumField B) j
    rw [← Algebra.TraceLattice.algebraMap_basisElement A B (spectrumField A) (spectrumField B) j,
      hF_apply]
    have he (i : Fin (degree A B)) :
        Algebra.trace (spectrumField A) (spectrumField B)
            (algebraMap B (spectrumField B) (fixedBasisElement A B i) *
              algebraMap B (spectrumField B) (fixedBasisElement A B j)) =
          algebraMap A (spectrumField A)
            (Algebra.TraceLattice.coordinates A B (spectrumField A) (spectrumField B)
              (fixedBasisElement A B j) i) := by
      rw [Algebra.TraceLattice.coordinates_apply, Algebra.TraceLattice.algebraMap_fieldTrace]
      exact congrArg (Algebra.trace (spectrumField A) (spectrumField B))
        ((algebraMap B (spectrumField B)).map_mul
          (fixedBasisElement A B i) (fixedBasisElement A B j)).symm
    simp_rw [he]
    rw [hmap, adjugate_coordinates_basis]
    exact (l.map_smul (fixedDiscriminant A B) (fixedBasisElement A B j)).trans
      (IsScalarTower.algebraMap_smul (spectrumField A) (fixedDiscriminant A B)
        (algebraMap B (spectrumField B) (fixedBasisElement A B j))).symm
  exact (hF_apply z).symm.trans (LinearMap.congr_fun hF z)

end FixedAlgebra

attribute [local instance] baseMapDominant upperFieldAlgebra
  upperFieldTower baseFieldTower
attribute [local instance 1100] baseFieldAlgebra

private theorem scalar_germ
    {R : Type u} [CommRing R] [IsDomain R] {Z : Scheme.{u}} [IsIntegral Z]
    (c : Z ⟶ Spec (.of R)) [IsDominant c] (r : R) :
    letI : Nonempty (⊤ : Z.Opens) := ⟨⟨genericPoint Z, trivial⟩⟩
    Z.germToFunctionField ⊤
        (structureScalar c r) =
      functionFieldMap c (algebraMap R (spectrumField R) r) := by
  let : Nonempty (⊤ : Z.Opens) := ⟨⟨genericPoint Z, trivial⟩⟩
  let : Nonempty (⊤ : (Spec (.of R)).Opens) :=
    ⟨⟨genericPoint (Spec (.of R)), trivial⟩⟩
  have h := ConcreteCategory.congr_hom (functionFieldMap_germ c)
    ((Scheme.ΓSpecIso (.of R)).inv r)
  change functionFieldMap c
      ((Spec (.of R)).germToFunctionField ⊤ ((Scheme.ΓSpecIso (.of R)).inv r)) =
    Z.germToFunctionField ⊤ (structureScalar c r) at h
  exact h.symm

private theorem scalar_restriction_germ
    {R : Type u} [CommRing R] [IsDomain R] {Z : Scheme.{u}} [IsIntegral Z]
    (c : Z ⟶ Spec (.of R)) [IsDominant c] (U : Z.Opens) [Nonempty U] (r : R) :
    Z.germToFunctionField U
        (Z.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
          (structureScalar c r)) =
      functionFieldMap c (algebraMap R (spectrumField R) r) := by
  let : Nonempty (⊤ : Z.Opens) := ⟨⟨genericPoint Z, trivial⟩⟩
  exact (germToFunctionField_restrict (homOfLE (show U ≤ ⊤ from le_top)) _).trans
    (scalar_germ c r)

private theorem moduleHom_sum_app {Z : Scheme.{u}} {M N : Z.Modules}
    {ι : Type*} (t : Finset ι) (f : ι → (M ⟶ N)) (U : Z.Opens) (x : Γ(M, U)) :
    Hom.app (∑ i ∈ t, f i) U x = ∑ i ∈ t, Hom.app (f i) U x := by
  classical
  induction t using Finset.induction_on with
  | empty => rfl
  | @insert i t hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    change Hom.app (f i) U x + Hom.app (∑ j ∈ t, f j) U x = _
    exact congrArg (Hom.app (f i) U x + ·) ih

private theorem center_biproduct_component
    {C : Type*} [Category C] [Preadditive C] {J : Type} [DecidableEq J]
    (M : C) [HasBiproduct (fun _ : J => M)] (c : CatCenter C) (j i : J) :
    biproduct.ι (fun _ : J => M) j ≫ c.app (⨁ fun _ : J => M) ≫
        biproduct.π (fun _ : J => M) i =
      if j = i then c.app M else 0 := by
  classical
  have hn := c.naturality (biproduct.ι (fun _ : J => M) j)
  calc
    _ = (biproduct.ι (fun _ : J => M) j ≫ c.app (⨁ fun _ : J => M)) ≫
        biproduct.π (fun _ : J => M) i := (Category.assoc _ _ _).symm
    _ = (c.app M ≫ biproduct.ι (fun _ : J => M) j) ≫
        biproduct.π (fun _ : J => M) i := congrArg (· ≫ _) hn
    _ = c.app M ≫ (biproduct.ι (fun _ : J => M) j ≫
        biproduct.π (fun _ : J => M) i) := Category.assoc _ _ _
    _ = _ := by
      by_cases h : j = i <;> simp [h]

private theorem compose_mapped
    {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
    {P : C} {U : D} (u : U ⟶ G.obj P) (f g h : P ⟶ P) (he : f ≫ g = h) :
    (u ≫ G.map f) ≫ G.map g = u ≫ G.map h := by
  calc
    _ = u ≫ (G.map f ≫ G.map g) := Category.assoc _ _ _
    _ = u ≫ G.map (f ≫ g) := congrArg (u ≫ ·) (G.map_comp f g).symm
    _ = _ := congrArg (fun k : P ⟶ P => u ≫ G.map k) he

/-- The original structure-unit arrow followed by multiplication by an original constant. -/
def generator (B : Type u) [CommRing B] {X Y : Scheme.{u}}
    (π : Y ⟶ X) (b : Y ⟶ Spec (.of B)) (r : B) :
    (structureModule X) ⟶ directImageStructure π :=
  SheafOfModules.unitToPushforwardObjUnit π.toRingCatSheafHom ≫
    (pushforward π).map (unitMul Y (structureScalar b r))

private theorem generator_app (B : Type u) [CommRing B] {X Y : Scheme.{u}}
    (π : Y ⟶ X) (b : Y ⟶ Spec (.of B)) (r : B) (U : X.Opens) (x : Γ(X, U)) :
    (show Γ(Y, π ⁻¹ᵁ U) from Hom.app (generator B π b r) U x) =
      π.app U x * Y.presheaf.map (homOfLE (show π ⁻¹ᵁ U ≤ ⊤ from le_top)).op
        (structureScalar b r) := by
  exact unitMul_app Y (structureScalar b r) (π ⁻¹ᵁ U) (π.app U x)

/-- The original scheme square identifies the two actual structural scalar maps. -/
theorem scalar_square (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    {X Y : Scheme.{u}} (π : Y ⟶ X) (a : X ⟶ Spec (.of A)) (b : Y ⟶ Spec (.of B))
    (hsq : π ≫ a = b ≫ baseMap A B) :
    π.appTop.hom.comp (a.appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom) =
      (b.appTop.hom.comp (Scheme.ΓSpecIso (.of B)).inv.hom).comp (algebraMap A B) :=
  Scheme.Cohomology.moduleSectionsBaseChangeScalars π b a (algebraMap A B) hsq

private theorem pushforward_scalar_mono {X Y : Scheme.{u}} [IsIntegral Y]
    (π : Y ⟶ X) (r : Γ(X, ⊤)) (hr : π.appTop r ≠ 0) :
    Mono (globalScalarEndomorphism X (directImageStructure π) r) := by
  have hinj (U : X.Opens) : Function.Injective
      ((globalScalarEndomorphism X (directImageStructure π) r).val.app (op U)) := by
    let V := π ⁻¹ᵁ U
    by_cases hV : Nonempty V
    · let := hV
      let t := Y.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op (π.appTop r)
      have ht : t ≠ 0 := by
        intro hz
        apply hr
        apply map_injective_of_isIntegral Y (homOfLE (show V ≤ ⊤ from le_top))
        exact hz.trans
          (Y.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op).hom.map_zero.symm
      have hn := ConcreteCategory.congr_hom
        (π.naturality (homOfLE (show U ≤ ⊤ from le_top)).op) r
      change π.app U (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r) = t at hn
      have formula (z : Γ(Y, V)) :
          (show Γ(Y, V) from
            (globalScalarEndomorphism X (directImageStructure π) r).val.app (op U) z) =
            t * z := by
        have h := globalScalarEndomorphism_app X (directImageStructure π) r U z
        change (show Γ(Y, V) from
            (globalScalarEndomorphism X (directImageStructure π) r).val.app (op U) z) =
          π.app U (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r) * z at h
        exact h.trans (congrArg (· * z) hn)
      intro x y hxy
      have he : (show Γ(Y, V) from x) = (show Γ(Y, V) from y) :=
        mul_left_cancel₀ ht ((formula x).symm.trans (hxy.trans (formula y)))
      exact he
    · have hbot : V = ⊥ := by
        apply bot_unique
        intro y hy
        exact (hV ⟨⟨y, hy⟩⟩).elim
      let : Subsingleton Γ(Y, V) :=
        CommRingCat.subsingleton_of_isTerminal (Y.sheaf.isTerminalOfEqEmpty hbot)
      intro x y _
      exact Subsingleton.elim (show Γ(Y, V) from x) (show Γ(Y, V) from y)
  have hm : Mono (globalScalarEndomorphism X (directImageStructure π) r).val :=
    PresheafOfModules.mono_of_injective (fun {U} => hinj U.unop)
  exact (SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map hm

section Diagram

variable (A B : Type u) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
  [Algebra A B] [Module.Finite A B] [FaithfulSMul A B] [IsIntegrallyClosed A]

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (π : Y ⟶ X) [IsDominant π] [IsFinite π] (hX : NormalStalks X)
  (a : X ⟶ Spec (.of A)) (b : Y ⟶ Spec (.of B))

/-- The native finite biproduct of original target structure modules. -/
abbrev target : X.Modules :=
  biproduct (C := X.Modules) (fun _ : Fin (degree A B) => structureModule X)

/-- One original trace coordinate, after multiplication by a fixed upper-ring constant. -/
def coordinate (i : Fin (degree A B)) :
    directImageStructure π ⟶ (structureModule X) :=
  (pushforward π).map (unitMul Y (structureScalar b (fixedBasisElement A B i))) ≫
    finiteStructureTrace π hX

/-- The original trace-coordinate sheaf map, using the fixed field basis. -/
def coordinates : directImageStructure π ⟶ target A B (X := X) :=
  biproduct.lift (C := X.Modules) (coordinate A B π hX b)

/-- The original adjugate-expansion sheaf map, using the fixed lattice columns. -/
def adjugateExpansion : target A B (X := X) ⟶ directImageStructure π :=
  biproduct.desc (C := X.Modules) (fun i => generator B π b (fixedAdjugateElement A B i))

omit [IsIntegrallyClosed A] in
/-- Each native projection recovers its original trace coordinate. -/
theorem coordinates_π (i : Fin (degree A B)) :
    coordinates A B π hX b ≫
        biproduct.π (C := X.Modules) (fun _ : Fin (degree A B) =>
          (structureModule X)) i =
      coordinate A B π hX b i := biproduct.lift_π (C := X.Modules) _ _

omit [IsIntegral X] [IsIntegral Y] [IsDominant π] [IsFinite π] in
/-- Each native inclusion recovers the original adjugate-column generator. -/
theorem ι_adjugateExpansion (i : Fin (degree A B)) :
    biproduct.ι (C := X.Modules) (fun _ : Fin (degree A B) =>
        (structureModule X)) i ≫ adjugateExpansion A B π b =
      generator B π b (fixedAdjugateElement A B i) := biproduct.ι_desc (C := X.Modules) _ _

omit [IsIntegrallyClosed A] in
private theorem coordinate_app (i : Fin (degree A B)) (U : X.Opens) (z : Γ(Y, π ⁻¹ᵁ U)) :
    (show Γ(X, U) from Hom.app (coordinate A B π hX b i) U z) =
      finiteSectionTrace π hX U
        (z * Y.presheaf.map (homOfLE (show π ⁻¹ᵁ U ≤ ⊤ from le_top)).op
          (structureScalar b (fixedBasisElement A B i))) := by
  exact congrArg (finiteSectionTrace π hX U)
    (unitMul_app Y (structureScalar b (fixedBasisElement A B i)) (π ⁻¹ᵁ U) z)

variable [IsDominant a] [IsDominant b]
  (ha : IsIso (CommRingCat.ofHom (functionFieldMap a)))
  (hb : IsIso (CommRingCat.ofHom (functionFieldMap b)))
  (hsq : π ≫ a = b ≫ baseMap A B)

include hsq in
omit [Module.Finite A B] [IsIntegrallyClosed A] [IsFinite π] in
private theorem field_square (z : spectrumField A) :
    functionFieldMap π (functionFieldMap a z) =
      functionFieldMap b (functionFieldMap (baseMap A B) z) := by
  have hcongr {c d : Y ⟶ Spec (.of A)} [IsDominant c] [IsDominant d] (hcd : c = d) :
      functionFieldMap c = functionFieldMap d := by
    subst d
    rfl
  exact DFunLike.congr_fun
    ((functionFieldMap_comp π a).symm.trans ((hcongr hsq).trans
      (functionFieldMap_comp b (baseMap A B)))) z

include ha hb hsq in
/-- The trace of an original upper constant is the pullback of its fixed base trace. -/
theorem trace_originalConstant (r : B) :
    finiteSectionTrace π hX ⊤ (structureScalar b r) =
      structureScalar a
        (Algebra.TraceLattice.fieldTrace A B (spectrumField A) (spectrumField B) r) := by
  let : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  let : Nonempty (⊤ : Y.Opens) := ⟨⟨genericPoint Y, trivial⟩⟩
  let : Nonempty (π ⁻¹ᵁ ⊤) := nonempty_preimage_of_isDominant π ⊤
  let := functionFieldMapAlgebra π
  have ht := finiteSectionTrace_germ π hX ⊤
    (show Γ(Y, π ⁻¹ᵁ ⊤) from structureScalar b r)
  have hy : Y.germToFunctionField (π ⁻¹ᵁ ⊤)
      (show Γ(Y, π ⁻¹ᵁ ⊤) from structureScalar b r) =
        functionFieldMap b (algebraMap B (spectrumField B) r) := scalar_germ b r
  have hx := scalar_germ a
    (Algebra.TraceLattice.fieldTrace A B (spectrumField A) (spectrumField B) r)
  have hbase := Algebra.TraceLattice.algebraMap_fieldTrace A B
    (spectrumField A) (spectrumField B) r
  apply X.germToFunctionField_injective ⊤
  calc
    _ = Algebra.trace X.functionField Y.functionField
        (Y.germToFunctionField (π ⁻¹ᵁ ⊤)
          (show Γ(Y, π ⁻¹ᵁ ⊤) from structureScalar b r)) := ht
    _ = Algebra.trace X.functionField Y.functionField
        (functionFieldMap b (algebraMap B (spectrumField B) r)) :=
      congrArg (Algebra.trace X.functionField Y.functionField) hy
    _ = functionFieldMap a (Algebra.trace (spectrumField A) (spectrumField B)
        (algebraMap B (spectrumField B) r)) :=
      (functionFieldTrace_birational_square (baseMap A B) a b π ha hb hsq
        (algebraMap B (spectrumField B) r)).symm
    _ = functionFieldMap a (algebraMap A (spectrumField A)
        (Algebra.TraceLattice.fieldTrace A B (spectrumField A) (spectrumField B) r)) :=
      congrArg (functionFieldMap a) hbase.symm
    _ = _ := hx.symm

include ha hb hsq in
private theorem generator_trace (r : B) :
    generator B π b r ≫ finiteStructureTrace π hX =
      unitMul X (structureScalar a
        (Algebra.TraceLattice.fieldTrace A B (spectrumField A) (spectrumField B) r)) := by
  let q := structureScalar a
    (Algebra.TraceLattice.fieldTrace A B (spectrumField A) (spectrumField B) r)
  have hy : (show Γ(Y, ⊤) from Hom.app (generator B π b r) ⊤ (1 : Γ(X, ⊤))) =
      structureScalar b r := by
    change π.appTop.hom 1 *
      (Y.presheaf.map (𝟙 (op (⊤ : Y.Opens)))).hom (structureScalar b r) = _
    exact (congrArg (· * _) π.appTop.hom.map_one).trans
      ((one_mul _).trans
        (ConcreteCategory.congr_hom (Y.presheaf.map_id (op (⊤ : Y.Opens)))
          (structureScalar b r)))
  have hx : (show Γ(X, ⊤) from Hom.app (unitMul X q) ⊤ (1 : Γ(X, ⊤))) = q := by
    change (1 : Γ(X, ⊤)) * (X.presheaf.map (𝟙 (op (⊤ : X.Opens)))).hom q = q
    exact (one_mul _).trans
      (ConcreteCategory.congr_hom (X.presheaf.map_id (op (⊤ : X.Opens))) q)
  apply (unitHomGlobalSectionsEquiv X (structureModule X)).injective
  exact (congrArg (fun y : Γ(Y, ⊤) =>
      finiteSectionTrace π hX ⊤ (show Γ(Y, π ⁻¹ᵁ ⊤) from y)) hy).trans
    ((trace_originalConstant A B π hX a b ha hb hsq r).trans hx.symm)

include ha hb hsq in
private theorem generator_coordinate (r : B) (i : Fin (degree A B)) :
    generator B π b r ≫ coordinate A B π hX b i =
      unitMul X (structureScalar a
        (Algebra.TraceLattice.coordinates A B (spectrumField A) (spectrumField B) r i)) := by
  let m : directImageStructure π ⟶ directImageStructure π :=
    (pushforward π).map (unitMul Y (structureScalar b (fixedBasisElement A B i)))
  have hmul : generator B π b r ≫ m =
      generator B π b (r * fixedBasisElement A B i) := by
    apply compose_mapped (pushforward π)
      (show structureModule X ⟶ (pushforward π).obj (structureModule Y) from
        SheafOfModules.unitToPushforwardObjUnit π.toRingCatSheafHom)
      (unitMul Y (structureScalar b r))
      (unitMul Y (structureScalar b (fixedBasisElement A B i)))
      (unitMul Y (structureScalar b (r * fixedBasisElement A B i)))
    exact (unitMul_mul Y _ _).symm.trans
      (congrArg (unitMul Y)
        ((structureScalar b).map_mul r (fixedBasisElement A B i)).symm)
  calc
    _ = (generator B π b r ≫ m) ≫ finiteStructureTrace π hX :=
      (Category.assoc (obj := X.Modules) (generator B π b r) m
        (finiteStructureTrace π hX)).symm
    _ = generator B π b (r * fixedBasisElement A B i) ≫ finiteStructureTrace π hX :=
      congrArg (fun k : structureModule X ⟶ directImageStructure π =>
        k ≫ finiteStructureTrace π hX) hmul
    _ = (show structureModule X ⟶ structureModule X from
        unitMul X (structureScalar a
          (Algebra.TraceLattice.fieldTrace A B (spectrumField A) (spectrumField B)
            (r * fixedBasisElement A B i)))) :=
      generator_trace A B π hX a b ha hb hsq _
    _ = _ := congrArg (fun x : A =>
        (show structureModule X ⟶ structureModule X from unitMul X (structureScalar a x)))
      (congrArg (Algebra.TraceLattice.fieldTrace A B (spectrumField A) (spectrumField B))
        (mul_comm r (fixedBasisElement A B i)))

include ha hb hsq in
/-- The composite on the native biproduct is the original pulled-back discriminant action. -/
theorem adjugateExpansion_comp_coordinates :
    adjugateExpansion A B π b ≫ coordinates A B π hX b =
      globalScalarEndomorphism X (target A B (X := X))
        (structureScalar a (fixedDiscriminant A B)) := by
  classical
  apply biproduct.hom_ext' (C := X.Modules)
  intro j
  apply biproduct.hom_ext (C := X.Modules)
  intro i
  have hL :
      (biproduct.ι (C := X.Modules) (fun _ : Fin (degree A B) =>
          (structureModule X)) j ≫ adjugateExpansion A B π b) ≫
        (coordinates A B π hX b ≫ biproduct.π (C := X.Modules) (fun _ : Fin (degree A B) =>
          (structureModule X)) i) =
        generator B π b (fixedAdjugateElement A B j) ≫ coordinate A B π hX b i :=
    congrArg₂ (fun f g => f ≫ g) (ι_adjugateExpansion A B π b j)
      (coordinates_π A B π hX b i)
  calc
    _ = generator B π b (fixedAdjugateElement A B j) ≫ coordinate A B π hX b i := by
      simpa only [Category.assoc] using hL
    _ = (show structureModule X ⟶ structureModule X from
        unitMul X (structureScalar a
          (Algebra.TraceLattice.coordinates A B (spectrumField A) (spectrumField B)
            (fixedAdjugateElement A B j) i))) :=
      generator_coordinate A B π hX a b ha hb hsq _ i
    _ = if j = i then
        globalScalarEndomorphism X (structureModule X)
          (structureScalar a (fixedDiscriminant A B)) else 0 := by
      have hc := congrFun
        (Algebra.TraceLattice.coordinates_adjugateExpansion A B (spectrumField A) (spectrumField B)
          (Pi.single j 1)) i
      by_cases h : j = i
      · subst i
        have hv : Algebra.TraceLattice.coordinates A B (spectrumField A) (spectrumField B)
            (fixedAdjugateElement A B j) j = fixedDiscriminant A B := by
          simpa only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] using hc
        rw [hv, ite_eq_left rfl]
        exact (globalScalarEndomorphism_unit X _).symm
      · have hv : Algebra.TraceLattice.coordinates A B (spectrumField A) (spectrumField B)
            (fixedAdjugateElement A B j) i = 0 := by
          simpa only [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm h), smul_zero] using hc
        have hzero : (show structureModule X ⟶ structureModule X from
            unitMul X (structureScalar a
              (Algebra.TraceLattice.coordinates A B (spectrumField A) (spectrumField B)
                (fixedAdjugateElement A B j) i))) = 0 :=
          (congrArg (fun x : A => (show structureModule X ⟶ structureModule X from
              unitMul X (structureScalar a x))) hv).trans
            ((congrArg (fun q : Γ(X, ⊤) => (show structureModule X ⟶ structureModule X from
                unitMul X q)) (structureScalar a).map_zero).trans (unitMul_zero X))
        exact hzero.trans (ite_eq_right h).symm
    _ = _ := (center_biproduct_component (C := X.Modules) (structureModule X)
      (globalScalarCenter X (structureScalar a (fixedDiscriminant A B))) j i).symm

include ha hb hsq in
omit [IsIntegrallyClosed A] in
private theorem coordinate_germ (U : X.Opens) [Nonempty U]
    (z : Γ(Y, π ⁻¹ᵁ U)) (w : spectrumField B)
    (hw : letI : Nonempty (π ⁻¹ᵁ U) := nonempty_preimage_of_isDominant π U
      Y.germToFunctionField (π ⁻¹ᵁ U) z = functionFieldMap b w) (i : Fin (degree A B)) :
    X.germToFunctionField U
        (show Γ(X, U) from Hom.app (coordinate A B π hX b i) U z) =
      functionFieldMap a
        (Algebra.trace (spectrumField A) (spectrumField B)
          (algebraMap B (spectrumField B) (fixedBasisElement A B i) * w)) := by
  let : Nonempty (π ⁻¹ᵁ U) := nonempty_preimage_of_isDominant π U
  let := functionFieldMapAlgebra π
  rw [coordinate_app, finiteSectionTrace_germ, map_mul, hw,
    scalar_restriction_germ b]
  rw [← map_mul]
  exact (functionFieldTrace_birational_square (baseMap A B) a b π ha hb hsq
    (w * algebraMap B (spectrumField B) (fixedBasisElement A B i))).symm.trans
      (congrArg (fun q =>
        functionFieldMap a (Algebra.trace (spectrumField A) (spectrumField B) q)) (mul_comm _ _))

include ha hb hsq in
private theorem composite_component_germ (U : X.Opens) [Nonempty U]
    (z : Γ(Y, π ⁻¹ᵁ U)) (w : spectrumField B)
    (hw : letI : Nonempty (π ⁻¹ᵁ U) := nonempty_preimage_of_isDominant π U
      Y.germToFunctionField (π ⁻¹ᵁ U) z = functionFieldMap b w) (i : Fin (degree A B)) :
    letI : Nonempty (π ⁻¹ᵁ U) := nonempty_preimage_of_isDominant π U
    Y.germToFunctionField (π ⁻¹ᵁ U)
        (show Γ(Y, π ⁻¹ᵁ U) from
          Hom.app (coordinate A B π hX b i ≫ generator B π b (fixedAdjugateElement A B i)) U z) =
      functionFieldMap b
        (Algebra.trace (spectrumField A) (spectrumField B)
          (algebraMap B (spectrumField B) (fixedBasisElement A B i) * w) •
          algebraMap B (spectrumField B) (fixedAdjugateElement A B i)) := by
  let : Nonempty (π ⁻¹ᵁ U) := nonempty_preimage_of_isDominant π U
  let := functionFieldMapAlgebra π
  let x : Γ(X, U) := Hom.app (coordinate A B π hX b i) U z
  have hx := coordinate_germ A B π hX a b ha hb hsq U z w hw i
  have hp := ConcreteCategory.congr_hom (functionFieldMap_germ_app π U) x
  change functionFieldMap π (X.germToFunctionField U x) =
    Y.germToFunctionField (π ⁻¹ᵁ U) (π.app U x) at hp
  change Y.germToFunctionField (π ⁻¹ᵁ U)
    (show Γ(Y, π ⁻¹ᵁ U) from Hom.app (generator B π b (fixedAdjugateElement A B i)) U x) = _
  rw [generator_app, map_mul, scalar_restriction_germ b, ← hp, hx, field_square A B π a b hsq]
  exact (map_mul (functionFieldMap b) _ _).symm

include hsq in
omit [IsFinite π] in
private theorem scalar_component_germ (U : X.Opens) [Nonempty U]
    (z : Γ(Y, π ⁻¹ᵁ U)) (w : spectrumField B)
    (hw : letI : Nonempty (π ⁻¹ᵁ U) := nonempty_preimage_of_isDominant π U
      Y.germToFunctionField (π ⁻¹ᵁ U) z = functionFieldMap b w) :
    letI : Nonempty (π ⁻¹ᵁ U) := nonempty_preimage_of_isDominant π U
    Y.germToFunctionField (π ⁻¹ᵁ U)
        (show Γ(Y, π ⁻¹ᵁ U) from
          Hom.app (globalScalarEndomorphism X (directImageStructure π)
            (structureScalar a (fixedDiscriminant A B))) U z) =
      functionFieldMap b (algebraMap A (spectrumField A) (fixedDiscriminant A B) • w) := by
  let : Nonempty (π ⁻¹ᵁ U) := nonempty_preimage_of_isDominant π U
  let := functionFieldMapAlgebra π
  let r := X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
    (structureScalar a (fixedDiscriminant A B))
  have hp := ConcreteCategory.congr_hom (functionFieldMap_germ_app π U) r
  change functionFieldMap π (X.germToFunctionField U r) =
    Y.germToFunctionField (π ⁻¹ᵁ U) (π.app U r) at hp
  have hs : (show Γ(Y, π ⁻¹ᵁ U) from
      Hom.app (globalScalarEndomorphism X (directImageStructure π)
        (structureScalar a (fixedDiscriminant A B))) U z) =
        π.app U r * z :=
    globalScalarEndomorphism_app X (directImageStructure π)
      (structureScalar a (fixedDiscriminant A B)) U z
  have hr : X.germToFunctionField U r =
      functionFieldMap a (algebraMap A (spectrumField A) (fixedDiscriminant A B)) :=
    scalar_restriction_germ a U (fixedDiscriminant A B)
  rw [hs, map_mul, ← hp, hr, hw, field_square A B π a b hsq]
  exact (map_mul (functionFieldMap b) _ _).symm

include ha hb hsq in
/-- The composite on the literal direct image is the same original discriminant action. -/
theorem coordinates_comp_adjugateExpansion :
    coordinates A B π hX b ≫ adjugateExpansion A B π b =
      globalScalarEndomorphism X (directImageStructure π)
        (structureScalar a (fixedDiscriminant A B)) := by
  let := hb
  have hc : coordinates A B π hX b ≫ adjugateExpansion A B π b =
      ∑ i : Fin (degree A B),
        coordinate A B π hX b i ≫ generator B π b (fixedAdjugateElement A B i) :=
    biproduct.lift_desc (C := X.Modules)
  apply Scheme.Modules.hom_ext
  intro U
  ext z
  have hv := congrArg
    (fun f : directImageStructure π ⟶ directImageStructure π => Hom.app f U z) hc
  have hsum := moduleHom_sum_app Finset.univ
    (fun i : Fin (degree A B) =>
      coordinate A B π hX b i ≫ generator B π b (fixedAdjugateElement A B i)) U z
  have he := hv.trans hsum
  by_cases hU : Nonempty U
  · let := hU
    let : Nonempty (π ⁻¹ᵁ U) := nonempty_preimage_of_isDominant π U
    let g : Γ(directImageStructure π, U) →+ Y.functionField :=
      (Y.germToFunctionField (π ⁻¹ᵁ U)).hom.toAddMonoidHom
    have hg : Function.Injective g := Y.germToFunctionField_injective (π ⁻¹ᵁ U)
    obtain ⟨w, hw⟩ := (ConcreteCategory.bijective_of_isIso
      (CommRingCat.ofHom (functionFieldMap b))).2 (g z)
    apply hg
    calc
      _ = ∑ i : Fin (degree A B),
          g (Hom.app (coordinate A B π hX b i ≫
            generator B π b (fixedAdjugateElement A B i)) U z) :=
        (congrArg g he).trans (_root_.map_sum g _ Finset.univ)
      _ = ∑ i : Fin (degree A B), functionFieldMap b
          (Algebra.trace (spectrumField A) (spectrumField B)
            (algebraMap B (spectrumField B) (fixedBasisElement A B i) * w) •
            algebraMap B (spectrumField B) (fixedAdjugateElement A B i)) :=
        Finset.sum_congr rfl fun i _ =>
          composite_component_germ A B π hX a b ha hb hsq U
            (show Γ(Y, π ⁻¹ᵁ U) from z) w hw.symm i
      _ = functionFieldMap b (algebraMap A (spectrumField A) (fixedDiscriminant A B) • w) := by
        rw [← map_sum, field_adjugate_sum]
      _ = _ := (scalar_component_germ A B π a b hsq U
        (show Γ(Y, π ⁻¹ᵁ U) from z) w hw.symm).symm
  · apply TopCat.Presheaf.section_ext Y.sheaf
    intro y hy
    exact (hU ⟨⟨π y, hy⟩⟩).elim

include ha hb hsq in
/-- Actual separability makes the original trace-coordinate sheaf map monic. -/
theorem coordinates_mono [Algebra.IsSeparable (spectrumField A) (spectrumField B)] :
    Mono (coordinates A B π hX b) := by
  let : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  let : Nonempty (⊤ : Y.Opens) := ⟨⟨genericPoint Y, trivial⟩⟩
  have hd : fixedDiscriminant A B ≠ 0 :=
    Algebra.TraceLattice.discriminant_ne_zero A B (spectrumField A) (spectrumField B)
  have hr : π.appTop (structureScalar a (fixedDiscriminant A B)) ≠ 0 := by
    intro hz
    have hg := ConcreteCategory.congr_hom (functionFieldMap_germ π)
      (structureScalar a (fixedDiscriminant A B))
    change functionFieldMap π
        (X.germToFunctionField ⊤ (structureScalar a (fixedDiscriminant A B))) =
      Y.germToFunctionField ⊤
        (π.appTop (structureScalar a (fixedDiscriminant A B))) at hg
    have he : functionFieldMap π
        (functionFieldMap a (algebraMap A (spectrumField A) (fixedDiscriminant A B))) = 0 := by
      calc
        _ = functionFieldMap π
            (X.germToFunctionField ⊤ (structureScalar a (fixedDiscriminant A B))) :=
          congrArg (functionFieldMap π) (scalar_germ a (fixedDiscriminant A B)).symm
        _ = Y.germToFunctionField ⊤
            (π.appTop (structureScalar a (fixedDiscriminant A B))) := hg
        _ = 0 := (congrArg (Y.germToFunctionField ⊤) hz).trans
          (Y.germToFunctionField ⊤).hom.map_zero
    apply hd
    apply IsFractionRing.injective A (spectrumField A)
    apply (functionFieldMap a).injective
    apply (functionFieldMap π).injective
    simpa only [map_zero] using he
  let : Mono (globalScalarEndomorphism X (directImageStructure π)
      (structureScalar a (fixedDiscriminant A B))) :=
    pushforward_scalar_mono π _ hr
  exact mono_of_mono_fac (coordinates_comp_adjugateExpansion A B π hX a b ha hb hsq)

end Diagram

end AlgebraicGeometry.Scheme.Modules.FiniteTraceCoordinates
