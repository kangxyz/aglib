/-
Copyright (c) 2026 R5Lab contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.FiniteEmbedding.ChartData
public import Aglib.AlgebraicGeometry.ProjectiveSpace.TwistPresentation.Sections
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pushforward
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Coherent
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Actual chart coefficients of a finite cover of projective space

Uniform negative-twist generation of the actual finite direct image supplies a
finite family of original preimage sections. Their spanning property and their
transition formula retain the original structure-sheaf scalar action.
-/




@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Modules.Invertible

attribute [local instance] Abelian.hasFiniteBiproducts

universe u

namespace AlgebraicGeometry.ProjectiveSpace.FiniteEmbedding

variable {R : Type u} [CommRing R] {ι : Type u}

private theorem finiteType_structureModule (X : Scheme.{u}) :
    affineLocallyFiniteType X (SheafOfModules.unit X.ringCatSheaf) := by
  let e : SheafOfModules.free (R := X.ringCatSheaf) PUnit.{u + 1} ≅
      SheafOfModules.unit X.ringCatSheaf :=
    coproductUniqueIso (fun _ : PUnit.{u + 1} => SheafOfModules.unit X.ringCatSheaf)
  exact (affineLocallyFiniteType X).prop_of_iso e
    (coherent_of_finiteLocallyFree (SheafOfModules.free (R := X.ringCatSheaf) PUnit.{u + 1}))

/-- Finite coproduct-section surjectivity gives the span of the original frame images.
The argument uses a finite biproduct decomposition and does not assume that arbitrary
module-sheaf coproducts are computed sectionwise. -/
private theorem span_frameImages_eq_top
    (M : (ProjectiveSpace R ι).Modules) (d : ℕ)
    {J : Type u} [Finite J]
    (φ : ∀ _ : J, twistingSheaf R ι (-(d : ℤ)) ⟶ M)
    (hφ : ∀ i, Function.Surjective
      ((Sigma.desc φ).val.app (op (coordinateOpen R ι i)))) (i : ι) :
    Submodule.span Γ(ProjectiveSpace R ι, coordinateOpen R ι i)
      (Set.range (fun a : J => (φ a).val.app (op (coordinateOpen R ι i))
        (twistingGenerator R ι (-(d : ℤ)) i le_rfl))) = ⊤ := by
  classical
  let := Fintype.ofFinite J
  let F : J → (ProjectiveSpace R ι).Modules :=
    fun _ => twistingSheaf R ι (-(d : ℤ))
  let e : (⨁ F) ≅ ∐ F := biproduct.isoCoproduct F
  have hdesc : e.hom ≫ Sigma.desc φ = ∑ a : J, biproduct.π F a ≫ φ a := by
    apply biproduct.hom_ext'
    intro a
    simp [e, biproduct.isoCoproduct_hom, Preadditive.comp_sum,
      biproduct.ι_π_assoc, ite_comp]
  apply top_unique
  intro s _
  obtain ⟨x, hx⟩ := hφ i s
  let y : Γ(⨁ F, coordinateOpen R ι i) :=
    e.inv.val.app (op (coordinateOpen R ι i)) x
  have hy : e.hom.val.app (op (coordinateOpen R ι i)) y = x := by
    exact congrArg (fun ψ : (∐ F) ⟶ ∐ F =>
      ψ.val.app (op (coordinateOpen R ι i)) x) e.inv_hom_id
  let ev : ((⨁ F) ⟶ M) →+ Γ(M, coordinateOpen R ι i) := {
    toFun := fun ψ => ψ.val.app (op (coordinateOpen R ι i)) y
    map_zero' := rfl
    map_add' := fun _ _ => rfl }
  have hs : s = ∑ a : J, (φ a).val.app (op (coordinateOpen R ι i))
      ((biproduct.π F a).val.app (op (coordinateOpen R ι i)) y) := by
    calc
      s = (Sigma.desc φ).val.app (op (coordinateOpen R ι i)) x := hx.symm
      _ = ev (e.hom ≫ Sigma.desc φ) := by
        change _ = (Sigma.desc φ).val.app (op (coordinateOpen R ι i))
          (e.hom.val.app (op (coordinateOpen R ι i)) y)
        rw [hy]
      _ = ev (∑ a : J, biproduct.π F a ≫ φ a) := congrArg ev hdesc
      _ = _ := by
        rw [map_sum]
        rfl
  rw [hs]
  apply Submodule.sum_mem
  intro a _
  let z := (biproduct.π F a).val.app (op (coordinateOpen R ι i)) y
  have hz := twistingSectionsEquiv_smul_generator R ι (-(d : ℤ)) i le_rfl z
  change (φ a).val.app (op (coordinateOpen R ι i)) z ∈ _
  rw [← hz, ((φ a).val.app (op (coordinateOpen R ι i))).hom.map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self a))

variable {Y : Scheme.{u}} (f : Y ⟶ ProjectiveSpace R ι)

private abbrev finiteStructureModule : (ProjectiveSpace R ι).Modules :=
  (Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf)

private def frameCoefficient (d : ℕ)
    (φ : twistingSheaf R ι (-(d : ℤ)) ⟶ finiteStructureModule f) (i : ι) :
    Γ(Y, sourceOpen f i) :=
  φ.val.app (op (coordinateOpen R ι i))
    (twistingGenerator R ι (-(d : ℤ)) i le_rfl)

private theorem frameCoefficient_transition (d : ℕ)
    (φ : twistingSheaf R ι (-(d : ℤ)) ⟶ finiteStructureModule f)
    (i j : ι) (V : (ProjectiveSpace R ι).Opens)
    (hi : V ≤ coordinateOpen R ι i) (hj : V ≤ coordinateOpen R ι j) :
    restrictPreimageSections f hj (frameCoefficient f d φ j) =
      (f.app V) (((coordinateTransitionOn R ι i j hi hj) ^ d).val) *
        restrictPreimageSections f hi (frameCoefficient f d φ i) := by
  change (finiteStructureModule f).val.map (homOfLE hj).op
      (φ.val.app (op (coordinateOpen R ι j))
        (twistingGenerator R ι (-(d : ℤ)) j le_rfl)) =
    ((coordinateTransitionOn R ι i j hi hj ^ d).val : Γ(ProjectiveSpace R ι, V)) •
      (finiteStructureModule f).val.map (homOfLE hi).op
        (φ.val.app (op (coordinateOpen R ι i))
          (twistingGenerator R ι (-(d : ℤ)) i le_rfl))
  rw [← PresheafOfModules.naturality_apply φ.val,
    ← PresheafOfModules.naturality_apply φ.val,
    twistingGenerator_restrict, twistingGenerator_restrict]
  rw [twistingGenerator_transition R ι (-(d : ℤ)) i j hi hj,
    (φ.val.app (op V)).hom.map_smul]
  simp only [neg_neg, zpow_natCast]

/-- Every original finite morphism to finite-coordinate polynomial projective space
supplies actual positive-degree chart generators with their correctly oriented
transition law. No Noetherianity hypothesis is used. -/
theorem nonempty_chartData [Finite ι] [IsFinite f] : Nonempty (ChartData f) := by
  have hA : affineLocallyFiniteType (ProjectiveSpace R ι) (finiteStructureModule f) :=
    FiniteMorphism.affineLocallyFiniteType_pushforward f (finiteType_structureModule Y)
  obtain ⟨d, hd, J, hJ, φ, hφ⟩ :=
    exists_uniformNegativeTwistSectionsSurjective R ι (finiteStructureModule f) hA 1
  let := hJ
  refine ⟨{
    J := J
    finite_J := hJ
    d := d
    one_le_d := hd
    b := fun i a => frameCoefficient f d (φ a) i
    span_b := ?_
    transition := ?_ }⟩
  · intro i
    exact span_frameImages_eq_top (finiteStructureModule f) d φ hφ i
  · intro i j V hi hj a
    exact frameCoefficient_transition f d (φ a) i j V hi hj

/-- A chosen realization of the native chart-generator data of an original finite map. -/
def chartDataOfFinite [Finite ι] [IsFinite f] : ChartData f :=
  (nonempty_chartData f).some

end AlgebraicGeometry.ProjectiveSpace.FiniteEmbedding
