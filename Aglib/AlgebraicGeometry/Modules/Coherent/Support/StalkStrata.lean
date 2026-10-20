/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.FiniteLengthFamilies
public import Aglib.AlgebraicGeometry.Modules.Coherent.Support.HeightSlice
public import Aglib.CategoryTheory.Abelian.SerreClass.ExactKernels
public import Aglib.AlgebraicGeometry.Modules.Stalk.Basic
public import Aglib.CategoryTheory.ExactCategory.MatrixDeflation
public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.Property
public import Aglib.AlgebraicGeometry.Modules.Exact
public import Aglib.AlgebraicGeometry.Modules.Coherent.Exact
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeProperty
public import Aglib.CategoryTheory.SmallModel.Abelian
public import Aglib.CategoryTheory.ExactCategory.Basic
public import Aglib.AlgebraicGeometry.Modules.Support
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.AlgebraicGeometry.Dimension.CodimensionTwo

/-!
# Exact coherent height-stalk families

Source-only extraction from `R5Lab.KTheory.Quillen.CoherentStratumStalks` at R5Lab revision
`e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`. Existing objects, maps,
hypotheses, universes, proof bodies and mathematical namespaces are retained.
The original source correspondence remains in the supplying application module.
-/



/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Modules.Support.StalkStrata` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`b6adf9ae554411960316dccb06606573327855bd91093ed29315d1b9b1c171c6`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ZeroObject
attribute [local instance] Abelian.hasFiniteBiproducts
open ModuleCat.FiniteLengthFamilies CategoryTheory.Pi
namespace AlgebraicGeometry.Scheme.Modules.Coherent.Support
universe u

variable (X : Scheme.{u}) [IsNoetherian X]

/-- The points of `X` whose local rings have Krull dimension `p`. -/
abbrev HeightPoint (p : ℕ) := {x : X // ringKrullDim (X.presheaf.stalk x) = p}
/-- The local rings at the points of the height-`p` stratum. -/
abbrev localRings (p : ℕ) (x : HeightPoint X p) : Type u := X.presheaf.stalk x.1

/-- The exact functor taking a coherent sheaf to its module stalk at `x`. -/
def coherentStalk (x : X) : _root_.CategoryTheory.ExactCategory.ExactFunctor
    (Scheme.Modules.Coherent.coherentExactStructure X)
    (_root_.CategoryTheory.ExactCategory.abelianExactStructure (ModuleCat.{u} (X.presheaf.stalk
        x))) :=
  (Scheme.Modules.Coherent.coherentInclusion X).comp
      (Scheme.Modules.moduleStalkExactFunctor X x)

omit [AlgebraicGeometry.IsNoetherian X] in
lemma moduleStalk_isZero_iff (M : X.Modules) (x : X) :
    IsZero ((Scheme.Modules.moduleStalk X x).obj M) ↔
      IsZero ((Scheme.Modules.stalkFunctor X x).obj M) := by
  rw [ModuleCat.isZero_iff_subsingleton, AddCommGrpCat.isZero_iff_subsingleton]
  rfl

/-- The genuine stalk-vanishing support filtration on original coherent sheaves. -/
def coherentAtLeast (p : ℕ) : ObjectProperty
    (Scheme.Modules.QuasiCoherent.FiniteTypeSheaves X) :=
  fun M => ∀ x : {x : X // ringKrullDim (X.presheaf.stalk x) < p},
    (coherentStalk X x.1).toFunctor.kernel M

instance coherentAtLeast_serre (p : ℕ) : (coherentAtLeast X p).IsSerreClass := by
  let : ∀ x : {x : X // ringKrullDim (X.presheaf.stalk x) < p},
      (coherentStalk X x.1).toFunctor.kernel.IsSerreClass :=
    fun x => CategoryTheory.ObjectProperty.exactKernelSerre (coherentStalk X x.1)
  exact CategoryTheory.ObjectProperty.forallSerre _

/-- The full subcategory of coherent sheaves with zero stalks at local-ring dimension below `p`. -/
abbrev CohAtLeast (p : ℕ) := (coherentAtLeast X p).FullSubcategory

/-- Actual stalk modules, with no finite-length or quotient assumption. -/
def allStratumStalks (p : ℕ) : _root_.CategoryTheory.ExactCategory.ExactFunctor
    (Scheme.Modules.Coherent.coherentExactStructure X)
    (_root_.CategoryTheory.ExactCategory.abelianExactStructure (AllFamilies (localRings X p))) where
  toFunctor := Functor.pi' (fun x : HeightPoint X p => (coherentStalk X x.1).toFunctor)
  additive := { map_add := by intros; funext x; exact (coherentStalk X x.1).toFunctor.map_add }
  map_conflation S h := shortExact_pi_of _ _
    (fun x => (coherentStalk X x.1).map_conflation S h)

/-- Finite support is proved for the actual family, using coherent closed support. -/
theorem stratumStalks_finite (p : ℕ) (M : CohAtLeast X p) :
    finiteSupportProperty (localRings X p) ((allStratumStalks X p).toFunctor.obj M.obj) := by
  have hf := coherent_finite_height_support X M.obj p (fun x hx =>
    (moduleStalk_isZero_iff X M.obj.obj x).mp (M.property ⟨x, hx⟩))
  have hp := hf.preimage (f := fun x : HeightPoint X p => x.1) Subtype.val_injective.injOn
  apply hp.subset
  intro x hx
  exact ⟨x.2, fun hz => hx ((moduleStalk_isZero_iff X M.obj.obj x.1).mpr hz)⟩

/-- The original coherent stalk functor landing in finite-support module families.
Local finite length is a separate still-needed theorem for the stronger target `Family`. -/
/- The geometric functor currently lands in finite-support modules.
   Local finite-length landing into the stronger Family category remains open. -/
def stratumStalks (p : ℕ) : _root_.CategoryTheory.ExactCategory.ExactFunctor
    (_root_.CategoryTheory.ExactCategory.abelianExactStructure (CohAtLeast X p))
    (_root_.CategoryTheory.ExactCategory.abelianExactStructure (FiniteSupportFamily (localRings
        X p))) where
  toFunctor := (finiteSupportProperty (localRings X p)).lift
    ((coherentAtLeast X p).ι ⋙ (allStratumStalks X p).toFunctor)
    (stratumStalks_finite X p)
  additive := {
    map_add := by
      intros
      apply (finiteSupportProperty (localRings X p)).ι.map_injective
      funext x
      exact (coherentStalk X x.1).toFunctor.map_add }
  map_conflation S h := by
    let P := finiteSupportProperty (localRings X p)
    let F := (_root_.CategoryTheory.ObjectProperty.exactInclusion (coherentAtLeast X p)).comp
        (allStratumStalks X p)
    have he := F.map_conflation S h
    exact { exact := Functor.reflects_exact_of_faithful P.ι _ he.exact
            mono_f := P.ι.mono_of_mono_map he.mono_f
            epi_g := P.ι.epi_of_epi_map he.epi_g }

/-- The kernel is literally the objects whose height-p stalks vanish. -/
theorem stratumStalks_kernel (p : ℕ) (M : CohAtLeast X p) :
    (stratumStalks X p).toFunctor.kernel M ↔
      ∀ x : HeightPoint X p, IsZero ((coherentStalk X x.1).toFunctor.obj M.obj) := by
  change IsZero ((stratumStalks X p).toFunctor.obj M) ↔ _
  constructor
  · intro h
    exact (isZero_family_iff _ _).mp
      ((finiteSupportProperty (localRings X p)).ι.map_isZero h)
  · intro h
    exact IsZero.of_full_of_faithful_of_isZero (finiteSupportProperty (localRings X p)).ι _
      ((isZero_family_iff _ _).mpr h)

/-- The actual kernel is exactly the next support condition, not a chosen abstract class. -/
theorem stratumStalks_kernel_next (p : ℕ) (M : CohAtLeast X p) :
    (stratumStalks X p).toFunctor.kernel M ↔ coherentAtLeast X (p + 1) M.obj := by
  rw [stratumStalks_kernel]
  constructor
  · intro h x
    have hx : ringKrullDim (X.presheaf.stalk x.1) ≤ p :=
      ENat.WithBot.lt_add_one_iff.mp (by simpa using x.2)
    rcases lt_or_eq_of_le hx with hlt | heq
    · exact M.property ⟨x.1, hlt⟩
    · exact h ⟨x.1, heq⟩
  · intro h x
    exact h ⟨x.1, by rw [x.2]; exact_mod_cast Nat.lt_succ_self p⟩

/-- At the last support stratum of a surface, no nonzero object is killed. -/
theorem stratumTwo_reflects_zero
    (hdim : AlgebraicGeometry.Scheme.SurfaceDimensionAtMostTwo X)
    (M : CohAtLeast X 2) (hM : (stratumStalks X 2).toFunctor.kernel M) : IsZero M := by
  have hs := (stratumStalks_kernel X 2 M).mp hM
  have hzero : IsZero M.obj.obj := by
    apply (Scheme.Modules.isZero_iff_stalks _).mpr
    intro x
    apply (moduleStalk_isZero_iff X M.obj.obj x).mp
    rcases lt_or_eq_of_le (hdim x) with hlt | heq
    · exact M.property ⟨x, hlt⟩
    · exact hs ⟨x, heq⟩
  have hzcoh : IsZero M.obj :=
    IsZero.of_full_of_faithful_of_isZero
        (Scheme.Modules.QuasiCoherent.finiteTypeSheavesToModules X) _ hzero
  exact IsZero.of_full_of_faithful_of_isZero (coherentAtLeast X 2).ι _ hzcoh

end AlgebraicGeometry.Scheme.Modules.Coherent.Support
