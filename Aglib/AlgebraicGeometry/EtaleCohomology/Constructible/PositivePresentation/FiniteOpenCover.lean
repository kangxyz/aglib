/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.TorsionColimit.BoundedPresentation
public import Aglib.CategoryTheory.Sites.Torsion.FinitePresentation.FiniteCover
public import Mathlib.Algebra.Homology.Square
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Square
public import Mathlib.AlgebraicGeometry.Restrict

/-! # Actual two-open-cover presentations of original free mod-n generators

The bounded and ambient presentations retain the original generator objects,
the original inclusion-induced maps, and the actual difference/sum cokernel
cofork. No positivity, invertibility or Noetherian premise is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation
namespace FiniteOpenCover

universe u

attribute [local instance] hasSheafifyLarge

open CategoryTheory.Sheaf.TorsionFinitePresentation

variable (X : Scheme.{u}) (n : ℕ)

local instance coefficientHasFiniteColimits :
    HasFiniteColimits (BoundedPresentation.Coefficient X n) :=
  @hasFiniteColimits_of_hasColimitsOfSize (BoundedPresentation.Coefficient X n) _
    (BoundedPresentation.coefficient_hasColimits X n)

local instance coefficientHasFiniteBiproducts :
    HasFiniteBiproducts (BoundedPresentation.Coefficient X n) := by
  let : HasFiniteCoproducts (BoundedPresentation.Coefficient X n) :=
    @hasFiniteCoproducts_of_hasFiniteColimits (BoundedPresentation.Coefficient X n) _
      (coefficientHasFiniteColimits X n)
  exact HasFiniteBiproducts.of_hasFiniteCoproducts

local instance coefficientHasBinaryBiproducts :
    HasBinaryBiproducts (BoundedPresentation.Coefficient X n) :=
  hasBinaryBiproducts_of_finite_biproducts (BoundedPresentation.Coefficient X n)

local instance boundedInclusionPreservesFiniteColimits :
    PreservesFiniteColimits (BoundedPresentation.inclusion X n) :=
  @PreservesColimitsOfSize.preservesFiniteColimits
    (BoundedPresentation.Coefficient X n) _ (AbelianSheaf.{u, u + 1} X) _
    (BoundedPresentation.inclusion X n) (BoundedPresentation.inclusion_preservesColimits X n)

/-- Original free scalar-quotient maps, inside the native full bounded coefficient category. -/
def coefficientFreeFunctor : X.Etale ⥤ BoundedPresentation.Coefficient X n :=
  TorsionZMod.Presentation.coefficientFreeFunctor X.smallEtaleTopology n

/-- The full bounded inclusion retains every original generator and its original map. -/
theorem coefficientFreeFunctor_inclusion :
    coefficientFreeFunctor X n ⋙ BoundedPresentation.inclusion X n =
      FiniteCover.freeFunctor.{u + 1} X.smallEtaleTopology n := rfl

/-- Evaluation of the original bounded-generator inclusion is literal section restriction. -/
theorem sections_restriction {U V : X.Etale} (f : U ⟶ V) (F : BoundedPresentation.Coefficient X n)
    (b : BoundedPresentation.free X n V ⟶ F) :
    BoundedPresentation.sectionsEquiv X n U F ((coefficientFreeFunctor X n).map f ≫ b) =
      F.obj.obj.map f.op (BoundedPresentation.sectionsEquiv X n V F b) :=
  TorsionZMod.Presentation.sections_restriction X.smallEtaleTopology n f F b

variable (sq : Square X.Etale) [Mono sq.f₂₄] [Mono sq.f₃₄]
  (hp : sq.IsPullback) (hcover : Sieve.ofTwoArrows sq.f₂₄ sq.f₃₄ ∈ X.smallEtaleTopology sq.X₄)

/-- The original free mod-n square as an actual square of native bounded coefficients. -/
def coefficientSquare : Square (BoundedPresentation.Coefficient X n) :=
  sq.map (coefficientFreeFunctor X n)

include hp hcover in
/-- Original binary-cover section amalgamation proves the actual bounded-generator pushout. -/
theorem coefficientSquare_isPushout : (coefficientSquare X n sq).IsPushout :=
  TorsionZMod.Presentation.coefficientSquare_isPushout X.smallEtaleTopology n sq hp hcover

/-- The original bounded difference-map cokernel cofork. -/
def coefficientCokernelCofork :
    CokernelCofork (biprod.lift ((coefficientFreeFunctor X n).map sq.f₁₂)
      (-((coefficientFreeFunctor X n).map sq.f₁₃))) :=
  (coefficientSquare X n sq).cokernelCofork

omit [Mono sq.f₂₄] [Mono sq.f₃₄] in
/-- Its point is the original generator on the actual union. -/
@[simp]
theorem coefficientCokernelCofork_pt :
    (coefficientCokernelCofork X n sq).pt = BoundedPresentation.free X n sq.X₄ := rfl

omit [Mono sq.f₂₄] [Mono sq.f₃₄] in
/-- Its quotient map is the sum of the original two inclusion-induced maps. -/
@[simp]
theorem coefficientCokernelCofork_π :
    (coefficientCokernelCofork X n sq).π =
      biprod.desc ((coefficientFreeFunctor X n).map sq.f₂₄)
        ((coefficientFreeFunctor X n).map sq.f₃₄) := rfl

include hp hcover in
/-- The displayed original bounded cofork is actually a cokernel. -/
def coefficientCokernelCoforkIsColimit : IsColimit (coefficientCokernelCofork X n sq) :=
  (coefficientSquare_isPushout X n sq hp hcover).isColimitCokernelCofork

include hp hcover in
/-- Inclusion preserves the same finite pushout on the original abelian sheaves. -/
theorem ambientSquare_isPushout :
    (sq.map (FiniteCover.freeFunctor.{u + 1} X.smallEtaleTopology n)).IsPushout := by
  have h := (coefficientSquare_isPushout X n sq hp hcover).map (BoundedPresentation.inclusion X n)
  exact h

/-- The ambient original cofork uses the same free quotient generators and the literal
original difference and sum maps. -/
def ambientCokernelCofork :
    CokernelCofork (biprod.lift (FiniteCover.freeMap.{u + 1} X.smallEtaleTopology n sq.f₁₂)
      (-(FiniteCover.freeMap.{u + 1} X.smallEtaleTopology n sq.f₁₃))) :=
  (sq.map (FiniteCover.freeFunctor.{u + 1} X.smallEtaleTopology n)).cokernelCofork

include hp hcover in
/-- The ambient cofork is a colimit of the actual original two inclusion maps. -/
def ambientCokernelCoforkIsColimit : IsColimit (ambientCokernelCofork X n sq) :=
  (ambientSquare_isPushout X n sq hp hcover).isColimitCokernelCofork

section Opens

variable {X} (U : X.Etale)

/-- An actual open subscheme of the original etale test scheme, with its original map to X. -/
def openChart (V : U.left.Opens) : X.Etale := by
  letI : AlgebraicGeometry.Etale U.hom := U.prop
  exact Scheme.Etale.mk (V.ι ≫ U.hom)

/-- The original open inclusion as a morphism in the original small-etale category. -/
def openInclusion (V : U.left.Opens) : openChart U V ⟶ U :=
  MorphismProperty.Over.homMk V.ι rfl

instance openInclusion_mono (V : U.left.Opens) : Mono (openInclusion U V) := by
  apply Functor.mono_of_mono_map (Scheme.Etale.forget X ⋙ Over.forget X)
  exact inferInstanceAs (Mono V.ι)

/-- The original inclusion between two actual open charts. -/
def openMap {V W : U.left.Opens} (h : V ≤ W) : openChart U V ⟶ openChart U W :=
  MorphismProperty.Over.homMk (U.left.homOfLE h) (by
    change U.left.homOfLE h ≫ (W.ι ≫ U.hom) = V.ι ≫ U.hom
    rw [← Category.assoc, Scheme.homOfLE_ι])

/-- The literal intersection square of the two given opens, in the original etale site. -/
def openSquare (V W : U.left.Opens) : Square X.Etale where
  X₁ := openChart U (V ⊓ W)
  X₂ := openChart U V
  X₃ := openChart U W
  X₄ := U
  f₁₂ := openMap U inf_le_left
  f₁₃ := openMap U inf_le_right
  f₂₄ := openInclusion U V
  f₃₄ := openInclusion U W
  fac := by
    apply MorphismProperty.Over.Hom.ext
    change U.left.homOfLE inf_le_left ≫ V.ι = U.left.homOfLE inf_le_right ≫ W.ι
    rw [Scheme.homOfLE_ι, Scheme.homOfLE_ι]

instance openSquareLeftMono (V W : U.left.Opens) : Mono (openSquare U V W).f₂₄ :=
  openInclusion_mono U V

instance openSquareRightMono (V W : U.left.Opens) : Mono (openSquare U V W).f₃₄ :=
  openInclusion_mono U W

theorem openSquare_isPullback (V W : U.left.Opens) : (openSquare U V W).IsPullback := by
  apply CategoryTheory.IsPullback.of_map (Scheme.Etale.forget X ⋙ Over.forget X)
    (openSquare U V W).fac
  exact AlgebraicGeometry.isPullback_opens_inf V W

theorem openSquare_cover (V W : U.left.Opens) (hVW : V ⊔ W = ⊤) :
    Sieve.ofTwoArrows (openSquare U V W).f₂₄ (openSquare U V W).f₃₄ ∈
      X.smallEtaleTopology U := by
  rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
  ext x
  simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
  have hx : x ∈ V ⊔ W := by rw [hVW]; trivial
  rcases hx with hx | hx
  · exact ⟨WalkingPair.left, ⟨x, hx⟩, rfl⟩
  · exact ⟨WalkingPair.right, ⟨x, hx⟩, rfl⟩

/-- The original free generator on U is the actual displayed cokernel of the
original overlap-to-two-opens difference map, for every coefficient modulus. -/
def openCoverCokernelIsColimit (V W : U.left.Opens) (hVW : V ⊔ W = ⊤) :
    IsColimit (coefficientCokernelCofork X n (openSquare U V W)) :=
  coefficientCokernelCoforkIsColimit X n (openSquare U V W)
    (openSquare_isPullback U V W) (openSquare_cover U V W hVW)

/-- The same actual original cokernel presentation in abelian sheaves. -/
def openCoverAmbientCokernelIsColimit (V W : U.left.Opens) (hVW : V ⊔ W = ⊤) :
    IsColimit (ambientCokernelCofork X n (openSquare U V W)) :=
  ambientCokernelCoforkIsColimit X n (openSquare U V W)
    (openSquare_isPullback U V W) (openSquare_cover U V W hVW)

end Opens

end FiniteOpenCover
end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation
