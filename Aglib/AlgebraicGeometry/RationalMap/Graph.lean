/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.IsIso.OpenSection
public import Aglib.AlgebraicGeometry.SchemeTheoreticImage.Integral
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Aglib.AlgebraicGeometry.SchemeOverField

/-!
# Actual rational graph closures over a field

Source: `R5Lab.Aglib.AlgebraicGeometry.RationalMap.Graph`.
R5 packet revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256: `fc367c1428de43bc2204d2eb9bf9eca5a789fe03d739040a1d50bcdfd1882ea6`.
Actual objects, maps, universes and hypotheses are retained.
Native declaration ownership replaces the source application namespaces.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.OverField (FScheme)
/- Component: GraphImage; declaration bodies preserved. -/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace AlgebraicGeometry.Scheme
universe u

variable {K : Type u} [Field K] (X P : FScheme K)
    (U : X.left.Opens) (r : U.toScheme ⟶ P.left)
    (hr : U.ι ≫ X.hom = r ≫ P.hom)

/-- The graph map uses the original structural maps in the fiber product. -/
def rationalGraph : U.toScheme ⟶ pullback X.hom P.hom := pullback.lift U.ι r hr

@[reassoc (attr := simp)] theorem rationalGraph_fst :
    rationalGraph X P U r hr ≫ pullback.fst X.hom P.hom = U.ι := by
  simp [rationalGraph]
@[reassoc (attr := simp)] theorem rationalGraph_snd :
    rationalGraph X P U r hr ≫ pullback.snd X.hom P.hom = r := by
  simp [rationalGraph]

instance rationalGraph_isImmersion : IsImmersion (rationalGraph X P U r hr) := by
  have : IsImmersion (rationalGraph X P U r hr ≫ pullback.fst X.hom P.hom) := by
    rw [rationalGraph_fst]; infer_instance
  exact IsImmersion.of_comp _ (pullback.fst X.hom P.hom)

instance rationalGraph_quasiCompact [IsNoetherian X.left] :
    QuasiCompact (rationalGraph X P U r hr) := by
  let : NoetherianSpace U.toScheme := U.ι.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  exact quasiCompact_of_noetherianSpace_source _

/-- The schematic closure of the graph, over the unchanged base field. -/
def rationalGraphImage : FScheme K :=
  Over.mk ((rationalGraph X P U r hr).imageι ≫ pullback.fst X.hom P.hom ≫ X.hom)

/-- The projection from the scheme-theoretic rational graph image to the source scheme. -/
def rationalGraphProjectionLeft : rationalGraphImage X P U r hr ⟶ X :=
  Over.homMk ((rationalGraph X P U r hr).imageι ≫ pullback.fst X.hom P.hom) (by rfl)

/-- The projection from the scheme-theoretic rational graph image to the target scheme. -/
def rationalGraphProjectionRight : rationalGraphImage X P U r hr ⟶ P :=
  Over.homMk ((rationalGraph X P U r hr).imageι ≫ pullback.snd X.hom P.hom) (by
    change _ = (rationalGraph X P U r hr).imageι ≫ pullback.fst X.hom P.hom ≫ X.hom
    rw [Category.assoc, pullback.condition])

instance rationalGraphProjectionLeft_isProper [IsProper P.hom] :
    IsProper (rationalGraphProjectionLeft X P U r hr).left := by
  change IsProper ((rationalGraph X P U r hr).imageι ≫ pullback.fst X.hom P.hom)
  infer_instance
instance rationalGraphProjectionRight_isProper [IsProper X.hom] :
    IsProper (rationalGraphProjectionRight X P U r hr).left := by
  change IsProper ((rationalGraph X P U r hr).imageι ≫ pullback.snd X.hom P.hom)
  infer_instance

instance rationalGraphImage_isIntegral [IsIntegral X.left] [Nonempty U]
    [IsNoetherian X.left] : IsIntegral (rationalGraphImage X P U r hr).left := by
  let : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  exact schemeImage_isIntegral (rationalGraph X P U r hr)

instance rationalGraph_toImage_isOpenImmersion [IsNoetherian X.left] :
    IsOpenImmersion (rationalGraph X P U r hr).toImage := inferInstance

@[reassoc (attr := simp)] theorem rationalGraph_toImage_projectionLeft :
    (rationalGraph X P U r hr).toImage ≫
      (rationalGraphProjectionLeft X P U r hr).left = U.ι := by
  simp [rationalGraphProjectionLeft]


instance rationalGraphProjectionLeft_isDominant [IsIntegral X.left] [Nonempty U] :
    IsDominant (rationalGraphProjectionLeft X P U r hr).left := by
  let : IsDominant U.ι := ⟨U.ι.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  let : IsDominant ((rationalGraph X P U r hr).toImage ≫
      (rationalGraphProjectionLeft X P U r hr).left) := by
    rw [rationalGraph_toImage_projectionLeft]; infer_instance
  exact IsDominant.of_comp (rationalGraph X P U r hr).toImage _

instance rationalGraphProjectionRight_isDominant [IsDominant r] :
    IsDominant (rationalGraphProjectionRight X P U r hr).left := by
  have h : (rationalGraph X P U r hr).toImage ≫
      (rationalGraphProjectionRight X P U r hr).left = r := by
    simp [rationalGraphProjectionRight]
  let : IsDominant ((rationalGraph X P U r hr).toImage ≫
      (rationalGraphProjectionRight X P U r hr).left) := by
    rw [h]; infer_instance
  exact IsDominant.of_comp (rationalGraph X P U r hr).toImage _

instance rationalGraphProjectionLeft_restrict_isIso [IsIntegral X.left] [Nonempty U]
    [IsNoetherian X.left] [IsProper P.hom] :
    IsIso ((rationalGraphProjectionLeft X P U r hr).left ∣_ U) :=
  isIso_restrict_of_open_section _ U (rationalGraph X P U r hr).toImage
    (rationalGraph_toImage_projectionLeft X P U r hr)

instance rationalGraphImage_isNoetherian [IsNoetherian X.left] [IsProper P.hom] :
    IsNoetherian (rationalGraphImage X P U r hr).left := by
  let : IsLocallyNoetherian (rationalGraphImage X P U r hr).left :=
    LocallyOfFiniteType.isLocallyNoetherian (rationalGraphProjectionLeft X P U r hr).left
  let : CompactSpace (rationalGraphImage X P U r hr).left :=
    QuasiCompact.compactSpace_of_compactSpace (rationalGraphProjectionLeft X P U r hr).left
  exact ⟨⟩

end AlgebraicGeometry.Scheme
end


noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite Order
open _root_.AlgebraicGeometry.Scheme.OverField (FScheme)
universe u
namespace AlgebraicGeometry.Scheme
variable {K : Type u} [Field K] (X : FScheme K)
/-- The open cover of the underlying scheme of `X` by all affine opens. -/
def graphBaseOpenCover : X.left.OpenCover :=
  X.left.openCoverOfIsOpenCover _ (iSup_affineOpens_eq_top X.left)


end AlgebraicGeometry.Scheme
