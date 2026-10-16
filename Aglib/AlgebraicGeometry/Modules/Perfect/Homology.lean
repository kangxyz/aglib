/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Homology
public import Aglib.AlgebraicGeometry.Modules.Perfect.LocalModels

/-! # Compatibility import for native perfect-complex homology

The sole implementation is `PerfectComplexes.Homology`: quasicoherence and
local homology bounds are unchanged, and global bounds still require the
original compactness hypothesis. The legacy model import preserves old
transitive namespace aliases without another mathematical implementation.
-/
