/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalModels
public import Aglib.AlgebraicGeometry.Modules.Perfect.LocalRestriction

/-! # Compatibility import for actual global strict-model witnesses

The sole native `HasStrictModel` and its restriction statements are in
`PerfectComplexes.LocalModels`. The legacy restriction import also preserves
old transitive names as transparent canonical delegates.
-/
