# scheme-4 milestones

## Files processed
- numina/blueprints/scheme-4/scheme-4.tex (rewritten)
- numina/.metadata/blueprints/scheme-4/blueprint.json (entries populated)
- numina/.metadata/blueprints/scheme-4/declarations/*.json (10 entries via update_declaration)
- FLT/Scheme4.lean (new umbrella import)
- FLT/Scheme4/Basic.lean (new, 3 wrappers)
- FLT.lean (added `import FLT.Scheme4`)

## Declarations
| label | lean_name | status |
|---|---|---|
| def:presheaf | FLT.Scheme4.RingPresheaf | proved |
| def:sheaf | FLT.Scheme4.RingSheaf | proved |
| def:ringed-space | AlgebraicGeometry.RingedSpace | proved (Mathlib) |
| def:stalk | TopCat.Presheaf.stalk | proved (Mathlib) |
| def:locally-ringed-space | AlgebraicGeometry.LocallyRingedSpace | proved (Mathlib) |
| def:spectrum | PrimeSpectrum | proved (Mathlib) |
| def:structure-sheaf | AlgebraicGeometry.Spec.structureSheaf | proved (Mathlib) |
| def:affine-scheme | FLT.Scheme4.IsAffineScheme | proved |
| def:scheme | AlgebraicGeometry.Scheme | proved (Mathlib) |
| def:scheme-hom | AlgebraicGeometry.Scheme.Hom | proved (Mathlib) |

## Build
- `lake build FLT.Scheme4`: success (no errors, no warnings).
- Full project build fails on pre-existing, unrelated `FLT.Deformations.Subfunctor` (Mathlib name clash); not caused by this work.

## Notes
- The metadata status enum allows only `not_started`, `in_progress`, `proved`. Used `proved` for definitions since their content is the type itself.
- `refresh_blueprint_metadata` may overwrite the hand-authored `entries` array in `blueprint.json` back to the parser's default schema; if that matters, regenerate after parser changes.
