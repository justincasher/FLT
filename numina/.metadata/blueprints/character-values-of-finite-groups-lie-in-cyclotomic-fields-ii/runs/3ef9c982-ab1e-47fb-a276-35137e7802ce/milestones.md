# Milestones — character-values-of-finite-groups-lie-in-cyclotomic-fields-ii (resumed)

## Status from prior run
- Blueprint reviewed, reviewer fixes applied.
- 11 declarations formalized with sorries in FLT/Mathlib/RepresentationTheory/CharacterValuesCyclotomic.lean.
- Formalizer-reviewer PASS with minor fixes; minor fixes applied (dropped redundant hypotheses, linked cyclotomicEmbedding to AlgHom).
- Wave 1 leaf lemmas proved and merged:
  - cyclotomicField_isAlgebraic (Algebra.IsAlgebraic.of_finite)
  - representation_pow_exponent_eq_one (rw chain)
  - eigenvalue_pow_eq_one (eigenvector unpacking + smul)
  - hasEigenvalue_of_mem_charpoly_roots (charpoly iff + mem_roots)
  - trace_eq_charpoly_roots_sum (Matrix.trace_eq_sum_roots_charpoly_of_splits + IsAlgClosed)
  - multiset_sum_mem_subring (Subring.multiset_sum_mem)
- Module builds with zero errors / warnings.

## Plan from here
1. Wave 2 (parallel): cyclotomicEmbeddingAlgHom, mem_range_of_pow_eq_one, charpoly_roots_pow_eq_one.
2. Wave 3: trace_mem_range.
3. Wave 4: character_values_in_cyclotomic_field.
4. Final build, mark all proved in blueprint metadata.
