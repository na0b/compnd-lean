/- Run with `lake env lean Axioms.lean` after `lake build`.
Every result below should depend only on `propext`, `Classical.choice` and `Quot.sound`. -/
import CompND

#print axioms ComparisonUnderNondegeneracy
#print axioms ComparisonUnconditional
