import JSP572Four
open Lean

#print axioms JSP572Four.singletonFree_four_bound
#print axioms JSP572Four.singletonFree_four_bound_fin
#print axioms JSP572Four.sharpBound_attained
#print axioms JSP572Four.exact_extremal_value
#print axioms JSP572Four.jsp572_four_complete

#check JSP572Four.jsp572_four_complete

run_cmd do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[``JSP572Four.singletonFree_four_bound,
      ``JSP572Four.sharpBound_attained, ``JSP572Four.exact_extremal_value,
      ``JSP572Four.jsp572_four_complete] do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axiom dependencies in {name}: {axioms}"
  logInfo "Axiom allowlist audit passed."

example : JSP572Four.sharpBound 7 = 15 := by decide
example : JSP572Four.sharpBound 8 = 17 := by decide
example : JSP572Four.sharpBound 9 = 21 := by decide
example : JSP572Four.sharpBound 10 = 28 := by decide
