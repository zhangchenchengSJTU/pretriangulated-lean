import PretriangulatedV2
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
Check the axioms of every imported project declaration, including private
declarations, definitions, and instances. Only the three standard Lean axioms
below are accepted; incomplete proofs also fail this check.
-/

open Lean Elab Command

#check PretriangulatedV2.MainTheorem.theorem_1_1
#check PretriangulatedV2.ConcreteCounterexample.corollary_1_2
#check PretriangulatedV2.ConcreteFieldExample.counterexample

run_cmd do
  let env ← getEnv
  let projectModules := env.header.moduleNames.map fun moduleName =>
    (`PretriangulatedV2).isPrefixOf moduleName
  let names := env.constants.toList.filterMap fun (name, _) =>
    match env.getModuleIdxFor? name with
    | some idx =>
      if (projectModules[idx]?).getD false then some name else none
    | none => none
  if names.isEmpty then
    throwError "No project declarations imported"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    let axioms ← collectAxioms name
    let unexpected := axioms.filter (fun ax => !allowed.contains ax)
    unless unexpected.isEmpty do
      throwError "Unexpected axioms in {name}: {unexpected}"
  logInfo m!"Axiom audit passed for {names.length} declarations; allowed: {allowed}"
