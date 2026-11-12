import Volume01.A.chapters.Chapter01.sections.Section01.Formalization
import Volume01.A.chapters.Chapter01.sections.Section02.Formalization
import Volume01.A.chapters.Chapter01.sections.Section03.Formalization
import Volume01.A.chapters.Chapter01.sections.Section04.Formalization
import Volume01.A.chapters.Chapter01.sections.Section05.Formalization
import Volume01.A.chapters.Chapter01.sections.Section06.Formalization
import Volume01.A.chapters.Chapter01.sections.Section07.Formalization
import Volume01.A.chapters.Chapter01.sections.Section08.Formalization
import Volume01.A.appendices.A.sections.Section01.Formalization
import Volume01.A.appendices.A.sections.Section02.Formalization
import Lean.Util.CollectAxioms

/-!
# Chapter 1 partial-coverage axiom gate

Inspect every logical project declaration in the imported environment, including
private proof helpers. `collectAxioms` traverses actual kernel declarations and
their dependencies; this is not a search for words in source text.

Unsafe/partial compiler implementation artifacts are not logical declarations.
They cannot occur in a safe theorem's kernel proof. The runner separately rejects
user-written unsafe/partial definitions in the project source snapshot.

Only Lean's ordinary foundational axioms are accepted. In particular `sorryAx`,
extra mathematical axioms, and native-evaluation trust axioms cause failure.
This gate does not replace Steven's review of mathematical correspondence.
-/

set_option autoImplicit false

set_option maxHeartbeats 0 in
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count := 0
  for (name, info) in env.constants.toList do
    let text := name.toString
    if (text.startsWith "TraceFormulas." ||
        text.startsWith "_private.TraceFormulas." ||
        text.startsWith "_private.Volume01.A.chapters.Chapter01." ||
        text.startsWith "_private.Volume01.A.appendices.A.") &&
        !info.isUnsafe && !info.isPartial then
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "Forbidden axiom {axiomName} in {name}"
      let report := Json.mkObj [
        ("declaration", toJson name.toString),
        ("axioms", toJson (axioms.map Name.toString))]
      logInfo m!"AXIOM_AUDIT_JSON {report.compress}"
      count := count + 1
  if count == 0 then throwError "No project declarations were audited"
  logInfo m!"AXIOM_AUDIT_CHECKED {count}"
