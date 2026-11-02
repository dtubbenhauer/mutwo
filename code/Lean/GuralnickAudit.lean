import Guralnick.AxiomAudit
import Guralnick.GuardedAudit

/-!
# Verification target

Build `Guralnick` for the mathematical library alone. Build `GuralnickAudit`
for diagnostic output, failing axiom guards and exact endpoint applications.
The default `lake build` builds both targets.
-/
