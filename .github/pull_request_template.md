## What this changes

Write one or two sentences.

## Milestone

Refers to tamnd/mmp#

## Checks

- [ ] `lake build` passes.
- [ ] `sh scripts/scan.sh` passes: no `sorry`, `admit`, `axiom` or `native_decide` outside `MinimalModel/WIP/`.
- [ ] If a file of `MinimalModel/Statements/` changes, `manifests/statements.sha256` changes too, and the pull request has the label `type/statement`.
- [ ] Each new node of the map in tamnd/mmp names the new declaration.
- [ ] The pull request has one `area/*` label and one `type/*` label.
