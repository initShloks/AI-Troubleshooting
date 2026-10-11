# Faultline: AI Troubleshooting Expert System

A rule-based expert system for laptop faults, built on first-order logic.

The diagnosis flow asks targeted questions, shows its proof and certainty score,
and can download a plain-text report with the conclusion, recommended steps,
answers, and supporting rule.

## Files

| File | Contents |
|---|---|
| `index.html` | Page structure and tabs |
| `styles.css` | All styling (light and dark themes) |
| `engine.js` | Logic engine: terms, parser, knowledge base, unification, backward chaining, forward chaining, resolution |
| `app.js` | UI: rendering, state, event handling |

Custom rules and facts are validated as a complete submission before they are
added, so a rejected multi-line entry does not leave partial changes behind.

## Run it in VS Code

1. Put all four files in one folder and open that folder in VS Code.
2. Install the **Live Server** extension (by Ritwick Dey).
3. Right-click `index.html` and choose **Open with Live Server**.

You can also double-click `index.html` to open it in a browser. No install or build step is needed.

## Syllabus mapping

| Topic | Where in the code |
|---|---|
| Knowledge representation | `KB_SRC`, `ASK`, `FAULTS` in `engine.js` |
| Predicates and FOL syntax | `mkParser`, `parseProgram` |
| Unification (MGU, occurs check) | `unify`, `bindVar` |
| Backward chaining | `makeProver` (asks questions through `AskNeeded`) |
| Forward chaining | `forwardChain` |
| CNF and resolution | `toClauses`, `resolvePair`, `refute`, `proofLedger` |
| Certainty factors | `cf` in `makeProver` (rule cf × weakest premise) |

## Rule syntax

```
w6 [0.9]: device(D), router(R), wifi_on(D), router_ok(R), not associated(D, R) => suspect(D, adapter).
device(lap).
```

Variables start with an uppercase letter. Constants and predicates start lowercase. `[0.9]` is the rule's certainty factor.

## Testing the engine in Node

`engine.js` exports its functions when run in Node:

```js
const E = require('./engine.js');
E.buildKB([]);
console.log(E.solveAll('fault(wifi, X)', E.PRESETS['wifi-brief'].answers).sols[0].binding);
```
