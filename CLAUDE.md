<!-- OPENSPEC:START -->
# OpenSpec Instructions

These instructions are for AI assistants working in this project.

Always open `@/openspec/AGENTS.md` when the request:
- Mentions planning or proposals (words like proposal, spec, change, plan)
- Introduces new capabilities, breaking changes, architecture shifts, or big performance/security work
- Sounds ambiguous and you need the authoritative spec before coding

Use `@/openspec/AGENTS.md` to learn:
- How to create and apply change proposals
- Spec format and conventions
- Project structure and guidelines

Keep this managed block so 'openspec update' can refresh the instructions.

<!-- OPENSPEC:END -->

# Lean MCP

When writing or repairing Lean proofs, use the Lean MCP tools (`lean_goal`,
`lean_diagnostic_messages`, `lean_multi_attempt`, `lean_hover_info`, etc.)
to inspect proof states and test tactics **before** editing files. This avoids
blind edit-build cycles. In particular:

- Use `lean_goal` at a `sorry` to see the exact goal and hypotheses.
- Use `lean_multi_attempt` to trial several tactic alternatives without editing.
- Use `lean_diagnostic_messages` to check a file for errors without `lake build`.

# Checklist

Before stopping work, always read `checklist.md` and continue working through
unchecked items. Do not stop until every item is checked off. Run `lake build`
after each phase to confirm zero `sorry` and no errors.