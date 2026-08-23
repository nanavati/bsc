# KB deposit procedure: bsc typeclass coherence

Goal: deposit two new entries into the KB (ravi@matx.com's cross-agent
knowledge base kept as never-sent Gmail drafts titled "KB: <topic>")
and register them in the bootstrap index.

Steps (follow the KB's own bootstrap rule):

1. Load Gmail MCP tools via ToolSearch. List drafts with query
   subject:"KB:" (use the drafts listing — thread search does not
   return drafts).
2. READ FIRST: "KB: cross-agent Gmail draft protocol". Follow any
   conventions there that contradict this file (the protocol wins).
3. Read "KB: agent bootstrap and handoff index" (draft id
   r-9093101298179149502 as of 2026-08-23, v21).
4. Create draft #1: subject "KB: bsc typeclass coherence",
   NO recipients, body = kb-deposit/lane-entry.txt verbatim.
5. Create draft #2: subject
   "KB: bsc typeclass coherence dev note (full text)",
   NO recipients, body = kb-deposit/devnote-mirror.txt verbatim.
   After saving, re-read it and diff the mirrored body against
   git blob 82ca05e0 (doc/dev-notes/typechecker-coherent-instance-
   commitment.md at branch claude/typechecker-coherent-instances-dkmn8w,
   commit 1b35eb7d); differences beyond Gmail auto-linkification must
   be fixed.
6. Update the index: RE-READ it immediately before editing (documented
   stale-base clobber hazard), then add entries for both new drafts in
   the index's own format (one-line summary each; the lane entry is
   the design digest for the typeclass-coherence PR stack #1033/#1035-
   #1038; the mirror is the full-text dev note). Save via update_draft,
   then re-read to confirm the save took.
7. NEVER send any draft. Report what was created (draft ids) and the
   diff-verification result.

Author context: this content was produced by the Claude session that
built the coherent-instances PR stack (session_01YMPXjaiFCjeVJv1TbhYfd5
and its continuation). The KB previously had zero coverage of this
design line.
