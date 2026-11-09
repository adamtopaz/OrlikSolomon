/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import OrlikSolomonBook.Blueprint

/-!
# Blueprint parser regressions

Run with `lake env lean -DmaxSynthPendingDepth=3 -DautoImplicit=false
scripts/tests/book-blueprint-parser.lean`. Section labels may follow whitespace and comments,
but orphan labels, missing theorem labels and duplicated labels must not disappear from tracking.
Custom node markers organize the fourth blueprint without replacing its theorem labels.
-/

open OrlikSolomonBook.Blueprint

-- The earlier blueprints put section labels on the same line as their headings.
#guard ((parseNodes r"\section{Heading}\label{sec:heading}
\begin{lemma}[A title]\label{lem:test}
Statement.
\end{lemma}").toOption.map (·.size)) == some 1

-- The fourth blueprint puts them on the following line.
#guard ((parseNodes r"\section{Heading}
\label{sec:heading}
\begin{lemma}\label{lem:test}
Statement.
\end{lemma}").toOption.map (fun nodes => nodes.map (·.label))) == some #["lem:test"]

-- Blank lines and stripped comments are whitespace, not intervening prose.
#guard ((parseNodes r"\subsection{Heading}
% A comment.

\label{sec:heading}
\begin{theorem}\label{thm:test}
Statement.
\end{theorem}").toOption.map (·.size)) == some 1

#guard !(parseNodes r"Orphan.
\label{bad:orphan}").isOk

#guard !(parseNodes r"\section{Heading}
Intervening prose.
\label{bad:prose}").isOk

#guard !(parseNodes r"\begin{lemma}\label{lem:test}
Statement.
\end{lemma}
\begin{theorem}
An unlabeled statement.
\end{theorem}").isOk

#guard !(parseNodes r"\begin{lemma}\label{lem:test}\label{bad:extra}
Statement.
\end{lemma}").isOk

-- Both members of a definition-and-lemma pair remain independent coverage obligations.
#guard ((parseNodes r"\node{U01}{Proposed.name}{Dependencies}
\begin{definition}\label{def:u01}
Definition.
\end{definition}
\begin{lemma}\label{lem:u01}
Statement.
\end{lemma}").toOption.map (fun nodes => nodes.map (·.label))) == some #["def:u01", "lem:u01"]

-- readNodes rejects this result, including when duplicates come from different source files.
#guard match parseNodes r"\begin{lemma}\label{lem:test}
Statement.
\end{lemma}
\begin{theorem}\label{lem:test}
Another statement.
\end{theorem}" with
  | .ok nodes => duplicateLabels nodes == ["lem:test"]
  | .error _ => false

#guard ((parseNodes r"% \begin{lemma}\label{lem:commented}
").toOption.map (·.size)) == some 0
