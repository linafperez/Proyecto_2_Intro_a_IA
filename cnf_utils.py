"""
cnf_utils.py — shared utilities for CNF conversion and resolution.

Used by:
  fol_to_cnf.py      — FOL → CNF pipeline (reads a .txt KB, writes *_CNF.txt)
  resolution_prover.py — resolution refutation prover (reads *_CNF.txt)

Key design decision
───────────────────
BinaryTreeNode predicates are stored as  node.data = "Pred()"  with
  node.left_child  = first argument  (a leaf or nested predicate node)
  node.right_child = second argument (a leaf or nested predicate node, or None)

The string representation used throughout the prover is the flat infix form
produced by tree_to_infix(), e.g. "Leal(K1, Cesar)" or "NOT Animal(X)".
"""

import re
from BinaryTreeNode import BinaryTreeNode


# ══════════════════════════════════════════════════════════════
#  TREE → STRING  (reused from main.py, now shared)
# ══════════════════════════════════════════════════════════════

def tree_to_infix(node, is_root=True) -> str:
    """
    Serialise a BinaryTreeNode expression tree to an infix string.
    Binary operators are wrapped in [...] unless they are the root.
    """
    if node is None:
        return ""

    data = node.data
    binary_ops  = {"AND", "OR", "->", "<->"}
    unary_ops   = {"NOT"}
    quantifiers = {"FORALL", "EXISTS"}

    if data in binary_ops:
        left  = tree_to_infix(node.left_child,  False)
        right = tree_to_infix(node.right_child, False)
        expr  = f"{left} {data} {right}"
        return expr if is_root else f"[{expr}]"

    elif data in unary_ops:
        child = tree_to_infix(node.left_child, False)
        return f"{data} {child}"

    elif data in quantifiers:
        var     = tree_to_infix(node.left_child,  False)
        formula = tree_to_infix(node.right_child, False)
        expr    = f"{data} {var} {formula}"
        return expr if is_root else f"[{expr}]"

    elif "()" in data:                          # predicate node  e.g. "Leal()"
        name = data.replace("()", "")
        args = []
        if node.left_child:
            args.append(tree_to_infix(node.left_child,  False))
        if node.right_child:
            args.append(tree_to_infix(node.right_child, False))
        return f"{name}({', '.join(args)})"

    else:                                       # variable / constant leaf
        return data


# ══════════════════════════════════════════════════════════════
#  TREE → FROZENSET OF LITERAL STRINGS
#  Replaces resolution_prover's  tokenise → parse → ast_to_literals  pipeline.
#  Works directly on BinaryTreeNode objects produced by main.py's CNF pipeline.
# ══════════════════════════════════════════════════════════════

def tree_to_literals(node) -> frozenset:
    """
    Flatten a CNF clause tree (a pure OR-tree of literals) into a frozenset
    of literal strings, e.g. frozenset({'NOT Animal(X)', 'Ama(Jack, X)'}).

    Each literal is the infix string of a NOT-subtree or a predicate leaf.
    AND nodes are handled gracefully (should not appear inside a single clause).
    """
    if node is None:
        return frozenset()

    data = node.data

    if data == "OR":
        return tree_to_literals(node.left_child) | tree_to_literals(node.right_child)

    if data == "AND":
        # Defensive: split into separate clauses if AND appears (shouldn't in CNF clause)
        return tree_to_literals(node.left_child) | tree_to_literals(node.right_child)

    # A literal: either "NOT <something>" or a bare predicate/atom
    return frozenset({tree_to_infix(node)})


# ══════════════════════════════════════════════════════════════
#  EXTRACT CLAUSES FROM A CNF TREE  (moved from main.py)
# ══════════════════════════════════════════════════════════════

def extract_clauses(node) -> list:
    """
    Split a CNF tree (a conjunction of clauses) into a list of clause trees.
    AND nodes are recursively split; anything else is a single clause.
    """
    if node is None:
        return []
    if node.data == "AND":
        return extract_clauses(node.left_child) + extract_clauses(node.right_child)
    return [node]


# ══════════════════════════════════════════════════════════════
#  CLAUSE → DISPLAY STRING  (replaces clause_str in prover)
# ══════════════════════════════════════════════════════════════

def clause_str(clause: frozenset) -> str:
    """Pretty-print a clause frozenset as 'Lit1 OR Lit2 OR ...'."""
    if not clause:
        return "□"
    return " OR ".join(sorted(clause))


# ══════════════════════════════════════════════════════════════
#  FILE I/O
#  parse_cnf_file  — reads a *_CNF.txt file written by fol_to_cnf.py.
#  The prover calls this instead of its own parse_file().
#  fol_to_cnf.py calls write_cnf_file() to produce the same format.
# ══════════════════════════════════════════════════════════════

def _parse_cnf_line(content: str) -> frozenset:
    """
    Parse one CNF clause line (already stripped of its numeric label) into a
    frozenset of literal strings.

    The format written by fol_to_cnf.py uses tree_to_infix(), so it contains
    'NOT', 'OR', and '[...]' grouping.  We walk the text token-by-token using a
    tiny recursive-descent parser that produces BinaryTreeNode trees and then
    calls tree_to_literals() — reusing the same tree machinery as the rest of
    the pipeline.

    Alternatively (simpler path): since the clause is already a flat disjunction
    of literals at this point, we can tokenise and group without a full parser.
    We use the full parser for correctness with deeply nested brackets like
    [[NOT A OR NOT B] OR NOT C].
    """
    from BinaryTree import BinaryTree   # local import to avoid circular deps

    tree_root = BinaryTree.build_expression_tree(content)
    return tree_to_literals(tree_root)


def parse_cnf_file(path: str):
    """
    Read a *_CNF.txt file produced by fol_to_cnf.py.

    Returns
    -------
    clauses    : list of (label_str, frozenset_of_literals, raw_line_text)
    query_text : str  — the raw query expression (after 'Q ')
    """
    clauses    = []
    query_text = None

    with open(path, "r", encoding="utf-8") as fh:
        for line in fh:
            line = line.rstrip("\n").strip()
            if not line or line.startswith("#"):
                continue
            parts = line.split(maxsplit=1)
            if len(parts) < 2:
                continue
            identifier, content = parts[0], parts[1].strip()

            if identifier == "Q":
                query_text = content
            elif identifier.isdigit():
                lits = _parse_cnf_line(content)
                clauses.append((identifier, lits, content))

    if query_text is None:
        raise ValueError(f"No query line (Q ...) found in '{path}'.")

    return clauses, query_text


def write_cnf_file(output_path: str, cnf_trees: list, query: str) -> None:
    """
    Write a list of CNF clause trees to *_CNF.txt format.
    Mirrors the output block at the end of the original main.py.
    """
    with open(output_path, "w", encoding="utf-8") as f:
        for i, tree in enumerate(cnf_trees, start=1):
            f.write(f"{i} {tree_to_infix(tree)}\n")
        f.write(f"Q {query}\n")
