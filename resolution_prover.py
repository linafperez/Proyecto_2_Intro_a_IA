#!/usr/bin/env python3
"""
Resolution Theorem Prover — Proof by Refutation
Compatible with CNF files produced by main.py

File format (from main.py output):
  1 Hombre(Marco)
  2 NOT Pompeyano(K0) OR Romano(K0)
  3 [[NOT Hombre(K2) OR NOT Gobernante(K3)] OR NOT IntentaAsesinar(K2,K3)] OR NOT Leal(K2,K3)
  Q Odia(Marco,Cesar)

Operators:  NOT  OR  AND  (brackets [ ] for grouping)
Predicates: Name(arg1, arg2, ...)   — constants/Skolem terms are capitalised or K0,K1…
Variables:  lowercase identifiers
"""

import sys
import re


# ══════════════════════════════════════════════════════════════
#  TOKENISER
# ══════════════════════════════════════════════════════════════

def tokenise(text: str) -> list[str]:
    """
    Break an expression string into tokens:
      keywords  NOT OR AND
      brackets  [ ]
      predicates  Hombre(Marco)  treated as single atom token
      identifiers / constants
    """
    text = text.strip()
    tokens = []
    i = 0
    while i < len(text):
        # skip whitespace
        if text[i].isspace():
            i += 1
            continue
        # bracket
        if text[i] in '[]':
            tokens.append(text[i])
            i += 1
            continue
        # word (keyword, predicate name, variable, constant)
        m = re.match(r'[A-Za-z_]\w*', text[i:])
        if m:
            word = m.group()
            i += len(word)
            # check for predicate: word followed by '('
            if i < len(text) and text[i] == '(':
                # collect everything up to the matching ')'
                depth = 0
                j = i
                while j < len(text):
                    if text[j] == '(':
                        depth += 1
                    elif text[j] == ')':
                        depth -= 1
                        if depth == 0:
                            j += 1
                            break
                    j += 1
                tokens.append(word + text[i:j])
                i = j
            else:
                tokens.append(word)
            continue
        # anything else (comma inside predicates is consumed above)
        i += 1
    return tokens


# ══════════════════════════════════════════════════════════════
#  PARSER  — recursive descent
#  Grammar:
#    expr   ::= or_expr
#    or_expr  ::= and_expr (OR and_expr)*
#    and_expr ::= not_expr (AND not_expr)*
#    not_expr ::= NOT not_expr | atom
#    atom     ::= '[' expr ']' | PREDICATE | IDENTIFIER
# ══════════════════════════════════════════════════════════════

class ParseError(Exception):
    pass


def parse_expr(tokens: list[str], pos: int):
    return parse_or(tokens, pos)


def parse_or(tokens, pos):
    node, pos = parse_and(tokens, pos)
    while pos < len(tokens) and tokens[pos] == 'OR':
        pos += 1  # consume OR
        right, pos = parse_and(tokens, pos)
        node = ('OR', node, right)
    return node, pos


def parse_and(tokens, pos):
    node, pos = parse_not(tokens, pos)
    while pos < len(tokens) and tokens[pos] == 'AND':
        pos += 1
        right, pos = parse_not(tokens, pos)
        node = ('AND', node, right)
    return node, pos


def parse_not(tokens, pos):
    if pos < len(tokens) and tokens[pos] == 'NOT':
        pos += 1
        child, pos = parse_not(tokens, pos)
        return ('NOT', child), pos
    return parse_atom(tokens, pos)


def parse_atom(tokens, pos):
    if pos >= len(tokens):
        raise ParseError("Unexpected end of tokens")
    tok = tokens[pos]
    if tok == '[':
        pos += 1  # consume '['
        node, pos = parse_expr(tokens, pos)
        if pos >= len(tokens) or tokens[pos] != ']':
            raise ParseError("Expected ']'")
        pos += 1  # consume ']'
        return node, pos
    # predicate or identifier
    return ('ATOM', tok), pos + 1


def parse_clause_text(text: str):
    """Parse a clause string into an AST tuple."""
    tokens = tokenise(text)
    if not tokens:
        return None
    node, pos = parse_expr(tokens, 0)
    if pos != len(tokens):
        raise ParseError(f"Unexpected token '{tokens[pos]}' in: {text}")
    return node


# ══════════════════════════════════════════════════════════════
#  AST → set of literals  (only valid for CNF disjunctions)
# ══════════════════════════════════════════════════════════════

def ast_to_literals(node) -> frozenset[str]:
    """
    Flatten an OR-tree of literals into a frozenset of literal strings.
    Literal: 'Pred(...)' or 'NOT Pred(...)'
    """
    if node is None:
        return frozenset()
    kind = node[0]
    if kind == 'OR':
        return ast_to_literals(node[1]) | ast_to_literals(node[2])
    if kind == 'NOT':
        inner = node[1]
        # inner should be an ATOM
        return frozenset({f"NOT {inner[1]}"})
    if kind == 'ATOM':
        return frozenset({node[1]})
    if kind == 'AND':
        # Should not appear inside a CNF clause — but handle gracefully
        return ast_to_literals(node[1]) | ast_to_literals(node[2])
    return frozenset()


# ══════════════════════════════════════════════════════════════
#  FILE PARSING
# ══════════════════════════════════════════════════════════════

def parse_file(path: str):
    clauses = []   # list of (original_label, frozenset_of_literals, raw_text)
    query_text = None

    with open(path, 'r', encoding='utf-8') as fh:
        for line in fh:
            line = line.rstrip('\n').strip()
            if not line or line.startswith('#'):
                continue
            parts = line.split(maxsplit=1)
            if len(parts) < 2:
                continue
            identifier, content = parts[0], parts[1]

            if identifier == 'Q':
                query_text = content.strip()
            elif identifier.isdigit():
                ast = parse_clause_text(content)
                lits = ast_to_literals(ast)
                clauses.append((identifier, lits, content))

    if query_text is None:
        raise ValueError("No query line (Q ...) found.")
    return clauses, query_text


# ══════════════════════════════════════════════════════════════
#  UNIFICATION  (Robinson's algorithm)
# ══════════════════════════════════════════════════════════════

def split_args(s: str) -> list:
    """Split comma-separated args respecting nested parentheses."""
    args, depth, current = [], 0, []
    for ch in s:
        if ch == '(':
            depth += 1; current.append(ch)
        elif ch == ')':
            depth -= 1; current.append(ch)
        elif ch == ',' and depth == 0:
            args.append(''.join(current).strip()); current = []
        else:
            current.append(ch)
    if current:
        args.append(''.join(current).strip())
    return [a for a in args if a]


def parse_predicate(atom: str):
    """
    'Leal(K1, Cesar)'  -> ('Leal', ['K1', 'Cesar'])
    'Animal(F0(X))'    -> ('Animal', ['F0(X)'])
    'Ama(F1(X), X)'    -> ('Ama', ['F1(X)', 'X'])
    'Marco'            -> ('Marco', [])
    """
    atom = atom.strip()
    m = re.match(r'^([A-Za-z_]\w*)\((.+)\)$', atom)
    if m:
        return m.group(1), split_args(m.group(2))
    return atom, []


def is_variable(s: str) -> bool:
    """
    Unifiable (variable) terms:
      - Single uppercase letters X, Y, Z  (FOL variable convention in main.py)
      - Lowercase identifiers x, y, z
      - Skolem constants K0, K1, K2 ...   (from EXISTS with no outer FORALL)
      - Renamed variants: X_r1, K0_r2 ... (produced by rename_vars)
    Ground (non-unifiable) constants:
      - Multi-char uppercase words: Marco, Cesar, Jack, Tuna, Curiosidad, ...
      - Skolem function names F0, F1 ... are compound terms handled by unify_terms
    """
    if not s:
        return False
    # Strip any _rN renaming suffix added by rename_vars
    base = re.sub(r'(_r\d+)+$', '', s)
    # Single uppercase letter: X, Y, Z
    if re.fullmatch(r'[A-Z]', base):
        return True
    # Skolem constants: K followed only by digits
    if re.fullmatch(r'K\d+', base):
        return True
    # Classic lowercase variable
    if base and base[0].islower():
        return True
    return False


def apply_subst(term: str, subst: dict) -> str:
    """
    Apply substitution to a term, recursing into compound functor terms.
    e.g. F0(X) with {X: Marco} -> F0(Marco)
    e.g. X     with {X: Marco} -> Marco
    """
    # If the term itself is directly mapped, follow the chain
    seen = set()
    t = term
    while t in subst and t not in seen:
        seen.add(t)
        t = subst[t]
    # If we made a substitution at the top level, return that
    if t != term:
        return t
    # Otherwise, try to recurse into functor arguments: F0(X), F1(X, Y)
    name, args = parse_predicate(term)
    if args:
        new_args = [apply_subst(a, subst) for a in args]
        return f"{name}({', '.join(new_args)})"
    return term


def apply_subst_to_literal(lit: str, subst: dict) -> str:
    """Apply substitution to a full literal string, recursing into functor args."""
    if not subst:
        return lit
    negated = lit.startswith('NOT ')
    atom = lit[4:] if negated else lit
    name, args = parse_predicate(atom)
    if not args:
        # Could be a plain variable or constant
        new_atom = apply_subst(atom, subst)
    else:
        # Recurse: each arg may itself be a functor like F0(X)
        new_args = [apply_subst(a, subst) for a in args]
        new_atom = f"{name}({', '.join(new_args)})"
    return ('NOT ' + new_atom) if negated else new_atom


def apply_subst_to_clause(clause: frozenset, subst: dict) -> frozenset:
    return frozenset(apply_subst_to_literal(lit, subst) for lit in clause)


def occurs_check(var: str, term: str, subst: dict) -> bool:
    term = apply_subst(term, subst)
    if var == term:
        return True
    _, args = parse_predicate(term)
    return any(occurs_check(var, a, subst) for a in args)


def unify_terms(t1: str, t2: str, subst: dict) -> dict | None:
    t1 = apply_subst(t1, subst)
    t2 = apply_subst(t2, subst)
    if t1 == t2:
        return subst
    if is_variable(t1):
        if occurs_check(t1, t2, subst):
            return None
        s = dict(subst)
        s[t1] = t2
        return s
    if is_variable(t2):
        if occurs_check(t2, t1, subst):
            return None
        s = dict(subst)
        s[t2] = t1
        return s
    # Both compound
    n1, a1 = parse_predicate(t1)
    n2, a2 = parse_predicate(t2)
    if n1 != n2 or len(a1) != len(a2):
        return None
    for x, y in zip(a1, a2):
        subst = unify_terms(x, y, subst)
        if subst is None:
            return None
    return subst


def unify_atoms(atom1: str, atom2: str) -> dict | None:
    """Try to unify two atom strings (no NOT prefix). Returns substitution or None."""
    n1, a1 = parse_predicate(atom1)
    n2, a2 = parse_predicate(atom2)
    if n1 != n2 or len(a1) != len(a2):
        return None
    subst = {}
    for x, y in zip(a1, a2):
        subst = unify_terms(x, y, subst)
        if subst is None:
            return None
    return subst


def negate_literal(lit: str) -> str:
    if lit.startswith('NOT '):
        return lit[4:]
    return 'NOT ' + lit


# ══════════════════════════════════════════════════════════════
#  VARIABLE RENAMING  (prevent clashes between clauses)
# ══════════════════════════════════════════════════════════════


def canonicalize_clause(clause: frozenset) -> frozenset:
    """
    Rename all variables in a clause to canonical names v0, v1, v2...
    in the order they first appear (left-to-right across sorted literals).
    This lets us detect logically duplicate clauses regardless of renaming history.
    """
    mapping = {}
    counter = [0]

    def canon_term(t: str) -> str:
        base = re.sub(r'(_r\d+)+$', '', t)   # strip all _rN suffixes
        if is_variable(t):                        # it is a variable
            if t not in mapping:
                mapping[t] = f'v{counter[0]}'
                counter[0] += 1
            return mapping[t]
        # compound functor: recurse into args
        name, args = parse_predicate(t)
        if args:
            new_args = [canon_term(a) for a in args]
            return f"{name}({', '.join(new_args)})"
        return t   # ground constant

    def canon_lit(lit: str) -> str:
        negated = lit.startswith('NOT ')
        atom = lit[4:] if negated else lit
        name, args = parse_predicate(atom)
        if args:
            new_args = [canon_term(a) for a in args]
            new_atom = f"{name}({', '.join(new_args)})"
        else:
            new_atom = canon_term(atom)
        return ('NOT ' + new_atom) if negated else new_atom

    # Process literals in sorted order for determinism
    new_lits = frozenset(canon_lit(lit) for lit in clause)
    return new_lits

_rename_counter = [0]

def collect_vars_in_term(term: str, out: set):
    """Recursively collect all variable names inside a term (including functor args)."""
    if is_variable(term):
        out.add(term)
    name, args = parse_predicate(term)
    for a in args:
        collect_vars_in_term(a, out)


def rename_vars(clause: frozenset) -> frozenset:
    """Give all variables in a clause fresh names, including those inside functors."""
    vars_in_clause = set()
    for lit in clause:
        atom = lit[4:] if lit.startswith('NOT ') else lit
        name, args = parse_predicate(atom)
        for a in args:
            collect_vars_in_term(a, vars_in_clause)
    if not vars_in_clause:
        return clause
    _rename_counter[0] += 1
    tag = f"_r{_rename_counter[0]}"
    mapping = {v: v + tag for v in vars_in_clause}
    return apply_subst_to_clause(clause, mapping)


# ══════════════════════════════════════════════════════════════
#  RESOLUTION STEP
# ══════════════════════════════════════════════════════════════

def resolve_clauses(ci: frozenset, cj: frozenset):
    """
    Try all pairs of complementary literals (with unification).
    Yields (resolvent_frozenset, pivot_lit_from_ci, substitution).
    """
    ci = rename_vars(ci)
    cj = rename_vars(cj)

    for lit_i in ci:
        neg_i = negate_literal(lit_i)
        for lit_j in cj:
            # Check if lit_j unifies with ¬lit_i
            # Both must have the same polarity after flipping
            atom_i = lit_i[4:] if lit_i.startswith('NOT ') else lit_i
            atom_j = lit_j[4:] if lit_j.startswith('NOT ') else lit_j
            # They complement if one is NOT and the other isn't
            i_neg = lit_i.startswith('NOT ')
            j_neg = lit_j.startswith('NOT ')
            if i_neg == j_neg:
                continue  # same polarity — not complementary

            subst = unify_atoms(atom_i, atom_j)
            if subst is None:
                continue

            # Build resolvent
            rest_i = apply_subst_to_clause(ci - {lit_i}, subst)
            rest_j = apply_subst_to_clause(cj - {lit_j}, subst)
            resolvent = rest_i | rest_j

            # Skip tautologies
            taut = False
            for l in resolvent:
                if negate_literal(l) in resolvent:
                    taut = True
                    break
            if not taut:
                pivot_display = apply_subst_to_literal(lit_i, subst)
                yield resolvent, pivot_display, subst


# ══════════════════════════════════════════════════════════════
#  MAIN RESOLUTION LOOP  (breadth-first, set-of-support)
# ══════════════════════════════════════════════════════════════

def resolution_refutation(named_clauses):
    """
    named_clauses: list of (label_str, frozenset_of_literals)

    Returns (proved, proof_steps, all_clauses_db)
      proof_steps: ordered list of dicts for display
    """
    # Index-based clause database
    db_clauses = {}   # int → frozenset
    db_parents = {}   # int → (p1_int|None, p2_int|None, pivot_str|None, label_str|None)
    counter = [0]

    # canonical_db maps canonical frozenset -> index, for O(1) duplicate detection
    canonical_db = {}

    def add(clause, p1=None, p2=None, pivot=None, label=None):
        canon = canonicalize_clause(clause)
        if canon in canonical_db:
            return canonical_db[canon], False
        idx = counter[0]
        counter[0] += 1
        db_clauses[idx] = clause
        db_parents[idx] = (p1, p2, pivot, label)
        canonical_db[canon] = idx
        return idx, True

    for label, clause in named_clauses:
        add(clause, label=label)

    proved = False
    empty_idx = None
    visited = set()   # set of (ia, ib) pairs already resolved
    MAX_CLAUSES = 5_000

    # Saturation loop: keep going until no new clauses are added or empty clause found.
    # We use a worklist: whenever a new clause N is added, we pair it against ALL
    # existing clauses (0..N-1). This guarantees derived clauses get paired with
    # each other, not just with the initial set.
    worklist = list(db_clauses.keys())  # indices that need to be paired with others

    while worklist and not proved and len(db_clauses) < MAX_CLAUSES:
        # Take the next "new" clause index to pair against everything before it
        new_idx = worklist.pop(0)
        existing = [i for i in db_clauses if i != new_idx]

        for old_idx in existing:
            ia, ib = min(new_idx, old_idx), max(new_idx, old_idx)
            if (ia, ib) in visited:
                continue
            visited.add((ia, ib))

            for resolvent, pivot, _ in resolve_clauses(db_clauses[ia], db_clauses[ib]):
                idx, added = add(resolvent, p1=ia, p2=ib, pivot=pivot)
                if added:
                    worklist.append(idx)   # new clause: schedule it for future pairing
                if len(resolvent) == 0:
                    proved = True
                    empty_idx = idx
                    break
            if proved:
                break

    # ── Collect proof path ─────────────────────────────────
    proof_steps = []
    if proved and empty_idx is not None:
        seen = set()
        def collect(idx):
            if idx in seen:
                return
            seen.add(idx)
            p1, p2, _, _ = db_parents[idx]
            if p1 is not None:
                collect(p1)
            if p2 is not None:
                collect(p2)
            proof_steps.append(idx)
        collect(empty_idx)

    return proved, proof_steps, db_clauses, db_parents


# ══════════════════════════════════════════════════════════════
#  DISPLAY HELPERS
# ══════════════════════════════════════════════════════════════

def clause_str(c: frozenset) -> str:
    if not c:
        return '□'
    return ' OR '.join(sorted(c))

W = 68

def banner(title):
    print('═' * W)
    print(f'  {title}')
    print('═' * W)


def print_proof(proved, proof_steps, db_clauses, db_parents,
                n_initial, query_str, neg_query_str):

    print()
    banner('RESOLUTION PROOF BY REFUTATION')
    print()

    if not proved:
        print('  ✗  The query CANNOT be proven from the given clauses.')
        print('     (The KB + ¬Q is satisfiable — no contradiction found.)')
        print()
        return

    print('  ✓  The query IS provable.')
    print()
    print(f'  Goal    : {query_str}')
    print(f'  Negated : {neg_query_str}')
    print()

    # Build display numbers (1-based)
    display = {}
    step_num = n_initial + 1
    for idx in proof_steps:
        p1, p2, _, label = db_parents[idx]
        if label is not None:
            display[idx] = label            # original numbered label
        else:
            display[idx] = str(step_num)
            step_num += 1

    print(f"  {'#':>4}  {'Clause':<46}  {'Justification'}")
    print(f"  {'─'*4}  {'─'*46}  {'─'*18}")

    for idx in proof_steps:
        p1, p2, pivot, label = db_parents[idx]
        c = db_clauses[idx]
        num = display.get(idx, '?')
        clause_display = clause_str(c)
        if len(clause_display) > 46:
            clause_display = clause_display[:43] + '...'

        if label is not None:
            src = '(given)'
            if label.startswith('¬Q'):
                src = '(negation of Q)'
            print(f"  {num:>4}  {clause_display:<46}  {src}")
        else:
            n1 = display.get(p1, '?')
            n2 = display.get(p2, '?')
            just = f"Res([{n1}],[{n2}]) pivot: {pivot}"
            print(f"  {num:>4}  {clause_display:<46}  {just}")

    print()
    print('  Empty clause □ derived → contradiction → Q is VALID.  ∎')
    print()
    print('═' * W)


# ══════════════════════════════════════════════════════════════
#  ENTRY POINT
# ══════════════════════════════════════════════════════════════

def main():
    if len(sys.argv) < 2:
        print('Usage: python resolution_prover.py <CNF_file.txt>')
        print()
        print('Expected format (produced by main.py):')
        print('  1 Hombre(Marco)')
        print('  2 NOT Pompeyano(K0) OR Romano(K0)')
        print('  3 [[NOT A OR NOT B] OR NOT C] OR NOT D')
        print('  Q Odia(Marco,Cesar)')
        sys.exit(1)

    path = sys.argv[1]

    try:
        named_clauses, query_text = parse_file(path)
    except FileNotFoundError:
        print(f'Error: file "{path}" not found.')
        sys.exit(1)
    except (ValueError, ParseError) as e:
        print(f'Parse error: {e}')
        sys.exit(1)

    # ── Display KB ────────────────────────────────────────────
    print()
    banner('INPUT — KNOWLEDGE BASE IN CNF')
    print()
    for label, lits, raw in named_clauses:
        print(f"  [{label:>3}]  {raw}")
    print()
    print(f"  [  Q]  {query_text}")
    print()

    # ── Negate query ──────────────────────────────────────────
    # Query is a single (possibly compound) expression.
    # Parse it, get its literals (it must itself be a disjunction for FOL).
    try:
        q_ast = parse_clause_text(query_text)
        q_lits = ast_to_literals(q_ast)
    except ParseError as e:
        print(f'Could not parse query: {e}')
        sys.exit(1)

    # ¬(L1 ∨ L2 ∨ ...) = ¬L1 ∧ ¬L2 ∧ ...  → one unit clause per negated literal
    neg_unit_clauses = []
    for lit in sorted(q_lits):
        neg_unit_clauses.append(frozenset({negate_literal(lit)}))

    neg_display_parts = [clause_str(c) for c in neg_unit_clauses]
    neg_query_str = '  AND  '.join(neg_display_parts)

    # ── Build full clause set ─────────────────────────────────
    all_clauses = [(lbl, lits) for lbl, lits, _ in named_clauses]
    for i, nc in enumerate(neg_unit_clauses, start=1):
        all_clauses.append((f'¬Q{i}', nc))

    n_initial = len(all_clauses)

    # ── Run resolution ────────────────────────────────────────
    proved, proof_steps, db_clauses, db_parents = resolution_refutation(all_clauses)

    # ── Print proof ───────────────────────────────────────────
    print_proof(proved, proof_steps, db_clauses, db_parents,
                n_initial, query_text, neg_query_str)


if __name__ == '__main__':
    main()
