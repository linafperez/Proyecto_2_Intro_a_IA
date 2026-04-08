## ESTE ARCHIVO IMPLEMENTA UN PROVER DE RESOLUCIÓN PARA FOL, USANDO LAS CLÁUSULAS CNF PRODUCIDAS POR fol_to_cnf.py. ##

import sys
import re

from cnf_utils  import parse_cnf_file, clause_str, tree_to_literals
from fol_to_cnf import get_cnf_clauses
from BinaryTree import BinaryTree




def _is_cnf_file(path: str) -> bool:

    if path.endswith("_CNF.txt"):
        return True
    fol_keywords = {"->", "<->", "FORALL", "EXISTS"}
    with open(path, "r", encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            parts = line.split(maxsplit=1)
            if len(parts) == 2 and parts[0].isdigit():
                return not any(kw in parts[1] for kw in fol_keywords)
    return True


def load_problem(path: str):

    if _is_cnf_file(path):
        return parse_cnf_file(path)
    else:
        # Raw FOL: convert in-memory, no intermediate file written
        clauses_no_raw, query_text = get_cnf_clauses(path)
        clauses = [(lbl, lits, clause_str(lits)) for lbl, lits in clauses_no_raw]
        return clauses, query_text




def _split_args(s: str) -> list:
  
    args, depth, current = [], 0, []
    for ch in s:
        if ch == "(":
            depth += 1; current.append(ch)
        elif ch == ")":
            depth -= 1; current.append(ch)
        elif ch == "," and depth == 0:
            args.append("".join(current).strip()); current = []
        else:
            current.append(ch)
    if current:
        args.append("".join(current).strip())
    return [a for a in args if a]


def _parse_predicate(atom: str):

    atom = atom.strip()
    m = re.match(r"^([A-Za-z_]\w*)\((.+)\)$", atom)
    if m:
        return m.group(1), _split_args(m.group(2))
    return atom, []

##ALGORITMO DE UNIFICACIÓN, RENOMBRADO DE VARIABLES, Y RESOLUCIÓN DE CLÁUSULAS##                

def is_variable(s: str) -> bool:

    if not s:
        return False
    base = re.sub(r"(_r\d+)+$", "", s)          # strip all _rN renaming suffixes
    if re.fullmatch(r"[A-Z]",  base): return True  # single uppercase letter
    if re.fullmatch(r"K\d+",   base): return True  # Skolem constant
    if base and base[0].islower():    return True   # lowercase variable
    return False


def _apply_subst(term: str, subst: dict) -> str:

    seen, t = set(), term
    while t in subst and t not in seen:
        seen.add(t); t = subst[t]
    if t != term:
        return t
    name, args = _parse_predicate(term)
    if args:
        return f"{name}({', '.join(_apply_subst(a, subst) for a in args)})"
    return term


def _apply_subst_to_literal(lit: str, subst: dict) -> str:
  
    if not subst:
        return lit
    negated = lit.startswith("NOT ")
    atom    = lit[4:] if negated else lit
    name, args = _parse_predicate(atom)
    new_atom = (f"{name}({', '.join(_apply_subst(a, subst) for a in args)})"
                if args else _apply_subst(atom, subst))
    return ("NOT " + new_atom) if negated else new_atom


def _apply_subst_to_clause(clause: frozenset, subst: dict) -> frozenset:
    return frozenset(_apply_subst_to_literal(lit, subst) for lit in clause)


def _occurs_check(var: str, term: str, subst: dict) -> bool:
    term = _apply_subst(term, subst)
    if var == term:
        return True
    _, args = _parse_predicate(term)
    return any(_occurs_check(var, a, subst) for a in args)


def _unify_terms(t1: str, t2: str, subst: dict):
    t1 = _apply_subst(t1, subst)
    t2 = _apply_subst(t2, subst)
    if t1 == t2:
        return subst
    if is_variable(t1):
        if _occurs_check(t1, t2, subst): return None
        return {**subst, t1: t2}
    if is_variable(t2):
        if _occurs_check(t2, t1, subst): return None
        return {**subst, t2: t1}
    n1, a1 = _parse_predicate(t1)
    n2, a2 = _parse_predicate(t2)
    if n1 != n2 or len(a1) != len(a2):
        return None
    for x, y in zip(a1, a2):
        subst = _unify_terms(x, y, subst)
        if subst is None: return None
    return subst


def _unify_atoms(atom1: str, atom2: str):
    n1, a1 = _parse_predicate(atom1)
    n2, a2 = _parse_predicate(atom2)
    if n1 != n2 or len(a1) != len(a2):
        return None
    subst = {}
    for x, y in zip(a1, a2):
        subst = _unify_terms(x, y, subst)
        if subst is None: return None
    return subst


def _negate_literal(lit: str) -> str:
    return lit[4:] if lit.startswith("NOT ") else "NOT " + lit




_rename_counter = [0]


def _collect_vars(term: str, out: set):
    """Recursively collect variable names from a term (including functor args)."""
    if is_variable(term):
        out.add(term)
    _, args = _parse_predicate(term)
    for a in args:
        _collect_vars(a, out)


def _rename_vars(clause: frozenset) -> frozenset:
    
    vars_found = set()
    for lit in clause:
        atom = lit[4:] if lit.startswith("NOT ") else lit
        _, args = _parse_predicate(atom)
        for a in args:
            _collect_vars(a, vars_found)
    if not vars_found:
        return clause
    _rename_counter[0] += 1
    tag     = f"_r{_rename_counter[0]}"
    mapping = {v: v + tag for v in vars_found}
    return _apply_subst_to_clause(clause, mapping)


def _canonicalize_clause(clause: frozenset) -> frozenset:
 
    mapping, counter = {}, [0]

    def canon_term(t):
        if is_variable(t):
            if t not in mapping:
                mapping[t] = f"v{counter[0]}"; counter[0] += 1
            return mapping[t]
        name, args = _parse_predicate(t)
        if args:
            return f"{name}({', '.join(canon_term(a) for a in args)})"
        return t

    def canon_lit(lit):
        negated = lit.startswith("NOT ")
        atom    = lit[4:] if negated else lit
        name, args = _parse_predicate(atom)
        new_atom = (f"{name}({', '.join(canon_term(a) for a in args)})"
                    if args else canon_term(atom))
        return ("NOT " + new_atom) if negated else new_atom

    return frozenset(canon_lit(lit) for lit in clause)




def _resolve_clauses(ci: frozenset, cj: frozenset):

    ci = _rename_vars(ci)
    cj = _rename_vars(cj)

    for lit_i in ci:
        i_neg  = lit_i.startswith("NOT ")
        atom_i = lit_i[4:] if i_neg else lit_i

        for lit_j in cj:
            j_neg  = lit_j.startswith("NOT ")
            atom_j = lit_j[4:] if j_neg else lit_j

            if i_neg == j_neg:
                continue  # same polarity — not complementary

            subst = _unify_atoms(atom_i, atom_j)
            if subst is None:
                continue

            rest_i    = _apply_subst_to_clause(ci - {lit_i}, subst)
            rest_j    = _apply_subst_to_clause(cj - {lit_j}, subst)
            resolvent = rest_i | rest_j

            # Skip tautologies
            if any(_negate_literal(l) in resolvent for l in resolvent):
                continue

            yield resolvent, _apply_subst_to_literal(lit_i, subst), subst




def resolution_refutation(named_clauses):

    db_clauses   = {}   
    db_parents   = {}   
    canonical_db = {}   
    counter      = [0]

    def add(clause, p1=None, p2=None, pivot=None, label=None):
        canon = _canonicalize_clause(clause)
        if canon in canonical_db:
            return canonical_db[canon], False
        idx = counter[0]; counter[0] += 1
        db_clauses[idx]     = clause
        db_parents[idx]     = (p1, p2, pivot, label)
        canonical_db[canon] = idx
        return idx, True

    for label, clause in named_clauses:
        add(clause, label=label)

    proved    = False
    empty_idx = None
    visited   = set()
    MAX_CLAUSES = 5_000

    worklist = list(db_clauses.keys())

    while worklist and not proved and len(db_clauses) < MAX_CLAUSES:
        new_idx  = worklist.pop(0)
        existing = [i for i in db_clauses if i != new_idx]

        for old_idx in existing:
            ia, ib = min(new_idx, old_idx), max(new_idx, old_idx)
            if (ia, ib) in visited:
                continue
            visited.add((ia, ib))

            for resolvent, pivot, _ in _resolve_clauses(db_clauses[ia], db_clauses[ib]):
                idx, added = add(resolvent, p1=ia, p2=ib, pivot=pivot)
                if added:
                    worklist.append(idx)
                if len(resolvent) == 0:
                    proved    = True
                    empty_idx = idx
                    break
            if proved:
                break

    
    proof_steps = []
    if proved and empty_idx is not None:
        seen = set()
        def collect(idx):
            if idx in seen: return
            seen.add(idx)
            p1, p2, _, _ = db_parents[idx]
            if p1 is not None: collect(p1)
            if p2 is not None: collect(p2)
            proof_steps.append(idx)
        collect(empty_idx)

    return proved, proof_steps, db_clauses, db_parents




W = 68

def _banner(title):
    print("═" * W)
    print(f"  {title}")
    print("═" * W)


def print_proof(proved, proof_steps, db_clauses, db_parents,
                n_initial, query_str, neg_query_str):

    print()
    _banner("RESOLUTION PROOF BY REFUTATION")
    print()

    if not proved:
        print("  ✗  The query CANNOT be proven from the given clauses.")
        print("     (The KB + ¬Q is satisfiable — no contradiction found.)")
        print()
        return

    print("  ✓  The query IS provable.")
    print()
    print(f"  Goal    : {query_str}")
    print(f"  Negated : {neg_query_str}")
    print()

    display  = {}
    step_num = n_initial + 1
    for idx in proof_steps:
        _, _, _, label = db_parents[idx]
        display[idx] = label if label is not None else str(step_num)
        if label is None: step_num += 1

    print(f"  {'#':>4}  {'Clause':<46}  Justification")
    print(f"  {'─'*4}  {'─'*46}  {'─'*18}")

    for idx in proof_steps:
        p1, p2, pivot, label = db_parents[idx]
        c   = db_clauses[idx]
        num = display.get(idx, "?")
        cd  = clause_str(c)
        if len(cd) > 46: cd = cd[:43] + "..."

        if label is not None:
            src = "(negation of Q)" if label.startswith("¬Q") else "(given)"
            print(f"  {num:>4}  {cd:<46}  {src}")
        else:
            n1   = display.get(p1, "?")
            n2   = display.get(p2, "?")
            just = f"Res([{n1}],[{n2}]) pivot: {pivot}"
            print(f"  {num:>4}  {cd:<46}  {just}")

    print()
    print("  Empty clause □ derived → contradiction → Q is VALID.  ∎")
    print()
    print("═" * W)




def main():
    if len(sys.argv) < 2:
        print("Usage: python resolution_prover.py <file.txt>")
        print("  Accepts a pre-converted *_CNF.txt or a raw FOL file.")
        sys.exit(1)

    path = sys.argv[1]

    try:
        named_clauses, query_text = load_problem(path)
    except FileNotFoundError:
        print(f'Error: file "{path}" not found.')
        sys.exit(1)
    except ValueError as e:
        print(f"Parse error: {e}")
        sys.exit(1)

    # Display KB
    print()
    _banner("INPUT — KNOWLEDGE BASE IN CNF")
    print()
    for label, lits, raw in named_clauses:
        print(f"  [{label:>3}]  {raw}")
    print()
    print(f"  [  Q]  {query_text}")
    print()

    # Negate the query: ¬(L1 ∨ L2 ∨ ...) = ¬L1 ∧ ¬L2 ∧ ...
    q_tree    = BinaryTree.build_expression_tree(query_text)
    q_lits    = tree_to_literals(q_tree)
    neg_units = [frozenset({_negate_literal(lit)}) for lit in sorted(q_lits)]
    neg_query_str = "  AND  ".join(clause_str(c) for c in neg_units)

    # Build full clause set (KB + negated query)
    all_clauses = [(lbl, lits) for lbl, lits, _ in named_clauses]
    for i, nc in enumerate(neg_units, start=1):
        all_clauses.append((f"¬Q{i}", nc))

    n_initial = len(all_clauses)

    # Run resolution
    proved, proof_steps, db_clauses, db_parents = resolution_refutation(all_clauses)

    print_proof(proved, proof_steps, db_clauses, db_parents,
                n_initial, query_text, neg_query_str)


if __name__ == "__main__":
    main()
