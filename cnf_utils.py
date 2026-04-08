
##este archivo contiene utilidades para convertir entre la representación de árboles binarios y 
# la representación de fórmulas lógicas en CNF, así como funciones para leer y escribir archivos de CNF con formato específico.

import re
from BinaryTreeNode import BinaryTreeNode



def tree_to_infix(node, is_root=True) -> str:

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

    elif "()" in data:                          
        name = data.replace("()", "")
        args = []
        if node.left_child:
            args.append(tree_to_infix(node.left_child,  False))
        if node.right_child:
            args.append(tree_to_infix(node.right_child, False))
        return f"{name}({', '.join(args)})"

    else:                                       
        return data




def tree_to_literals(node) -> frozenset:

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



def clause_str(clause: frozenset) -> str:
    """Pretty-print a clause frozenset as 'Lit1 OR Lit2 OR ...'."""
    if not clause:
        return "□"
    return " OR ".join(sorted(clause))




def _parse_cnf_line(content: str) -> frozenset:

    from BinaryTree import BinaryTree   # local import to avoid circular deps

    tree_root = BinaryTree.build_expression_tree(content)
    return tree_to_literals(tree_root)


def parse_cnf_file(path: str):

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

    with open(output_path, "w", encoding="utf-8") as f:
        for i, tree in enumerate(cnf_trees, start=1):
            f.write(f"{i} {tree_to_infix(tree)}\n")
        f.write(f"Q {query}\n")
