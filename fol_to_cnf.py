
##ESTE ARCHIVO SE ENCARGA DE TRANSFORMAR LAS REGLAS DE FOL A CNF, PARA QUE EL PROVER PUEDA USARLAS.##

import sys
from BinaryTree     import BinaryTree
from BinaryTreeNode import BinaryTreeNode
from cnf_utils      import extract_clauses, write_cnf_file, tree_to_literals




def _copy_tree(node):
    """Deep-copy a BinaryTreeNode subtree."""
    if node is None:
        return None
    new_node = BinaryTreeNode(node.data)
    new_node.set_left_child(_copy_tree(node.left_child))
    new_node.set_right_child(_copy_tree(node.right_child))
    return new_node



def del_biconditional(node):
  
    if node is None:
        return None
    node.set_left_child(del_biconditional(node.left_child))
    node.set_right_child(del_biconditional(node.right_child))

    if node.data == "<->":
        alpha, beta = node.left_child, node.right_child

        left_impl = BinaryTreeNode("->")
        left_impl.set_left_child(_copy_tree(alpha))
        left_impl.set_right_child(_copy_tree(beta))

        right_impl = BinaryTreeNode("->")
        right_impl.set_left_child(_copy_tree(beta))
        right_impl.set_right_child(_copy_tree(alpha))

        new_node = BinaryTreeNode("AND")
        new_node.set_left_child(left_impl)
        new_node.set_right_child(right_impl)
        return new_node

    return node


def del_implication(node):
  
    if node is None:
        return None
    node.set_left_child(del_implication(node.left_child))
    node.set_right_child(del_implication(node.right_child))

    if node.data == "->":
        alpha, beta = node.left_child, node.right_child

        not_alpha = BinaryTreeNode("NOT")
        not_alpha.set_left_child(_copy_tree(alpha))

        new_node = BinaryTreeNode("OR")
        new_node.set_left_child(not_alpha)
        new_node.set_right_child(_copy_tree(beta))
        return new_node

    return node


def apply_negation(node):
   
    if node is None:
        return None

    node.set_left_child(apply_negation(node.left_child))
    node.set_right_child(apply_negation(node.right_child))

    if node.data == "NOT":
        child = node.left_child
        if child is None:
            return node

        # ¬(¬α) → α
        if child.data == "NOT":
            return apply_negation(child.left_child)

        # ¬(α AND β) → (¬α OR ¬β)
        if child.data == "AND":
            new_node = BinaryTreeNode("OR")
            left_not  = BinaryTreeNode("NOT"); left_not.set_left_child(_copy_tree(child.left_child))
            right_not = BinaryTreeNode("NOT"); right_not.set_left_child(_copy_tree(child.right_child))
            new_node.set_left_child(apply_negation(left_not))
            new_node.set_right_child(apply_negation(right_not))
            return new_node

        # ¬(α OR β) → (¬α AND ¬β)
        if child.data == "OR":
            new_node = BinaryTreeNode("AND")
            left_not  = BinaryTreeNode("NOT"); left_not.set_left_child(_copy_tree(child.left_child))
            right_not = BinaryTreeNode("NOT"); right_not.set_left_child(_copy_tree(child.right_child))
            new_node.set_left_child(apply_negation(left_not))
            new_node.set_right_child(apply_negation(right_not))
            return new_node

        # ¬(FORALL X P) → EXISTS X ¬P
        if child.data == "FORALL":
            new_node = BinaryTreeNode("EXISTS")
            new_node.set_left_child(_copy_tree(child.left_child))
            not_formula = BinaryTreeNode("NOT")
            not_formula.set_left_child(_copy_tree(child.right_child))
            new_node.set_right_child(apply_negation(not_formula))
            return new_node

        # ¬(EXISTS X P) → FORALL X ¬P
        if child.data == "EXISTS":
            new_node = BinaryTreeNode("FORALL")
            new_node.set_left_child(_copy_tree(child.left_child))
            not_formula = BinaryTreeNode("NOT")
            not_formula.set_left_child(_copy_tree(child.right_child))
            new_node.set_right_child(apply_negation(not_formula))
            return new_node

    return node


def standardize_variables(node, mapping=None, used_vars=None):
    """Rename bound variables to avoid conflicts."""
    if node is None:
        return None
    if mapping   is None: mapping   = {}
    if used_vars is None: used_vars = set()

    if node.data in ("FORALL", "EXISTS"):
        old_var = node.left_child.data
        new_var = f"{old_var}_{len(used_vars)}" if old_var in used_vars else old_var

        used_vars_new  = used_vars | {new_var}
        mapping_new    = {**mapping, old_var: new_var}

        node.set_left_child(BinaryTreeNode(new_var))
        node.set_right_child(standardize_variables(node.right_child, mapping_new, used_vars_new))
        return node

    if node.left_child is None and node.right_child is None:
        return BinaryTreeNode(mapping[node.data]) if node.data in mapping else node

    node.set_left_child(standardize_variables(node.left_child,  mapping, used_vars))
    node.set_right_child(standardize_variables(node.right_child, mapping, used_vars))
    return node


def move_quantifiers_left(node):
   
    if node is None:
        return None

    node.set_left_child(move_quantifiers_left(node.left_child))
    node.set_right_child(move_quantifiers_left(node.right_child))

    if node.data in ("AND", "OR"):
        # Quantifier on the left child
        if node.left_child and node.left_child.data in ("FORALL", "EXISTS"):
            quant = node.left_child.data
            var   = node.left_child.left_child
            sub   = node.left_child.right_child

            new_node = BinaryTreeNode(quant)
            new_node.set_left_child(var)
            inner = BinaryTreeNode(node.data)
            inner.set_left_child(sub)
            inner.set_right_child(node.right_child)
            new_node.set_right_child(move_quantifiers_left(inner))
            return new_node

        # Quantifier on the right child
        if node.right_child and node.right_child.data in ("FORALL", "EXISTS"):
            quant = node.right_child.data
            var   = node.right_child.left_child
            sub   = node.right_child.right_child

            new_node = BinaryTreeNode(quant)
            new_node.set_left_child(var)
            inner = BinaryTreeNode(node.data)
            inner.set_left_child(node.left_child)
            inner.set_right_child(sub)
            new_node.set_right_child(move_quantifiers_left(inner))
            return new_node

    return node


def _build_skolem_term(name, args):
    node = BinaryTreeNode(f"{name}()")
    if len(args) >= 1: node.set_left_child(BinaryTreeNode(args[0]))
    if len(args) >= 2: node.set_right_child(BinaryTreeNode(args[1]))
    return node


def _replace_variable(node, var, value_node):
    if node is None:
        return None
    if node.left_child is None and node.right_child is None:
        return value_node if node.data == var else node
    node.set_left_child(_replace_variable(node.left_child,  var, value_node))
    node.set_right_child(_replace_variable(node.right_child, var, value_node))
    return node


_k_counter = [0]
_f_counter = [0]

def skolemize(node, universal_vars=None, counter=None):
    """Replace existential quantifiers with Skolem constants / functions."""
    if node is None:
        return None
    if universal_vars is None: universal_vars = []
    if counter        is None: counter        = [0]

    if node.data == "FORALL":
        var = node.left_child.data
        node.set_right_child(skolemize(node.right_child, universal_vars + [var], counter))
        return node

    if node.data == "EXISTS":
        var = node.left_child.data
        if not universal_vars:
            skolem_node = BinaryTreeNode(f"K{_k_counter[0]}")
            _k_counter[0] += 1
        else:
            name = f"F{_f_counter[0]}"
            skolem_node = _build_skolem_term(name, universal_vars)
            _f_counter[0] += 1
        counter[0] += 1
        replaced = _replace_variable(node.right_child, var, skolem_node)
        return skolemize(replaced, universal_vars, counter)

    node.set_left_child(skolemize(node.left_child,  universal_vars, counter))
    node.set_right_child(skolemize(node.right_child, universal_vars, counter))
    return node


def remove_universal_quantifiers(node):
    """Drop FORALL nodes — universal quantification becomes implicit."""
    if node is None:
        return None
    if node.data == "FORALL":
        return remove_universal_quantifiers(node.right_child)
    node.set_left_child(remove_universal_quantifiers(node.left_child))
    node.set_right_child(remove_universal_quantifiers(node.right_child))
    return node


def distribute_or_over_and(node):
    """Distribute OR over AND to reach CNF: (A∧B)∨C → (A∨C)∧(B∨C)."""
    if node is None:
        return None

    node.set_left_child(distribute_or_over_and(node.left_child))
    node.set_right_child(distribute_or_over_and(node.right_child))

    if node.data == "OR":
        left, right = node.left_child, node.right_child

        if left and left.data == "AND":
            A, B, C = left.left_child, left.right_child, right
            new_node = BinaryTreeNode("AND")
            lor = BinaryTreeNode("OR"); lor.set_left_child(_copy_tree(A)); lor.set_right_child(_copy_tree(C))
            ror = BinaryTreeNode("OR"); ror.set_left_child(_copy_tree(B)); ror.set_right_child(_copy_tree(C))
            new_node.set_left_child(distribute_or_over_and(lor))
            new_node.set_right_child(distribute_or_over_and(ror))
            return new_node

        if right and right.data == "AND":
            A, B, C = left, right.left_child, right.right_child
            new_node = BinaryTreeNode("AND")
            lor = BinaryTreeNode("OR"); lor.set_left_child(_copy_tree(A)); lor.set_right_child(_copy_tree(B))
            ror = BinaryTreeNode("OR"); ror.set_left_child(_copy_tree(A)); ror.set_right_child(_copy_tree(C))
            new_node.set_left_child(distribute_or_over_and(lor))
            new_node.set_right_child(distribute_or_over_and(ror))
            return new_node

    return node




def fol_rule_to_cnf_trees(rule_tree) -> list:
    """
    Apply the full FOL → CNF pipeline to a single expression tree.
    Returns a list of CNF clause trees (BinaryTreeNode).
    """
    node = del_biconditional(rule_tree)
    node = del_implication(node)
    node = apply_negation(node)
    node = standardize_variables(node)
    node = move_quantifiers_left(node)
    node = skolemize(node)
    node = remove_universal_quantifiers(node)
    node = distribute_or_over_and(node)
    return extract_clauses(node)


def get_cnf_clauses(input_path: str):
    """
    Read a FOL knowledge-base file and return clauses ready for the prover,
    WITHOUT writing an intermediate CNF file.

    Returns
    -------
    clauses    : list of (label, frozenset_of_literals)
                 label is the line number as a string ("1", "2", …)
    query_text : str  — raw query expression
    """
    # Reset Skolem counters so repeated calls are deterministic
    _k_counter[0] = 0
    _f_counter[0] = 0

    rules      = []
    query_text = None

    with open(input_path, "r", encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if not line:
                continue
            parts      = line.split(maxsplit=1)
            identifier = parts[0]
            content    = parts[1] if len(parts) > 1 else ""

            if identifier == "Q":
                query_text = content
            elif identifier.isdigit():
                rules.append((identifier, BinaryTree.build_expression_tree(content)))

    if query_text is None:
        raise ValueError(f"No query line (Q ...) found in '{input_path}'.")

    clauses = []
    for label, rule_tree in rules:
        for clause_tree in fol_rule_to_cnf_trees(rule_tree):
            lits = tree_to_literals(clause_tree)
            clauses.append((label, lits))

    return clauses, query_text




def main():
    if len(sys.argv) < 2:
        print("Usage: python fol_to_cnf.py input_file.txt")
        sys.exit(1)

    input_path = sys.argv[1]

    # Reset Skolem counters
    _k_counter[0] = 0
    _f_counter[0] = 0

    rules      = []
    query_text = None

    try:
        with open(input_path, "r") as fh:
            for line in fh:
                line = line.strip()
                if not line:
                    continue
                parts      = line.split(maxsplit=1)
                identifier = parts[0]
                content    = parts[1] if len(parts) > 1 else ""

                if identifier == "Q":
                    query_text = content
                elif identifier.isdigit():
                    rules.append(BinaryTree.build_expression_tree(content))
    except FileNotFoundError:
        print(f"File '{input_path}' was not found.")
        sys.exit(1)

    cnf_trees = []
    for rule_tree in rules:
        cnf_trees.extend(fol_rule_to_cnf_trees(rule_tree))

    output_path = input_path.split(".")[0] + "_CNF.txt"
    write_cnf_file(output_path, cnf_trees, query_text)
    print(f"CNF written to {output_path}")


if __name__ == "__main__":
    main()
