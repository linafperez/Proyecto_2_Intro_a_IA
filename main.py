import sys
from BinaryTree import BinaryTree

# Ensure that an input file is provided as a command-line argument
if len(sys.argv) < 2:
    print("Usage:", sys.argv[0], "input_file")
    sys.exit()

input_filename = sys.argv[1]

# Read the input file containing a knowledge base in first-order logic
try:
    with open(input_filename, "r") as reader:
        lines = reader.readlines()
except FileNotFoundError:
    print("File was not found")
    sys.exit()

"""
Expected input file format:

1 <rule>
2 <rule>
...
Q <query>
"""

rules = []
query = None

for line in lines:
    # Remove leading and trailing whitespace
    line = line.strip()

    # Split into identifier and content
    parts = line.split(maxsplit=1)

    identifier, content = parts

    # Save the query
    if identifier == "Q":
        query = content

    # Process each rule
    elif identifier.isdigit():
        expression_tree = BinaryTree.build_expression_tree(content)
        rules.append(expression_tree)
