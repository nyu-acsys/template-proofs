import re
import sys

def analyze_coq_file(file_path):
    try:
        with open(file_path, 'r') as file:
            content = file.read()
    except FileNotFoundError:
        print(f"Error: File '{file_path}' not found.")
        return

    # Remove comments from the content
    content = re.sub(r'\(\*.*?\*\)', '', content, flags=re.DOTALL)

    # Patterns for specs/proofs
    spec_pattern = (
      r'\b(Definition|'
      r'Fixpoint|'
      r'Inductive|'
      r'Record|'
      r'CoInductive|'
      r'Lemma|'
      r'Theorem|'
      r'Obligation|'
      r'Next Obligation|'
      r'Class|'
      r'Import|'
      r'Export|'
      r'Context|'
      r'Notation|'
      r'Parameter|'
      r'Hypothesis|'
      r'Section|'
      r'Instance)\b'
    )
    proof_pattern = r'Proof\.(.*?)Qed\.'

    # Count definitions and lemmas
    specs = re.findall(spec_pattern, content)

    # Count proof steps
    proofs = re.findall(proof_pattern, content, re.DOTALL)
    proof_steps = sum(proof.count('.') + proof.count(';') for proof in proofs)

    # Print results
    print(f"File: {file_path}")
    print(f"Spec Instructions: {len(specs)}")
    print(f"Proof Instructions: {proof_steps}")

if __name__ == "__main__":
    # Ensure the script is run with a file argument
    if len(sys.argv) != 2:
        print("Usage: python3 coqwc.py <file_name.v>")
    else:
        file_path = sys.argv[1]
        analyze_coq_file(file_path)
