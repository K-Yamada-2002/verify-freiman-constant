"""Run a Python source in the role-based layout with its project's imports.

Example: python3 -B -S run.py Freiman/verify/verify_unified_proof.py --full
The working directory is left unchanged. Existing src/ commands also work.
"""
import argparse
import runpy
import sys
from pathlib import Path


def main():
    root = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', help='Repository-relative Python source path')
    parser.add_argument('arguments', nargs=argparse.REMAINDER,
                        help='Arguments passed unchanged to the source')
    args = parser.parse_args()
    source = (root / args.source).resolve()
    if not source.is_relative_to(root):
        parser.error('Source must be inside this repository')
    relative = source.relative_to(root)
    if (len(relative.parts) < 3 or relative.parts[0] not in ('Freiman', 'Berstein')
            or source.suffix != '.py' or not source.is_file()):
        parser.error('Choose a Python source under Freiman/ or Berstein/')
    # Preserve the existing flat import names, including the distinct
    # exact_cf modules in the two projects. Sources themselves stay unchanged.
    sys.path.insert(0, str(source.parent))
    sys.path.insert(0, str(root / relative.parts[0] / 'src'))
    sys.argv = [str(source), *args.arguments]
    runpy.run_path(str(source), run_name='__main__')


if __name__ == '__main__':
    main()
