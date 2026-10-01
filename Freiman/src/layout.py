"""Filesystem layout shared by the command-line programs.

BASE in older modules denotes DATA. Bare --input/--output filenames are
relative to data/; absolute paths continue to work with pathlib joining.
"""
from pathlib import Path

SRC = Path(__file__).resolve().parent
ROOT = SRC.parent
DATA = ROOT / 'data'
DOC = ROOT / 'doc'
LOGS = ROOT / 'logs'
BIN = ROOT / 'bin'


def artifact_path(filename):
    """Resolve the basename keys used in verification SHA-256 manifests."""
    name = Path(filename)
    if name.name != str(name):
        raise ValueError('Manifest keys must be basenames')
    directory = SRC if name.suffix in ('.py', '.cpp') else DATA
    return directory / name
