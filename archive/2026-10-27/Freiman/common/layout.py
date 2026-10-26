"""Filesystem layout shared by the command-line programs.

BASE in older modules denotes DATA. Bare --input/--output filenames are
relative to data/; absolute paths continue to work with pathlib joining.
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / 'data'
DOC = ROOT / 'doc'
LOGS = ROOT / 'logs'
BIN = ROOT / 'bin'


def source_path(filename):
    """Resolve a source basename in the four explicit package directories."""
    name = Path(filename)
    if name.name != str(name):
        raise ValueError('Source keys must be basenames')
    matches = [ROOT / directory / name for directory in ('verify', 'search', 'common', 'history')
               if (ROOT / directory / name).is_file()]
    if len(matches) != 1:
        raise ValueError(f'Expected exactly one source for {filename}: {matches}')
    return matches[0]


def artifact_path(filename):
    """Resolve the basename keys used in verification SHA-256 manifests."""
    name = Path(filename)
    if name.name != str(name):
        raise ValueError('Manifest keys must be basenames')
    return source_path(filename) if name.suffix in ('.py', '.cpp') else DATA / name
