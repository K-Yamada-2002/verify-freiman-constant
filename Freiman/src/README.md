# Compatibility paths

The actual computational sources have moved to:

- [verify/](../verify/README.md): fixed-table and proof verification.
- [search/](../search/README.md): input generation and discovery.
- [common/](../common/README.md): shared arithmetic and helpers.
- [history/](../history/README.md): retained earlier constructions and experiments.

Files here are relative symbolic links, except for the original `layout.py`
path resolver. They preserve flat Python imports, old commands, and paths in
hash manifests. The moved sources have unchanged contents. Edit their actual
files in the role directories. Do not make a second copy here.

Old commands continue to work. To run sources at their new paths, use the
repository-root `run.py`; see [CODE.md](../../CODE.md).
