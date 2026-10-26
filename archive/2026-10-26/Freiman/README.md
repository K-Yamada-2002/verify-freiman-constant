# Dependencies of the preserved Berstein programs

`src/` is a byte-preserving snapshot of the original flat Freiman source modules.
The old Berstein programs need these exact sources and import names, including
the original path resolver and verifier hash manifests. `data/` preserves the original `graph_wide` inputs and their source-hash records
needed by those programs. `bin/` and `logs/` are local build outputs.

This is not the active Freiman source tree. See
[the main Freiman project](../../../Freiman/README.md) and the
[snapshot instructions](../README.md).
