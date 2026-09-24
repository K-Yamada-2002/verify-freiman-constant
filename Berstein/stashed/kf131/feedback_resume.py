"""Import an open frontier as discovery hypotheses, never as a proof."""
from fractions import Fraction
import gzip
import hashlib
import json
from pathlib import Path


def write_frontier(source, target, cfg):
    raw = Path(source).read_bytes()
    decoded = gzip.decompress(raw) if raw.startswith(b'\x1f\x8b') else raw
    data = json.loads(decoded)
    if data.get('schema') != 'kf131-scalar-atlas-v1' or len(data['roots']) != 1:
        raise ValueError('resume requires a scalar atlas with one root')
    for old, new in [('base', 'base'), ('bins', 'bins'), ('grid', 'scalar_grid')]:
        if Fraction(str(data['settings'][old])) != Fraction(str(cfg[new])):
            raise ValueError('resume geometry differs: '+old)
    # Memory controls future suffix refinement. Every stored concrete shape
    # is checked below, so increasing this limit preserves its geometry.
    nodes = data['nodes']
    if len(nodes) > cfg['max_types']:
        raise ValueError('resume frontier exceeds type limit')
    for key, value in zip(('root_left', 'root_right'), data['root_prefixes']):
        if key in cfg and cfg[key] != value:
            raise ValueError('resume root prefix differs')
        cfg[key] = value
    alternatives = data.get('alternative_rules', [])
    version = 3 if alternatives else 2
    lines = [f'kf131-frontier-v{version} {len(nodes)} {data["roots"][0]}']
    def add_edges(edges):
        for edge in edges:
            u, v = edge['suffixes']
            if not 1 <= len(u)+len(v) <= cfg['max_step']:
                raise ValueError('resume rule exceeds maximum suffix length or is empty')
            lines.append(f'{json.dumps(u)} {json.dumps(v)} {len(edge["cases"])}')
            for case in edge['cases']:
                destinations = case['destinations']
                if not destinations or not all(type(j) is int and 0 <= j < len(nodes) for j in destinations):
                    raise ValueError('resume rule has missing dependencies')
                lines.append(f'{int(case["swap"])} {case["interval"][0]} '
                             f'{case["interval"][1]} {len(destinations)} '+
                             ' '.join(map(str, destinations)))
    for index, node in enumerate(nodes):
        if node['id'] != index:
            raise ValueError('resume requires consecutive node IDs')
        left, right = node['states']
        minimum = cfg['minimum_memory'] or cfg['memory']
        if not all(minimum <= len(w) <= cfg['memory'] for w in (left, right)):
            raise ValueError('resume shape is outside configured suffix lengths')
        edges = node['children'] if node['covered'] else []
        refinement = node.get('ratio_refinement', [0, 0])
        if (type(refinement) is not list or len(refinement) != 2
                or any(type(i) is not int for i in refinement)):
            raise ValueError('invalid ratio refinement')
        level, part = refinement
        if not 0 <= level <= cfg.get('ratio_depth', 0) or not 0 <= part < 2**level:
            raise ValueError('resume refinement exceeds ratio depth')
        lines.append(f'{json.dumps(left)} {json.dumps(right)} {node["parity"]} '
                     f'{node["ratio_bin"]} {level} {part} {node["interval"][0]} {node["interval"][1]} '
                     f'{int(node["covered"])} {len(edges)}')
        add_edges(edges)
    if alternatives:
        lines.append(str(len(alternatives)))
        for alternative in alternatives:
            parent, edges = alternative['parent'], alternative['children']
            if type(parent) is not int or not 0 <= parent < len(nodes) or not edges:
                raise ValueError('invalid alternative rule')
            lines.append(f'{parent} {len(edges)}')
            add_edges(edges)
    Path(target).write_text('\n'.join(lines)+'\n')
    return dict(source_sha256=hashlib.sha256(raw).hexdigest(),
                decoded_graph_sha256=hashlib.sha256(decoded).hexdigest(),
                imported_nodes=len(nodes), imported_rules=sum(n['covered'] for n in nodes),
                imported_alternatives=len(alternatives),
                status='provisional hypotheses; closure requires fresh exact verification')
