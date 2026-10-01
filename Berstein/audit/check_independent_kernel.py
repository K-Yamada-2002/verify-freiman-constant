"""Positive and adversarial controls for independent_kernel.cpp.

The tiny artificial certificates test verifier logic, not CF semantics.  All
temporary data are built here; no production certificates are modified.
"""
import argparse
import json
import subprocess
import tempfile
from pathlib import Path

D = 1 << 48


def make_input(pairs, states=1, child=0, bins=1, cross_bin=False):
    cuts = [7*D//8, 9*D//8] if bins == 1 else [7*D//8, D, 9*D//8]
    lines = [f'FREIMAN_DYADIC_GRAPH_V1 {states} 3 0 {bins-1} 1 {len(pairs)} 0',
             f'0 {D}']
    lines.extend(f'{a} {b} 0' for a, b in pairs)
    lines.extend(f'{v} {v}' for v in cuts)
    for state in range(states):
        lines.extend([f'{D} {D}', '0 0 0 0 4', '0 0', f'{D} {D}',
                      f'{3*D//8} {3*D//8}', f'{5*D//8} {5*D//8}'])
        lines.append(f'{state} 0 1 {D} {D} 0 0 {D} {D} 0 1')
        if cross_bin:
            # The two derivatives have ratio 21/20. One direction maps the
            # lower parent bin into both bins; the reverse does that for the
            # upper parent bin. Both child bands therefore must survive.
            for derivative in (5*D//8, 21*D//32):
                lines.append(f'{child} 0 0 {derivative} {derivative} 0 0 {D} {D} 0 1')
        else:
            lines.extend([
                f'{child} 0 2 {3*D//8} {3*D//8} 0 0 {3*D//8} {3*D//8} 0 2',
                f'{child} 0 2 {3*D//8} {3*D//8} {5*D//8} {5*D//8} {D} {D} 3 1'])
    return '\n'.join(lines) + '\n'


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('binary', type=Path)
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).with_name('independent_kernel_controls.json'))
    args = parser.parse_args()
    all_pairs = [(1, 1), (1, 2), (2, 1), (2, 2)]
    cases = [
        ('overlapping_cover', make_input(all_pairs), bytes([1]), True),
        ('middle_gap_and_false_reverse_overlap', make_input([(1, 1), (2, 2)]), bytes([1]), False),
        ('missing_right_endpoint', make_input([(1, 1), (1, 2)]), bytes([1]), False),
        ('missing_left_endpoint', make_input([(2, 1), (2, 2)]), bytes([1]), False),
        ('two_state_closed_cover', make_input(all_pairs, states=2, child=1), bytes([1, 1, 1, 1]), True),
        ('child_state_removed', make_input(all_pairs, states=2, child=1), bytes([1, 0, 0, 0]), False),
        ('two_bin_closed_cover', make_input([(1, 2), (2, 1)], bins=2, cross_bin=True), bytes([1, 1]), True),
        ('cross_bin_child_removed', make_input([(1, 2), (2, 1)], bins=2, cross_bin=True), bytes([1, 0]), False),
        ('truncated_final_endpoint', make_input(all_pairs).rsplit(' ', 1)[0], bytes([1]), None),
    ]
    reports = []
    with tempfile.TemporaryDirectory(prefix='independent-kernel-controls-') as directory:
        folder = Path(directory)
        for name, text, bits, expected in cases:
            source = folder / (name + '.dat')
            table = folder / (name + '.bin')
            source.write_text(text)
            table.write_bytes(bits)
            result = subprocess.run([str(args.binary.resolve()), str(source), str(table)],
                                    text=True, capture_output=True, check=False)
            expected_exit = 2 if expected is None else (0 if expected else 1)
            assert result.returncode == expected_exit, (name, result.returncode, result.stderr)
            report = json.loads(result.stdout.splitlines()[-1]) if result.stdout else None
            if expected is not None:
                assert report['passed'] == expected, name
            reports.append({'name': name, 'expected_accept': expected, 'exit_code': result.returncode,
                            'checker_result': report, 'diagnostic': result.stderr.strip()})
    summary = {'passed': True, 'case_count': len(cases), 'cases': reports,
               'one_way_overlap_explanation':
               'In the gap control at S=1, the children are [0,3/4] and [5/4,2]. '
               'The comparison 2>=0 passes, but 3/4>=5/4 fails. Omitting the second '
               'overlap inequality would wrongly connect endpoints of the parent [0,2].',
               'scope': 'Artificial certificates test coverage and recursive availability; not CF input semantics.'}
    args.output.write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps({'passed': True, 'case_count': len(cases), 'output': str(args.output)}))


if __name__ == '__main__':
    main()
