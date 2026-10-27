"""Regression checks kept separate from normal certificate verification."""
import copy
import json
import subprocess
import tempfile
import unittest
from fractions import Fraction as Q
from pathlib import Path
from unittest.mock import patch

import audit
import proof
import verify

HERE = Path(__file__).resolve().parent
DATA = HERE / 'certificates'


class InputAuditTests(unittest.TestCase):
    def test_corrupted_inputs_are_rejected(self):
        for name in ('original', 'table'):
            meta = json.loads((DATA / (name + '.meta.json')).read_text())
            audit.RAD = meta['radicand']
            data = audit.parse_input(DATA / (name + '.dat'))
            for corruption in ('alias', 'constant', 'endpoint'):
                with self.subTest(table=name, corruption=corruption):
                    damaged = copy.deepcopy(data)
                    record = damaged['sides'][0]['extensions'][0]
                    if corruption == 'alias':
                        record['endpoints'][1] = record['endpoints'][0]
                    elif corruption == 'constant':
                        record = next(r for s in damaged['sides'] for r in s['extensions']
                                      if r and not r['constant'])
                        record['constant'] = 1
                    else:
                        damaged['sides'][0]['tails'][0] = (Q(0), Q(0))
                    with self.assertRaises(AssertionError):
                        audit.audit(damaged, meta)

    def test_inconsistent_metadata_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            work = Path(directory)
            for suffix in ('.dat', '.alive.bin'):
                (work / ('table' + suffix)).symlink_to(DATA / ('table' + suffix))
            meta = json.loads((DATA / 'table.meta.json').read_text())
            meta['bands'][0] = ['0', '1/2']
            (work / 'table.meta.json').write_text(json.dumps(meta))
            with self.assertRaisesRegex(ValueError, 'Regenerated metadata differs'):
                verify.verify_table(work, 'table', None, None, work)


class IntervalTests(unittest.TestCase):
    def test_wrong_root_bins_are_rejected(self):
        certificate = json.loads((DATA / 'roots.json').read_text())
        for name in ('original', 'table'):
            table = proof.Table(DATA, name)
            groups = ['rows', 'paper_rows'] if name == 'original' else ['rows']
            for group in groups:
                with self.subTest(table=name, group=group):
                    row = certificate[name][group][0]
                    table.check_row(row)
                    with self.assertRaises(AssertionError):
                        table.check_row(dict(row, bin=row['bin'] + 1))

    def test_incompatible_past_is_rejected(self):
        certificate = json.loads((DATA / 'roots.json').read_text())
        original_cf = proof.RationalBounds.cf
        for name in ('original', 'table'):
            forbidden = [tuple(map(int, word))
                         for word in certificate[name]['language'].split(',')]
            for row in certificate[name]['rows']:
                a, b = tuple(map(int, row['a'])), tuple(map(int, row['b']))
                try:
                    proof.compatible_past(a, b, row['center'], forbidden)
                except AssertionError:
                    continue
                prefix = a[::-1] + (row['center'],) + b

                def damaged_cf(bounds, word, tail):
                    return Q(2) if word == prefix else original_cf(bounds, word, tail)

                with self.subTest(table=name), \
                     patch.object(proof.RationalBounds, 'cf', damaged_cf), \
                     self.assertRaises(AssertionError):
                    proof.compatible_past(a, b, row['center'], forbidden)
                break
            else:
                self.fail('No compatible-past example: ' + name)


class KernelTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory()
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.work = Path(cls.temporary.name)
        for source in ('kernel', 'audit'):
            verify.run(['c++', '-O3', '-std=c++17', '-pthread', HERE / (source + '.cpp'),
                        '-o', cls.work / source])

    def test_fixed_table_success_and_failure(self):
        # A minimal numeric fixture isolates the coverage check from input semantics.
        unit = 1 << 48
        transition = f'0 0 1 {unit} {unit} 0 {unit} 0 {unit} 0 1'
        bits = self.work / 'alive.bin'
        bits.write_bytes(b'\x01')
        for closed in (True, False):
            text = '\n'.join([
                'FREIMAN_DYADIC_GRAPH_V1 1 2 0 0 1 1 0',
                f'0 {unit}', '0 1 0', f'{unit} {unit}', f'{2*unit} {2*unit}',
                f'{unit} {unit}', '0 0 0 0 2', '0 0', f'{unit} {unit}',
                transition, transition if closed else '-1',
            ]) + '\n'
            input_path = self.work / 'input.dat'
            input_path.write_text(text)
            for source in ('kernel', 'audit'):
                with self.subTest(closed=closed, verifier=source):
                    command = [self.work / source, input_path]
                    if source == 'kernel':
                        command.append(self.work / 'result.json')
                    command.append(bits)
                    result = subprocess.run(list(map(str, command)), capture_output=True, text=True)
                    self.assertEqual(result.returncode, 0 if closed else 1, result.stderr)
                    if closed:
                        report = json.loads((self.work / 'result.json').read_text()) if source == 'kernel' \
                            else json.loads(result.stdout.splitlines()[-1])
                        self.assertTrue(report['closed_family_found'] if source == 'kernel' else report['passed'])
                    else:
                        self.assertIn('not closed' if source == 'kernel' else 'uncovered adopted row', result.stderr)

    def test_subprocess_failure_is_propagated(self):
        with self.assertRaisesRegex(RuntimeError, 'Command failed'):
            verify.run([self.work / 'kernel'])


if __name__ == '__main__':
    unittest.main()
