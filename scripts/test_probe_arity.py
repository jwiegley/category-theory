"""Guard regression tests. Optional compiler tests pin eager-control semantics."""
from contextlib import contextmanager
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import probe_arity as guard


@contextmanager
def compiler_evidence(label):
    base = os.environ.get('PROBE_ARITY_TEST_EVIDENCE')
    if base:
        path = Path(base) / label
        path.mkdir(parents=True, exist_ok=False)
        yield str(path)
    else:
        with tempfile.TemporaryDirectory() as tmp:
            yield tmp


def save_result(file, command, result):
    file.with_suffix('.log').write_text('command: ' + repr(command) + '\n' +
        result.stdout + result.stderr + f'\nexit status: {result.returncode}\n')


def false_green_fixtures():
    """Compiler witnesses from review, with genuinely formable companions."""
    prefix = ('Set Universe Polymorphism.\n'
              'Polymorphic Definition F@{u +} (A : Type@{u}) := Type.\n')
    cases = []
    for name, comment, tail in (
            ('CommentPhantom', '(* "*) Check @F@{_ _ _}. (*" *)\n', ''),
            ('CommentHidden', '(* "(*" *)\n', '\n(* "*)" *)'),
            ('CommentPhantomDoubled', '(* "say ""*) Check @F@{_ _ _}. (*"" now" *)\n', ''),
            ('CommentHiddenDoubled', '(* "say ""(*"" now" *)\n', '\n(* "say ""*)"" now" *)')):
        bad = prefix + comment + 'Fail Check @F@{_ _ _}.' + tail
        good = prefix + 'Check @F@{_ _}.\n' + comment + 'Fail Check (@F@{_ _} : nat).' + tail
        cases.append((name, bad, good, 'F', 3, 2))
    notation = 'Notation "\'F\' @{ x y z }" := True (at level 0, x ident, y ident, z ident).\n'
    levels = 'Monomorphic Universe a b c.\n'
    cases.append(('NotationPhantom', prefix + notation + levels +
                  'Check F@{a b c}.\nFail Check @F@{a b c}.',
                  prefix + notation + levels +
                  'Check @F@{_ _}.\nFail Check (@F@{a b} : nat).', 'F', 3, 2))
    scoped = ('Set Universe Polymorphism.\n'
              'Polymorphic Definition F@{u v +} (A : Type@{u}) (B : Type@{v}) := Type.\n'
              'Polymorphic Definition G@{u +} (A : Type@{u}) := Type.\n'
              'Declare Scope s. Delimit Scope s with s.\n'
              'Notation "\'F\' @{ x y z }" := (G@{_ _ _}) '
              '(at level 0, x ident, y ident, z ident) : s.\n' + levels +
              'Check @F@{_ _ _}.\n')
    cases.append(('ScopedIdentity', scoped + 'Fail Check (F@{a b c})%s.',
                  scoped + 'Fail Check ((@F@{a b c})%s : nat).', 'G', 3, 2))
    for name, target, arity, old, declaration in (
            ('GeneratedRect', 'R_rect', 1,
             'Definition R_rect@{u v} (A : Type@{u}) (B : Type@{v}) := A.',
             'Inductive R : Set := r.'),
            ('GeneratedInd', 'R_ind', 0,
             'Definition R_ind@{u} (A : Type@{u}) := A.',
             'Inductive R : Set := r.'),
            ('GeneratedConstructor', 'Build_R', 0,
             'Definition Build_R@{u} (A : Type@{u}) := A.',
             'Record R : Set := { field : nat }.')):
        stale = ' '.join(['Set'] * (arity + 1))
        current = ' '.join(['Set'] * arity)
        common = ('Set Universe Polymorphism.\nModule Old.\n' + old +
                  '\nEnd Old. Import Old.\nCheck @' + target + '@{' + stale + '}.\n' + declaration + '\n')
        cases.append((name, common + 'Fail Check @' + target + '@{' + stale + '}.',
                      common + 'Check @' + target + '@{' + current + '}.\n' +
                      'Fail Check (@' + target + '@{' + current + '} : bool).',
                      target, arity + 1, arity))
    program = ('From Coq Require Import Program.\nSet Universe Polymorphism.\n'
               'Obligation Tactic := intros; reflexivity.\nSet Program Mode.\n'
               'Module Old.\nLemma hidden_obligation_1@{u} (A : Type@{u}) : A -> A.\n'
               'Proof. exact (fun x => x). Qed.\nEnd Old. Import Old.\n'
               'Check @hidden_obligation_1@{Set}.\n')
    for mode in ('', 'Program '):
        common = program + mode + 'Definition hidden (n : nat) : {m : nat | m = n} := n.\n'
        cases.append(('ProgramExplicit' if mode else 'ProgramMode',
                      common + 'Fail Check @hidden_obligation_1@{Set}.',
                      common + 'Check @hidden_obligation_1@{}.\n'
                      'Fail Check (@hidden_obligation_1@{} : bool).',
                      'hidden_obligation_1', 1, 0))
    return cases


class ScannerTests(unittest.TestCase):
    def assert_flags(self, text, names):
        self.assertEqual([(u.name, u.arity) for u in guard.scan(text)], names)

    def test_explicit_checks(self):
        for control in ('Check @F@{u v}.', 'Check @F@{_ _}.', 'Check ((@F@{_ _})).'):
            with self.subTest(control=control):
                self.assert_flags(control + '\nFail Check F@{x y}.', [])
                self.assert_flags('Fail Check F@{x y}.\n' + control, [])

    def test_missing_wrong_arity_and_wrong_name(self):
        for control in ('', 'Check @F@{_}.', 'Check @G@{_ _}.', 'Check @A.F@{_ _}.',
                        'Check F@{_ _}.'):
            with self.subTest(control=control):
                self.assert_flags(control + '\nFail Check F@{x y}.', [('F', 2)])

    def test_fail_does_not_control_fail(self):
        self.assert_flags('Fail Check F@{x y}.\nTime Fail Check F@{x y}.',
                          [('F', 2), ('F', 2)])

    def test_multiline_nested_comments_strings_qualified_names(self):
        self.assert_flags('''(* Check M.F@{_ _}. (* nested . *) *)
            Redirect "fake "" . Check M.F@{_ _}." Check nat.
            Fail Definition test@{u v} := M.F
              (* gap *) @{u (* nested (* . *) *) v}.
            Check @M.F@{_\n _}.
        ''', [])
        self.assert_flags('''(* Check F@{_}. *)
            Redirect "Check F@{_}." Check nat.
            Fail Check F@{u}.
        ''', [('F', 1)])

    def test_declaration_binders_are_not_instances(self):
        self.assert_flags('''Polymorphic Definition F@{u v | u < v} := nat.
            #[local] Fail Program Definition G@{u + | Set < u +} := F@{u u}.
        ''', [('F', 2)])
        self.assert_flags('Fail Definition G@{u} := Type@{max(u+1,u)}.', [])
        self.assert_flags('Timeout 30 Fail Definition G@{u} := F@{u}.', [('F', 1)])

    def test_declaration_is_not_control(self):
        self.assert_flags('Definition F@{u} := nat. Fail Check F@{u}.', [('F', 1)])

    def test_arity_zero(self):
        self.assert_flags('Check @F@{}. Fail Check F@{}.', [])
        self.assert_flags('Check @F@{_}. Fail Check F@{}.', [('F', 0)])

    def test_no_arbitrary_term_controls(self):
        for control in ('Definition x := F@{_}.', 'Check (erase F@{_}).',
                        'Notation bad := F@{_}.',
                        'Ltac delayed := exact F@{_}.',
                        'Goal True. try exact F@{_}. Abort.',
                        'Goal True. first [exact I | exact F@{_}]. Qed.'):
            with self.subTest(control=control):
                self.assert_flags(control + '\nFail Check F@{u}.', [('F', 1)])

    def test_scope_import_and_shadow_barriers(self):
        for barrier in ('Import B.', 'Require B.', 'Module B.', 'Section B.',
                        'End B.', 'Notation F := G.', 'Open Scope custom.',
                        'Definition F := nat.', 'Context (F : Type).',
                        'Variable F : Type.', 'intros F.'):
            with self.subTest(barrier=barrier):
                self.assert_flags('Check @F@{_}. ' + barrier + ' Fail Check F@{u}.',
                                  [('F', 1)])
        self.assert_flags('Check @A.F@{_}. Fail Check B.F@{u}.', [('B.F', 1)])
        self.assert_flags('Check @A.F@{_}. Definition F := nat. Fail Check A.F@{u}.',
                          [('A.F', 1)])

    def test_local_fail_binders_do_not_match_global_control(self):
        for command in ('Fail Definition bad (F : Type) := F@{u}.',
                        'Fail Check (fun F => F@{u}).',
                        'Fail Check (fun {F} => F@{u}).',
                        'Fail Check (BIND F IN F@{u}).',
                        'Fail Check (let F := nat in F@{u}).',
                        "Fail Check (fun '(F, x) => F@{u})."):
            with self.subTest(command=command):
                self.assert_flags('Check @F@{_}. ' + command, [('F', 1)])

    def test_tactic_references_need_qualification(self):
        for negative in (
                'Fail Definition bad : alias := ltac:(intros; exact F@{u}).',
                'Fail Definition bad : alias := ltac:(let q := constr:(@F@{u}) in exact I).',
                'Fail Check ltac2:(exact F@{u}).',
                'Fail exact F@{u}.'):
            with self.subTest(negative=negative):
                self.assert_flags('Check @F@{_}. ' + negative, [('F', 1)])
                self.assert_flags('Check @M.F@{_}. ' + negative.replace('F@', 'M.F@'), [])
        self.assert_flags('Check @F@{_}. Fail Definition bad : F@{u} := '
                          'ltac:(intros; exact I).', [])

    def test_mutual_declaration_not_match_branch(self):
        self.assert_flags('Fail Fixpoint f@{u} := F@{u} with g@{u} := F@{u}.',
                          [('F', 1), ('F', 1)])
        self.assert_flags('Fail Fixpoint f@{u} := match x with F@{u} => x end.',
                          [('F', 1)])

    def test_nested_module_cannot_leak_control(self):
        self.assert_flags('Section S. Module M. Check @F@{_}. End M. '
                          'Fail Check F@{u}. End S.', [('F', 1)])

    def test_source_only_cannot_certify_declaration_identity(self):
        self.assert_flags('Check @F@{_}. Definition G := nat. Fail Check F@{u}.', [('F', 1)])

    def test_whole_file_saft_instrument(self):
        # H4 removed N6's positional instance. Inject a fresh stale instance,
        # not a claim that the historical N6 still exists on this branch.
        source = (Path(__file__).resolve().parent.parent /
                  'Test/ProbeSAFT453.v').read_text()
        command = next(c for c in guard.commands(source)
                       if any(t.text == 'p453_n6_routes_convertible' for t in c))
        start, end = command[0].start, command[-1].start + 1
        original = source[start:end]
        control = 'Check @SAFT_cover_wp@{' + ' '.join(['_'] * 12) + '}.\n'
        for arity, expected in [(13, [('SAFT_cover_wp', 13)]), (12, [])]:
            with self.subTest(arity=arity):
                injected = original.replace('SAFT_cover_wp U',
                    'SAFT_cover_wp@{' + ' '.join(['_'] * arity) + '} U')
                self.assertNotEqual(injected, original)
                instrument = source[:start] + control + injected + source[end:]
                # This fast test isolates the injected arity mismatch. Full
                # acceptance of the companion is a fresh compiler gate run.
                flags = [(u.name, u.arity) for u in guard.scan(instrument)
                         if u.name == 'SAFT_cover_wp']
                self.assertEqual(flags, expected)

    def test_comment_strings_do_not_manufacture_or_hide_commands(self):
        for name, bad, good, _, _, _ in false_green_fixtures()[:4]:
            with self.subTest(name=name):
                self.assert_flags(bad, [('F', 3)])
                self.assert_flags(good, [])
        with self.assertRaises(guard.ScanError):
            list(guard.lex('(* "unterminated *)'))

    def test_glob_freshness_missing_swapped_and_ambiguous(self):
        source = 'Check @F@{_}. Fail Check @F@{_}.'
        uses = [u for c in guard.commands(source) for u in guard.instances(c)]
        header = 'DIGEST ' + guard.hashlib.md5(source.encode()).hexdigest() + '\nFCategory.Probe\n'
        records = ''.join(f'R{u.start}:{u.start} Category.Probe <> F def\n' for u in uses)
        evidence = guard.glob_references(source.encode(), header + records, 'Category.Probe')
        names = {u.start: ('Constant', 'Category.Probe.F') for u in uses}
        self.assertEqual(guard.scan(source, evidence, names), [])
        self.assertTrue(guard.scan(source, {}, names))
        self.assertTrue(guard.scan(source, evidence, {}))
        with self.assertRaises(guard.ScanError):
            guard.scan(source, evidence)
        for data in ('', header.replace('Category.Probe', 'Category.Other') + records,
                     header.replace('DIGEST ', 'DIGEST stale') + records):
            with self.subTest(data=data), self.assertRaises(guard.ScanError):
                guard.glob_references(source.encode(), data, 'Category.Probe')
        extra = f'R{uses[1].start}:{uses[1].start} Category.Other <> F def\n'
        ambiguous = guard.glob_references(source.encode(), header + records + extra, 'Category.Probe')
        self.assertTrue(guard.scan(source, ambiguous, names))

    def test_about_wrapping_and_ambiguity(self):
        import probe_arity_build as compiler
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'about.out'
            with self.assertRaises(guard.ScanError):
                compiler.canonical_about(path)
            line = 'Expands to: Constant\n  Category.Long.Path.F\n'
            path.write_text(line)
            self.assertEqual(compiler.canonical_about(path), ('Constant', 'Category.Long.Path.F'))
            path.write_text(line + line)
            with self.assertRaises(guard.ScanError):
                compiler.canonical_about(path)

    def test_broken_lexical_input_fails_closed(self):
        for text in ('(* unterminated', 'Check "unterminated', 'Fail Check F@{u',
                     'Fail Check F@{u+1}.'):
            with self.subTest(text=text), self.assertRaises(guard.ScanError):
                guard.scan(text)

    def test_other_file_is_not_control_and_exception_is_exact(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'A.v').write_text('Check @F@{_}.')
            (root / 'B.v').write_text('Fail Check F@{u}. Fail Check F@{u v}.')
            (root / 'exceptions.json').write_text(json.dumps([
                {'file': 'B.v', 'constant': 'F', 'arity': 1,
                 'reason': 'synthetic intentional arity error', 'evidence': 'test fixture'}]))
            exceptions = guard.load_exceptions(root / 'exceptions.json')
            errors, count, used = guard.check(root, ['A.v', 'B.v'], {})
            self.assertEqual((len(errors), count, used), (2, 2, 0))
            errors, _, used = guard.check(root, ['A.v', 'B.v'], exceptions)
            self.assertEqual((len(errors), used), (1, 1))
            self.assertIn('2 entries', errors[0])
            (root / 'B.v').write_text('Check @F@{_}. Fail Check F@{u}.')
            errors, _, _ = guard.check(root, ['B.v'], exceptions)
            self.assertIn('stale exception', errors[0])

    def test_invalid_exception_metadata(self):
        entry = {'file': 'B.v', 'constant': 'F', 'arity': 1,
                 'reason': 'intentional arity error', 'evidence': 'fixture'}
        with tempfile.TemporaryDirectory() as tmp:
            file = Path(tmp) / 'exceptions.json'
            invalid = [{}, [entry, entry], [dict(entry, reason='')], [dict(entry, reason=7)], [7], [None],
                       [dict(entry, arity=True)], [dict(entry, constant='*')]]
            invalid += [[dict(entry, **{field: value})] for field in
                        ('file', 'constant', 'reason', 'evidence', 'arity')
                        for value in (None, [], {}, 7.5)]
            for data in invalid:
                with self.subTest(data=data):
                    file.write_text(json.dumps(data))
                    with self.assertRaises(guard.ScanError):
                        guard.load_exceptions(file)

    def test_cli_reports_bad_exception_type_without_traceback(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'exceptions.json').write_text(json.dumps([{
                'file': 'Probe.v', 'constant': 'F', 'arity': 1,
                'reason': 7, 'evidence': 'fixture'}]))
            result = subprocess.run([sys.executable, '-B', str(Path(guard.__file__).resolve()),
                '--root', tmp, '--exceptions', 'exceptions.json'],
                capture_output=True, text=True, timeout=30)
            self.assertEqual(result.returncode, 1)
            self.assertIn('must be nonempty strings', result.stderr)
            self.assertNotIn('Traceback', result.stderr)

    def test_cli_rejects_and_accepts_nonempty_inventory(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / '_CoqProject').write_text('-R . Category\n"Probe.v" # source\n')
            (root / 'exceptions.json').write_text('[]')
            command = [sys.executable, '-B', str(Path(guard.__file__).resolve()),
                       '--root', tmp, '--exceptions', 'exceptions.json', '--syntax-only']
            for text, status in [('Fail Check F@{u}.', 1),
                                 ('Check @F@{_}. Fail Check F@{u}.', 0)]:
                (root / 'Probe.v').write_text(text)
                result = subprocess.run(command, capture_output=True, text=True, timeout=30)
                self.assertEqual(result.returncode, status, result.stderr)
                self.assertIn('1 files', result.stdout)
            (root / '_CoqProject').write_text('')
            self.assertNotEqual(subprocess.run(command, capture_output=True,
                                              timeout=30).returncode, 0)


@unittest.skipUnless(os.environ.get('PROBE_ARITY_COQC'), 'run probe-arity-coq-selftest')
class CompilerTests(unittest.TestCase):
    def compiled_fixture(self, root, source):
        import probe_arity_build as compiler
        root.mkdir()
        (root / '_CoqProject').write_text('-R . Category\nProbe.v\n')
        (root / 'Probe.v').write_text(source)
        (root / 'unreached.json').write_text('[]')
        snapshot, files, refs, ids, work = compiler.build(root, 2, 'unreached.json', root / 'evidence')
        errors, _, _ = guard.check(snapshot, files, {}, refs, ids)
        return errors, work

    def test_review_false_greens_and_companions(self):
        with compiler_evidence('review-fixtures') as tmp:
            for name, bad, good, target, stale, actual in false_green_fixtures():
                with self.subTest(name=name):
                    errors, work = self.compiled_fixture(Path(tmp) / (name + 'Bad'), bad)
                    self.assertTrue(errors, name)
                    stripped = work / 'Stripped.v'
                    stripped.write_text(bad.replace('Fail Check', 'Check'))
                    command = [os.environ['PROBE_ARITY_COQC'], '-q', str(stripped)]
                    result = subprocess.run(command, capture_output=True, text=True, timeout=60)
                    save_result(stripped, command, result)
                    self.assertNotEqual(result.returncode, 0, result.stdout)
                    self.assertIn(f'Universe instance length for {target} is {stale} but should be {actual}',
                                  result.stdout + result.stderr)
                    errors, _ = self.compiled_fixture(Path(tmp) / (name + 'Good'), good)
                    self.assertEqual(errors, [], name)
                    print(f'compiler regression {name}: false green rejected; arity strip confirmed; companion accepted')

    def test_stale_checkout_products_and_older_dependency_mtime(self):
        import probe_arity_build as compiler
        with compiler_evidence('freshness') as tmp:
            root = Path(tmp)
            (root / '_CoqProject').write_text('-R . Category\nBase.v\nProbe.v\n')
            (root / 'unreached.json').write_text('[]')
            (root / 'Base.v').write_text('Set Universe Polymorphism.\n'
                'Definition F@{u} (A : Type@{u}) := A.\n')
            (root / 'Probe.v').write_text('Require Import Category.Base.\n'
                'Check @F@{_}.\nFail Check (@F@{_} : nat).\n')
            snapshot, files, refs, ids, _ = compiler.build(root, 2, 'unreached.json', root / 'first')
            self.assertEqual(guard.check(snapshot, files, {}, refs, ids)[0], [])
            for file in files:
                for suffix in ('.vo', '.glob'):
                    path = Path(file).with_suffix(suffix)
                    (root / path).write_bytes((snapshot / path).read_bytes())
            (root / 'Base.v').write_text('Set Universe Polymorphism.\n'
                'Definition F@{u v} (A : Type@{u}) (B : Type@{v}) := A.\n')
            os.utime(root / 'Base.v', (1, 1))
            with self.assertRaises(guard.ScanError):
                compiler.build(root, 2, 'unreached.json', root / 'second')
            self.assertIn('Universe instance length for F is 1 but should be 2',
                          (root / 'second/build.log').read_text())
            with self.assertRaises(FileExistsError):
                compiler.build(root, 2, 'unreached.json', root / 'first')
            print('freshness regression: stale products/older dependency mtime rejected; no reuse mode')

    def test_implicit_tactic_context(self):
        prefix = ('Set Universe Polymorphism.\n'
                  'Polymorphic Definition F@{u} (A : Type@{u}) := A.\n'
                  'Check @F@{Set}.\n'
                  'Definition alias := forall F : nat, True.\n')
        with compiler_evidence('implicit-context') as tmp:
            for i, intro in enumerate(('intros', 'red; intros')):
                text = prefix + ('Definition probe : alias := ltac:(' + intro +
                                 '; let q := constr:(@F@{Set}) in exact I).\n')
                file = Path(tmp) / f'Implicit{i}.v'
                file.write_text(text)
                command = [os.environ['PROBE_ARITY_COQC'], str(file)]
                result = subprocess.run(command, capture_output=True, text=True, timeout=60)
                save_result(file, command, result)
                # On 9.1.1 intros alone does not unfold alias; red exposes it.
                # Neither result licenses inferring tactic-local name identity.
                if i == 0:
                    self.assertNotEqual(result.returncode, 0, result.stdout)
                    self.assertIn('expected to have type "alias"', result.stderr)
                else:
                    self.assertEqual(result.returncode, 0, result.stderr)
                negative = text.replace('Definition probe', 'Fail Definition probe')
                self.assertEqual([(u.name, u.arity) for u in guard.scan(negative)], [('F', 1)])
                print(f'implicit tactic context {i}: status {result.returncode}; guard rejects ambiguity')

    def test_real_control_elaboration(self):
        prefix = ('Set Universe Polymorphism.\n'
                  'Polymorphic Definition F@{u} (A : Type@{u}) := A.\n')
        cases = [
            ('Check F@{_}.', True),
            ('Check F@{_ _}.', False),
            ('Check @F@{_ _}.', False),
            ('Ltac delayed := let x := constr:(F@{_ _}) in idtac.', True),
            ('Goal True. try exact F@{_ _}. exact I. Qed.', True),
            ('Goal True. first [exact I | exact F@{_ _}]. Qed.', True),
            ('Notation bad := F@{_ _}.', True),
            ('Notation "\'erase\' x" := True (at level 0, x at level 99).\n'
             'Check (erase (F@{_ _})).', True),
        ]
        with compiler_evidence('controls') as tmp:
            for i, (body, success) in enumerate(cases):
                with self.subTest(body=body):
                    file = Path(tmp) / f'Control{i}.v'
                    file.write_text(prefix + body + '\n')
                    command = [os.environ['PROBE_ARITY_COQC'], str(file)]
                    result = subprocess.run(command, capture_output=True, text=True, timeout=60)
                    save_result(file, command, result)
                    output = result.stdout + result.stderr
                    self.assertEqual(result.returncode == 0, success, output)
                    if not success:
                        self.assertIn('Universe instance length for F is 2 but should be 1', output)
                    print(f'compiler control {i}: status {result.returncode}, expected '
                          f'{"success" if success else "arity refusal"}')


if __name__ == '__main__':
    unittest.main(verbosity=2)
