"""Acceptance tests for coverage, review gates, and stale-result protection."""
import argparse
from contextlib import redirect_stdout
import copy
import hashlib
import io
import json
from pathlib import Path
import shutil
import tempfile
import unittest
import zipfile

import yaml

import manage
import dry_run


class RegistryTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        (self.root / 'leaderboard').mkdir()
        (self.root / 'submissions').mkdir()
        shutil.copytree(manage.ROOT / 'templates', self.root / 'templates')
        self.ids = ['codeforces/cf1A', 'leetcode/lc1', 'leetcode/lc2']
        for pid in self.ids:
            (self.root / 'benchmark' / pid).mkdir(parents=True)
        content = '\n'.join(self.ids) + '\n'
        (self.root / 'leaderboard/problem_ids.txt').write_text(content)
        self.release = {'id': 'test-release', 'benchmark_revision': 'a' * 40,
                        'counts': {'codeforces': 1, 'leetcode': 2, 'full': 3},
                        'problem_ids_sha256': hashlib.sha256(content.encode()).hexdigest()}
        self.write(self.root / 'leaderboard/release.json', self.release)
        self.write(self.root / 'leaderboard/protocols.json', [])
        with redirect_stdout(io.StringIO()):
            manage.initialize(self.root, argparse.Namespace(id='test-system', track='agent', task='End2End', input_mode='nl', split='full'))
        self.entry = self.root / 'submissions/test-system'
        self.m = manage.load_yaml(self.entry / 'metadata.yaml')

        def fill(value):
            if isinstance(value, str):
                return value.replace('REPLACE_ME', 'Documented in methodology')
            if isinstance(value, dict):
                return {k: fill(v) for k, v in value.items()}
            if isinstance(value, list):
                return [fill(v) for v in value]
            return value

        self.m = fill(self.m)
        self.m['system'].update(authors=['Test author'], source_availability='unavailable')
        self.m['artifacts']['availability'] = 'pending'
        self.save_metadata()
        (self.entry / 'README.md').write_text('Synthetic test methodology. Never published.\n')
        self.rows = [json.loads(line) for line in (self.entry / 'results.jsonl').read_text().splitlines()]
        self.review = manage.load_json(self.entry / 'review.json')

    @staticmethod
    def write(path, obj):
        path.write_text(json.dumps(obj, indent=2) + '\n')

    def save_metadata(self):
        (self.entry / 'metadata.yaml').write_text(yaml.safe_dump(self.m, sort_keys=False))

    def save_rows(self):
        (self.entry / 'results.jsonl').write_text(''.join(json.dumps(r) + '\n' for r in self.rows))

    def save_review(self):
        self.write(self.entry / 'review.json', self.review)

    def validate(self):
        return manage.build(self.root)['entries'][0]

    def complete(self):
        tests = {'source': 'https://example.org/tests', 'revision': 'b' * 40, 'archive_sha256': None}
        self.m['benchmark']['testcases'].update(tests)
        self.m['artifacts'].update(availability='public', bundle_url='https://example.org/artifacts', revision='c' * 40)
        protocol = {'id': 'test-protocol', 'release': 'test-release', 'task': 'End2End', 'input_mode': 'nl',
                    'track': 'agent', 'policy_url': 'https://example.org/policy',
                    'testcases': tests, 'evaluator_revision': 'd' * 40, 'verus_version': 'test-verus',
                    'rustc_version': 'test-rust', 'environment': 'test image', 'resource_limits': 'test limits',
                    'spec_review_policy_url': 'https://example.org/spec-review'}
        self.write(self.root / 'leaderboard/protocols.json', [protocol])
        self.m['evaluation'].update({k: protocol[k] for k in ['evaluator_revision', 'verus_version', 'rustc_version', 'environment', 'resource_limits']})
        self.m['evaluation'].update(protocol_id='test-protocol', commands=['test-only evaluation command'])
        self.save_metadata()
        self.rows[0].update(generation_status='produced', artifacts={'program': 'programs/cf1A.rs'})
        self.rows[0]['checks'] = {'code_tests': 'pass', 'verus': 'pass', 'spec_tests': 'unsupported'}
        self.save_rows()
        self.review.update(status='evaluation_checked', submission_sha256=manage.fingerprint(self.entry),
                           reviewers=['maintainer'], reviewed_on='2026-10-08', report_url='https://example.org/review',
                           checked_problem_ids=self.ids, spec_review='complete',
                           verdicts={p: 'pass' if p == self.ids[0] else 'fail' for p in self.ids})
        self.save_review()

    def test_pending_entry_has_no_score(self):
        result = self.validate()
        self.assertIsNone(result['score'])
        self.assertFalse(result['rankable'])

    def test_average_cost_includes_failed_and_timed_out_attempts(self):
        self.m['experiment']['budget'].update(total_cost_usd=6, cost_notes='Test-only USD costs; all generation included.')
        self.rows[0]['generation_status'] = 'failed'
        self.rows[1]['generation_status'] = 'timeout'
        self.save_rows()
        self.save_metadata()
        result = self.validate()
        self.assertEqual(result['avg_cost_usd'], 3)
        self.assertEqual(result['cost_problem_count'], 2)
        self.assertEqual(result['problem_count'], 3)

    def test_unknown_and_zero_cost_are_distinct(self):
        self.assertIsNone(self.validate()['avg_cost_usd'])
        self.m['experiment']['budget'].update(total_cost_usd=0, cost_notes='Test-only zero cost.')
        self.rows[0]['generation_status'] = 'failed'
        self.save_rows()
        self.save_metadata()
        self.assertEqual(self.validate()['avg_cost_usd'], 0)

    def test_invalid_or_unexplained_cost_rejected(self):
        for value in (-1, True, '1.20', float('inf')):
            with self.subTest(value=value):
                self.m['experiment']['budget'].update(total_cost_usd=value, cost_notes='Test fixture.')
                self.save_metadata()
                with self.assertRaisesRegex(manage.Invalid, 'finite nonnegative'):
                    self.validate()
        self.m['experiment']['budget'].update(total_cost_usd=1, cost_notes=None)
        self.save_metadata()
        with self.assertRaisesRegex(manage.Invalid, 'budget.cost_notes'):
            self.validate()
        self.m['experiment']['budget']['cost_notes'] = 'No problems were attempted.'
        self.save_metadata()
        with self.assertRaisesRegex(manage.Invalid, 'at least one attempted'):
            self.validate()

    def test_public_table_dates_and_release_are_distinct(self):
        self.m['submitted_on'] = '2026-10-09'
        self.m['system'].update(version='v1.2.3', release_url='https://example.org/releases/v1.2.3')
        self.save_metadata()
        result = self.validate()
        self.assertEqual(result['date'], '2026-10-09')
        self.assertEqual(result['benchmark_release'], 'test-release')
        self.assertEqual(result['version'], 'v1.2.3')
        self.assertEqual(result['release_url'], 'https://example.org/releases/v1.2.3')

    def test_earlier_releases_accept_submissions(self):
        content = '\n'.join(self.ids[1:]) + '\n'
        (self.root / 'leaderboard/problem_ids-old-release.txt').write_text(content)
        old = {'id': 'old-release', 'git_tag': 'vold', 'benchmark_revision': 'e' * 40,
               'problem_ids_path': 'problem_ids-old-release.txt',
               'problem_ids_sha256': hashlib.sha256(content.encode()).hexdigest(),
               'counts': {'leetcode': 2, 'full': 2}}
        self.write(self.root / 'leaderboard/releases.json', [old])
        self.m['benchmark'].update(release='unknown-release')
        self.save_metadata()
        with self.assertRaisesRegex(manage.Invalid, 'must be one of: test-release, old-release'):
            self.validate()
        self.m['benchmark'].update(release='old-release', revision='a' * 40)
        self.save_metadata()
        with self.assertRaisesRegex(manage.Invalid, 'does not match the declared release'):
            self.validate()
        self.m['benchmark'].update(revision='e' * 40)
        self.save_metadata()
        with self.assertRaisesRegex(manage.Invalid, 'unknown/obsolete problem IDs'):
            self.validate()
        (self.entry / 'problem_ids.txt').write_text(content)
        self.m['benchmark']['problem_count'] = 2
        self.save_metadata()
        self.rows = [r for r in self.rows if r['problem_id'] != self.ids[0]]
        self.save_rows()
        result = self.validate()
        self.assertEqual((result['benchmark_release'], result['problem_count']), ('old-release', 2))
        data = manage.build(self.root)
        self.assertEqual([r['id'] for r in data['releases']], ['test-release', 'old-release'])
        protocol = {'id': 'test-protocol', 'release': 'test-release', 'task': 'End2End', 'input_mode': 'nl',
                    'track': 'agent', 'policy_url': 'https://example.org/policy',
                    'testcases': {'source': 'https://example.org/tests', 'revision': 'b' * 40},
                    'evaluator_revision': 'd' * 40, 'verus_version': 'test-verus', 'rustc_version': 'test-rust',
                    'environment': 'test image', 'resource_limits': 'test limits',
                    'spec_review_policy_url': 'https://example.org/spec-review'}
        self.write(self.root / 'leaderboard/protocols.json', [protocol])
        self.m['evaluation']['protocol_id'] = 'test-protocol'
        self.save_metadata()
        with self.assertRaisesRegex(manage.Invalid, 'protocol release mismatch'):
            self.validate()

    def test_model_column_uses_display_names(self):
        model = self.m['system']['models'][0]
        self.m['system']['models'] = [dict(model, id='example-model-2026-01-01', name='Example Model'),
                                      dict(model, id='example-model', name='Example Model'),
                                      dict(model, id='helper-model')]
        self.save_metadata()
        result = self.validate()
        self.assertEqual(result['model_names'], ['Example Model', 'helper-model'])
        self.assertEqual(result['models'], ['example-model-2026-01-01', 'example-model', 'helper-model'])

    def test_org_column_uses_organization_and_logo(self):
        result = self.validate()
        self.assertEqual((result['org'], result['org_logo']), (result['team'], None))
        (self.root / 'docs/static/logos').mkdir(parents=True)
        (self.root / 'docs/static/logos/example.svg').write_text('<svg xmlns="http://www.w3.org/2000/svg"/>')
        self.m['system'].update(organization='Example Lab', logo='static/logos/example.svg')
        self.save_metadata()
        result = self.validate()
        self.assertEqual((result['org'], result['org_logo']), ('Example Lab', 'static/logos/example.svg'))
        self.m['system']['logo'] = 'https://example.org/logo.svg'
        self.save_metadata()
        self.assertEqual(self.validate()['org_logo'], 'https://example.org/logo.svg')
        for bad, message in [('static/logos/missing.svg', 'missing from docs'),
                             ('../logos/example.svg', 'HTTPS URL'), ('javascript:alert(1)', 'HTTPS URL')]:
            self.m['system']['logo'] = bad
            self.save_metadata()
            with self.assertRaisesRegex(manage.Invalid, message):
                self.validate()

    def test_trajectory_links_respect_artifact_access(self):
        self.m['artifacts'].update(availability='private_by_arrangement', revision='c' * 40,
                                   bundle_url='https://example.org/private', traces_path='traces/')
        self.save_metadata()
        result = self.validate()
        self.assertEqual(result['trajectory_availability'], 'private_by_arrangement')
        self.assertIsNone(result['trajectory_url'])
        self.assertIsNone(result['trajectory_path'])
        self.m['artifacts'].update(availability='public', bundle_url='https://example.org/pinned.zip')
        self.save_metadata()
        self.assertEqual(self.validate()['trajectory_url'], 'https://example.org/pinned.zip')
        pinned = 'https://example.org/traces/' + 'd' * 40 + '/entry.jsonl.gz'
        self.m['artifacts']['traces_url'] = pinned
        self.save_metadata()
        self.assertEqual(self.validate()['trajectory_url'], pinned)
        self.m['artifacts']['availability'] = 'private_by_arrangement'
        self.save_metadata()
        self.assertEqual(self.validate()['trajectory_url'], pinned)

    def test_trajectory_link_must_be_pinned(self):
        self.m['artifacts']['traces_url'] = 'https://example.org/traces/main/entry.jsonl.gz'
        self.save_metadata()
        with self.assertRaisesRegex(manage.Invalid, 'must be pinned'):
            self.validate()

    def test_trajectories_are_required(self):
        self.m['artifacts']['traces_path'] = None
        self.save_metadata()
        with self.assertRaisesRegex(manage.Invalid, 'artifacts.traces_path'):
            self.validate()

    def test_metadata_paths_cannot_escape_bundle(self):
        for group, key in [('artifacts', 'readme_path'), ('artifacts', 'programs_path'),
                           ('artifacts', 'traces_path'), ('budget', 'measured_usage_path')]:
            target = self.m['experiment']['budget'] if group == 'budget' else self.m[group]
            previous = target[key]
            with self.subTest(field=key):
                target[key] = '../outside'
                self.save_metadata()
                with self.assertRaisesRegex(manage.Invalid, 'relative bundle path'):
                    self.validate()
            target[key] = previous

    def test_local_walkthrough_is_complete_but_never_ranked(self):
        before = manage.build(manage.ROOT)
        with redirect_stdout(io.StringIO()):
            destination = dry_run.create_example(self.root / 'walkthrough')
        entry = destination / 'local-example-agent'
        metadata = manage.load_yaml(entry / 'metadata.yaml')
        archive = destination / 'bundle.zip'
        self.assertEqual(metadata['artifacts']['archive_sha256'], hashlib.sha256(archive.read_bytes()).hexdigest())
        with zipfile.ZipFile(archive) as z:
            self.assertEqual(z.read('results.jsonl'), (entry / 'results.jsonl').read_bytes())
        preview = manage.load_json(destination / 'preview.json')
        self.assertEqual(preview['problem_count'], 284)
        self.assertEqual(preview['status'], 'submitted')
        self.assertIsNone(preview['score'])
        self.assertFalse(preview['rankable'])
        self.assertEqual(manage.build(manage.ROOT), before)
        with self.assertRaisesRegex(manage.Invalid, 'already exists'):
            dry_run.create_example(destination)
        with self.assertRaisesRegex(manage.Invalid, 'outside submissions'):
            dry_run.create_example(manage.ROOT / 'submissions/never-create-example')

    def test_denominator_includes_missing_outputs(self):
        self.complete()
        result = self.validate()
        self.assertAlmostEqual(result['score'], 100 / 3)
        self.assertTrue(result['rankable'])

    def test_full_entry_is_scored_on_each_split(self):
        self.complete()
        result = self.validate()
        self.assertEqual(result['split_problem_counts'], {'full': 3, 'leetcode': 2, 'codeforces': 1})
        self.assertAlmostEqual(result['split_scores']['full'], result['score'])
        self.assertEqual(result['split_scores']['leetcode'], 0)
        self.assertEqual(result['split_scores']['codeforces'], 100)

    def add_lite(self, ids=('codeforces/cf1A', 'leetcode/lc2')):
        content = ''.join(p + '\n' for p in ids)
        (self.root / 'leaderboard/lite_problem_ids.txt').write_text(content)
        self.release['lite'] = {'problem_ids_path': 'lite_problem_ids.txt', 'count': len(ids),
                                'problem_ids_sha256': hashlib.sha256(content.encode()).hexdigest()}
        self.write(self.root / 'leaderboard/release.json', self.release)

    def make_lite_entry(self):
        self.ids = ['codeforces/cf1A', 'leetcode/lc2']
        (self.entry / 'problem_ids.txt').write_text(''.join(p + '\n' for p in self.ids))
        self.rows = [r for r in self.rows if r['problem_id'] in self.ids]
        self.m['benchmark'].update(split='lite', problem_count=2)

    def test_full_entry_is_scored_on_lite(self):
        self.add_lite()
        self.complete()
        result = self.validate()
        self.assertEqual(result['split_problem_counts']['lite'], 2)
        self.assertEqual(result['split_scores']['lite'], 50)

    def test_lite_entry_is_scored_on_lite_only(self):
        self.add_lite()
        self.make_lite_entry()
        self.complete()
        result = self.validate()
        self.assertEqual(result['score'], 50)
        self.assertEqual(result['split_scores'], {'lite': 50})

    def test_lite_entry_needs_every_lite_problem(self):
        self.add_lite(('codeforces/cf1A', 'leetcode/lc1', 'leetcode/lc2'))
        self.make_lite_entry()
        self.complete()
        with self.assertRaisesRegex(manage.Invalid, 'lite requires all 3 problems'):
            self.validate()

    def test_lite_split_needs_a_lite_release(self):
        self.make_lite_entry()
        self.complete()
        with self.assertRaisesRegex(manage.Invalid, 'has no lite split'):
            self.validate()

    def test_full_entry_links_lite_trajectories(self):
        self.add_lite()
        lite = 'https://example.org/traces/' + 'e' * 40 + '/lite/entry.jsonl.gz'
        self.m['artifacts']['split_traces_urls'] = {'lite': lite}
        self.save_metadata()
        self.assertEqual(self.validate()['split_trajectory_urls'], {'lite': lite})
        self.m['artifacts']['split_traces_urls'] = {'lite': 'https://example.org/traces/main/lite/entry.jsonl.gz'}
        self.save_metadata()
        with self.assertRaisesRegex(manage.Invalid, 'split_traces_urls.lite must be pinned'):
            self.validate()

    def test_split_trajectories_need_a_full_entry_and_a_known_split(self):
        self.add_lite()
        lite = 'https://example.org/traces/' + 'e' * 40 + '/lite/entry.jsonl.gz'
        for split_traces in ({'full': lite}, {'unknown': lite}):
            with self.subTest(split_traces=split_traces):
                self.m['artifacts']['split_traces_urls'] = split_traces
                self.save_metadata()
                with self.assertRaisesRegex(manage.Invalid, 'other splits of a full-split entry'):
                    self.validate()
        self.make_lite_entry()
        self.m['artifacts']['split_traces_urls'] = {'lite': lite}
        self.save_metadata()
        self.save_rows()
        with self.assertRaisesRegex(manage.Invalid, 'other splits of a full-split entry'):
            self.validate()

    def test_lite_list_must_match_its_checksum(self):
        self.add_lite()
        (self.root / 'leaderboard/lite_problem_ids.txt').write_text('leetcode/lc1\n')
        with self.assertRaisesRegex(ValueError, 'Lite problem-list checksum mismatch'):
            manage.build(self.root)

    def test_unscored_entry_has_no_split_scores(self):
        result = self.validate()
        self.assertEqual(result['split_scores'], {'full': None, 'leetcode': None, 'codeforces': None})

    def test_no_rank_without_protocol(self):
        self.complete()
        self.m['evaluation']['protocol_id'] = None
        self.save_metadata()
        self.review['submission_sha256'] = manage.fingerprint(self.entry)
        self.save_review()
        with self.assertRaisesRegex(manage.Invalid, 'published evaluation protocol'):
            self.validate()

    def test_no_rank_without_human_spec_review(self):
        self.complete()
        self.review['spec_review'] = 'pending'
        self.save_review()
        with self.assertRaisesRegex(manage.Invalid, 'specification review is incomplete'):
            self.validate()

    def test_changed_artifact_pin_invalidates_review(self):
        self.complete()
        self.m['artifacts']['revision'] = 'f' * 40
        self.save_metadata()
        with self.assertRaisesRegex(manage.Invalid, 'fingerprint is stale'):
            self.validate()

    def test_old_benchmark_rejected(self):
        self.m['benchmark']['revision'] = '0' * 40
        self.save_metadata()
        with self.assertRaisesRegex(manage.Invalid, 'does not match the declared release'):
            self.validate()

    def test_missing_result_rejected(self):
        self.rows.pop()
        self.save_rows()
        with self.assertRaisesRegex(manage.Invalid, 'exactly one record'):
            self.validate()

    def test_duplicate_result_rejected(self):
        self.rows[1] = copy.deepcopy(self.rows[0])
        self.save_rows()
        with self.assertRaisesRegex(manage.Invalid, 'exactly one record'):
            self.validate()

    def test_full_split_cannot_drop_problem(self):
        (self.entry / 'problem_ids.txt').write_text('\n'.join(self.ids[:2]) + '\n')
        with self.assertRaisesRegex(manage.Invalid, 'requires all 3'):
            self.validate()

    def test_custom_subset_is_never_ranked(self):
        self.complete()
        self.m['benchmark']['split'] = 'custom'
        self.save_metadata()
        self.review['submission_sha256'] = manage.fingerprint(self.entry)
        self.save_review()
        self.assertFalse(self.validate()['rankable'])

    def test_partial_review_cannot_claim_final_score(self):
        self.complete()
        self.review['verdicts'].pop(self.ids[1])
        self.save_review()
        with self.assertRaisesRegex(manage.Invalid, 'verdict for every problem'):
            self.validate()

    def test_protocol_mismatch_rejected(self):
        self.complete()
        self.m['evaluation']['evaluator_revision'] = 'e' * 40
        self.save_metadata()
        with self.assertRaisesRegex(manage.Invalid, 'protocol evaluator_revision mismatch'):
            self.validate()

    def test_failed_code_cannot_pass(self):
        self.complete()
        self.rows[0]['checks']['code_tests'] = 'fail'
        self.save_rows()
        self.review['submission_sha256'] = manage.fingerprint(self.entry)
        self.save_review()
        with self.assertRaisesRegex(manage.Invalid, 'requires code_tests pass'):
            self.validate()

    def test_pending_artifacts_cannot_claim_review(self):
        self.review.update(status='automated_checks_complete', submission_sha256=manage.fingerprint(self.entry),
                           reviewers=['maintainer'], reviewed_on='2026-10-08', report_url='https://example.org/review', checked_problem_ids=[self.ids[0]])
        self.save_review()
        with self.assertRaisesRegex(manage.Invalid, 'pinned available artifacts'):
            self.validate()

    def test_script_url_rejected(self):
        self.m['artifacts']['bundle_url'] = 'javascript:alert(1)'
        self.save_metadata()
        with self.assertRaisesRegex(manage.Invalid, 'HTTPS URL'):
            self.validate()

    def test_bundle_path_escape_rejected(self):
        self.rows[0]['artifacts'] = {'program': '../secret.rs'}
        self.rows[0]['logs'] = {'program': 'legitimate.log'}
        self.save_rows()
        with self.assertRaisesRegex(manage.Invalid, 'relative bundle path'):
            self.validate()

    def test_duplicate_yaml_key_rejected(self):
        with (self.entry / 'metadata.yaml').open('a') as stream:
            stream.write('format_version: 1\n')
        with self.assertRaisesRegex(manage.Invalid, 'duplicate key'):
            self.validate()

    def test_boolean_is_not_a_format_version(self):
        self.m['format_version'] = True
        self.save_metadata()
        with self.assertRaisesRegex(manage.Invalid, 'format_version'):
            self.validate()

    def test_partial_rerun_cannot_claim_full_endpoint_origin(self):
        self.complete()
        self.review.update(artifact_origin='team_endpoint', rerun_problem_ids=[self.ids[0]])
        self.save_review()
        with self.assertRaisesRegex(manage.Invalid, 'entire submission'):
            self.validate()

    def test_scaffolder_refuses_overwrite(self):
        with self.assertRaisesRegex(manage.Invalid, 'refusing to overwrite'):
            manage.initialize(self.root, argparse.Namespace(id='test-system', track='agent', task='End2End', input_mode='nl', split='full'))

    def test_real_empty_registry_builds(self):
        data = manage.build(manage.ROOT)
        self.assertEqual(data['release']['counts']['full'], 1006)


if __name__ == '__main__':
    unittest.main()
