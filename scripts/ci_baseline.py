"""Select an ancestor with successful native CI evidence; never build or fetch."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import ssl
import subprocess
import sys
import time
import urllib.error
import urllib.parse
import urllib.request


sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'ci'))
from lean_ci import github as _generic


WORKFLOW = '.github/workflows/ci.yml'
NATIVE_STEP = 'Run CI checks for the library and independent client'
FINALIZE_STEP = 'Finalize complete CI coverage'
MAX_PAGES = 10  # GitHub workflow-run searches expose at most 1,000 results.
API_ATTEMPTS = 3

# Protocol admission is explicit source review, never shell/YAML inference.
# Enroll changed content only after its exact invocation protocol is reviewed.
REVIEWED_WORKFLOWS = {
    'd9f0c1873df405e62780963687c7d4459e363823f8fc045d801a8d0a113da3cc': 'legacy whole-native workflow',
    '3dca194bb4d22a3569c6dc77bc2e609d30390feb3e40bcdfa03c112acc445407': 'verified CI-core workflow',
}
LEGACY_RECIPE_SHA256 = '441bb18419661c8dff622f6b23b75332d2c0e58eba26f0b47e751be003fc5ad2'
REVIEWED_LEGACY_HEADS = frozenset({'cc17eecf0344f15c89ffc04cade60b1b09cf9f43'})
CORE_ENTRYPOINT_PATHS = (
    'scripts/ci_pipeline.py', 'scripts/ci_state.py', 'scripts/affected_scope.py',
    'scripts/check_affected.py', 'scripts/library_sources.py', 'scripts/prepare_downstream.py',
    'scripts/resource_guard.py', 'scripts/build_serial.py',
    'scripts/run_declaration_linter.py', 'scripts/run_style_linter.py',
    'scripts/check_negative_controls.py', 'scripts/check_compiled_inventory.py',
    'ci/native_test.py',
    *('ci/lean_ci/' + name + '.py' for name in
      ('__init__', '__main__', 'source', 'state', 'github', 'engine', 'runtime', 'resources', 'build', 'cli')),
)
# Ordered implementation-owner SHA256 tuples. The unsafe 7e6 recipe is absent.
# Enroll a complete repaired source tuple after independent source review.
# Supporting-source correctness retains the repository's independent-review and
# trusted-producer premise; this does not authenticate arbitrary dependencies.
REVIEWED_CORE_RECIPES = frozenset({
})


BaselineError = _generic.BaselineError
APIUnavailable = _generic.APIUnavailable
EvidenceProtocol = _generic.EvidenceProtocol
GitHubAPI = _generic.GitHubAPI
git = _generic.git
git_file = _generic.git_file
commit = _generic.commit
ancestor = _generic.ancestor


def evidence_protocol():
    reverse = {label: kind for kind, label in _generic.KIND_LABELS.items()}
    return EvidenceProtocol(
        workflow_path=WORKFLOW, job_name='library', native_step=NATIVE_STEP,
        finalize_step=FINALIZE_STEP,
        workflows={sha: reverse[kind] for sha, kind in REVIEWED_WORKFLOWS.items()},
        legacy_recipes={'scripts/check.sh': LEGACY_RECIPE_SHA256},
        legacy_heads=REVIEWED_LEGACY_HEADS,
        core_entrypoint_paths=CORE_ENTRYPOINT_PATHS, core_recipes=REVIEWED_CORE_RECIPES)


def workflow_kind(workflow):
    kind = _generic.workflow_kind(workflow, evidence_protocol())
    return _generic.KIND_LABELS.get(kind)


def reviewed_recipe(root, revision, kind):
    reverse = {label: value for value, label in _generic.KIND_LABELS.items()}
    return _generic.reviewed_recipe(root, revision, reverse.get(kind, kind), evidence_protocol())


def native_success(api, run, require_finalization=False, evidence=None):
    return _generic.native_success(api, run, require_finalization, evidence, protocol=evidence_protocol())


def select(root, repository, default_branch, head, requested_base=None, api=None):
    return _generic.select(root, repository, default_branch, head, requested_base,
                           api if api is not None else GitHubAPI(repository), protocol=evidence_protocol())


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repository', required=True)
    parser.add_argument('--default-branch', default='main')
    parser.add_argument('--head', required=True)
    parser.add_argument('--requested-base')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--github-output', type=Path)
    args = parser.parse_args(argv)
    try:
        result = select(Path.cwd(), args.repository, args.default_branch, args.head, args.requested_base)
        args.output.write_text(json.dumps(result, indent=2) + '\n')
        if args.github_output:
            with args.github_output.open('a') as output:
                output.write('base=' + result['base'] + '\n')
    except (BaselineError, OSError) as exc:
        print('CI baseline selection failed: ' + str(exc), file=sys.stderr)
        return 1
    print(f"Verified CI baseline {result['base']} for {result['head']}: "
          f"run {result['run_id']} attempt {result['run_attempt']}; "
          f"{result['selection_reason']}; rejected {result['rejected_runs']} run(s)")
    return 0


if __name__ == '__main__':
    sys.exit(main())
