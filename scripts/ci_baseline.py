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
# Changes require independent review of their affected source owners.
# Supporting-source correctness retains the repository's independent-review and
# trusted-producer premise; this does not authenticate arbitrary dependencies.
REVIEWED_CORE_RECIPES = frozenset({
    # Independently reviewed source: fd73486f3b9d2caaee5da270262ec3835f12b17d.
    (
        'e5a9c10f660ee40d042f53452849b1f698e35f3131a0134e7ab34f664c7d65ab',  # scripts/ci_pipeline.py
        '46bd04a0663879683fcde54386b98101610f50a405677e128fbebef8f6d04fb4',  # scripts/ci_state.py
        '0669fbbf147e2489db699f4dc7a775c4718261568593552d48676b071ef4658f',  # scripts/affected_scope.py
        '33a603f1bc8478ceb83d5c6a4a68fad7062e08f0e9eb567514e54c232f76413a',  # scripts/check_affected.py
        '90a59c54d6a62d728006ea230b3200e97e605571c827b0c55acd934c0ad2044b',  # scripts/library_sources.py
        'ec0e06f4f3a37a2fce6febef22ddc79b9fd9610c80f06b5f42897196bead2ab6',  # scripts/prepare_downstream.py
        'b7e85596f59a2627424eeaf30a0367da1aff89ffe8ef5a2847ad2b9a3cd7f6c0',  # scripts/resource_guard.py
        '66fdc8dc202a54d568e52fc94651a9c47789cc16009bdd069812b1c9616d0413',  # scripts/build_serial.py
        '615ae732055d58454ffce066b9ccbb0b84786c67b55e9b6746a5b01387ade1b5',  # scripts/run_declaration_linter.py
        '0eec427d1c94ec97cf9ef68f38e2ad3e6df372bc24138b8805c2db5ff44437ae',  # scripts/run_style_linter.py
        'b3d3b065d741428958a7f53872d6f00aaedced80d666a3812549c7ca85b32818',  # scripts/check_negative_controls.py
        'f092bbb6c3fcb45deb14cc74b01863f7a790cc203fff4bbc8da12f21b93fb518',  # scripts/check_compiled_inventory.py
        'a81966955fae15d248fbd8f789a336d8d75fd0871dc154b15aa26d4667b537d8',  # ci/native_test.py
        '3868ebea3761908a46678490847815974425b323a86690885c6b7c2a3804f73d',  # ci/lean_ci/__init__.py
        'd240a28939151c947f5cfc64a569d6e8ad8132dcd747cb61844c62fb517cc4f5',  # ci/lean_ci/__main__.py
        'aca3ae29f06f436895af36adc6f048f70985f7b3e6305d585bed09fa0515f50b',  # ci/lean_ci/source.py
        '1ffc0711ad70a652645e8ed288f3ad196b25452467d11af0b1c8d05b90d76bf2',  # ci/lean_ci/state.py
        '0595f57a196b3a5b73de0e7e896fe2e6029125d732a94c65a4872f247d20b66a',  # ci/lean_ci/github.py
        'd8aeb9eb510507360460c4acaa9a6c6585de971524032323fad9bf3d1ac2c309',  # ci/lean_ci/engine.py
        '030acf0422e65334863150c7b0abc25ad8047982ede76f465e499742dee37623',  # ci/lean_ci/runtime.py
        '5fc841c4da719be2e10f0178633693ff5d13177422ef42257f6c03a320f709b1',  # ci/lean_ci/resources.py
        '90f4ec5174d6d8e4d4e64d6f9d818b9d192da5bd230a3cb93f991f9a013fca7a',  # ci/lean_ci/build.py
        '35d89f7bfeb1a510828a4fbaaf3561217ef39763f77b56f0c2cd63b17e2ac657',  # ci/lean_ci/cli.py
    ),
    # Independently reviewed fixed-source integration: 57c4890c4cee91a08c8808113ea0743725db741d.
    (
        '98a698ee3c2ba30ea9836f4f0d9ed6c30e7951ebf57bca8e7280ee45e9f58d6e',  # scripts/ci_pipeline.py
        '46bd04a0663879683fcde54386b98101610f50a405677e128fbebef8f6d04fb4',  # scripts/ci_state.py
        'b4e645e03288f6327dd9e0f49be63ad1ea1461142304823d6067c666791cd1f4',  # scripts/affected_scope.py
        '820d0e9ce49d1907d6bbebbe86fe27abf8bdde0c5ddf873e934c618f43b53969',  # scripts/check_affected.py
        '90a59c54d6a62d728006ea230b3200e97e605571c827b0c55acd934c0ad2044b',  # scripts/library_sources.py
        'ec0e06f4f3a37a2fce6febef22ddc79b9fd9610c80f06b5f42897196bead2ab6',  # scripts/prepare_downstream.py
        'b7e85596f59a2627424eeaf30a0367da1aff89ffe8ef5a2847ad2b9a3cd7f6c0',  # scripts/resource_guard.py
        '66fdc8dc202a54d568e52fc94651a9c47789cc16009bdd069812b1c9616d0413',  # scripts/build_serial.py
        '615ae732055d58454ffce066b9ccbb0b84786c67b55e9b6746a5b01387ade1b5',  # scripts/run_declaration_linter.py
        '0eec427d1c94ec97cf9ef68f38e2ad3e6df372bc24138b8805c2db5ff44437ae',  # scripts/run_style_linter.py
        'b3d3b065d741428958a7f53872d6f00aaedced80d666a3812549c7ca85b32818',  # scripts/check_negative_controls.py
        'f092bbb6c3fcb45deb14cc74b01863f7a790cc203fff4bbc8da12f21b93fb518',  # scripts/check_compiled_inventory.py
        '75aa6dcdbf05b8cc2e8e747371e4b822771756fc676204db6b5ce7154f15cf15',  # ci/native_test.py
        '3868ebea3761908a46678490847815974425b323a86690885c6b7c2a3804f73d',  # ci/lean_ci/__init__.py
        'd240a28939151c947f5cfc64a569d6e8ad8132dcd747cb61844c62fb517cc4f5',  # ci/lean_ci/__main__.py
        'aca3ae29f06f436895af36adc6f048f70985f7b3e6305d585bed09fa0515f50b',  # ci/lean_ci/source.py
        '1ffc0711ad70a652645e8ed288f3ad196b25452467d11af0b1c8d05b90d76bf2',  # ci/lean_ci/state.py
        '0595f57a196b3a5b73de0e7e896fe2e6029125d732a94c65a4872f247d20b66a',  # ci/lean_ci/github.py
        'd8aeb9eb510507360460c4acaa9a6c6585de971524032323fad9bf3d1ac2c309',  # ci/lean_ci/engine.py
        '030acf0422e65334863150c7b0abc25ad8047982ede76f465e499742dee37623',  # ci/lean_ci/runtime.py
        '5fc841c4da719be2e10f0178633693ff5d13177422ef42257f6c03a320f709b1',  # ci/lean_ci/resources.py
        '90f4ec5174d6d8e4d4e64d6f9d818b9d192da5bd230a3cb93f991f9a013fca7a',  # ci/lean_ci/build.py
        '35d89f7bfeb1a510828a4fbaaf3561217ef39763f77b56f0c2cd63b17e2ac657',  # ci/lean_ci/cli.py
    ),
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
