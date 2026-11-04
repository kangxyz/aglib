# GitHub automation

[Lean CI](LEAN_CI.md) covers runner routing, execution order, cache boundaries and
recovery. [Development](../docs/DEVELOPMENT.md#local-verification-and-ci) owns
the local verification commands.

| Path | Responsibility |
| --- | --- |
| [`workflows/ci.yml`](workflows/ci.yml) | Aglib triggers, runner selection and resource settings |
| [`workflows/lean-ci.yml`](workflows/lean-ci.yml) | Shared build, checks, checkpoint handling and publication |
| [`workflows/ec2-pilot.yml`](workflows/ec2-pilot.yml) | Manual self-hosted runner smoke test |
| [`workflows/cache-checkpoints.yml`](workflows/cache-checkpoints.yml) | Linux tests for cold recovery, timeout continuation and archive repair |
| [`ci-cache/`](ci-cache/) | Scoped compilation checkpoints and native publication staging |
| [`ci-resource-monitor.py`](ci-resource-monitor.py) | Resource sampling and job-summary table |
| [`lint/run.sh`](lint/run.sh) | Workflow entry to the shared lint adapter under `scripts/lean_tools/_lint/` |
| [`workflows/cache-promotion.yml`](workflows/cache-promotion.yml), [`cache-promotion/`](cache-promotion/) | Explicit cache transfer for branch promotion |
| [`actions/lake-cache/`](actions/lake-cache/) | Compatibility cache action for explicit callers |

Run the workflow and checkpoint regression tests from the repository root.

```sh
PYTHONPATH=scripts python3 -m unittest discover -s scripts/tests -p 'test_lean_ci_workflow.py'
python3 -m unittest discover -s .github/ci-cache -p 'test_*.py'
```

The workflow suite uses PyYAML and the cache tests use `tar` and `zstd`. The
checkpoint workflow also exercises the pinned Linux Lean toolchain on fresh
runners.
