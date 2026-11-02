"""Mechanical projection of the existing native raw Expr DAG output only."""
import hashlib
import json
from pathlib import Path
import re
import sys

source = Path(sys.argv[1])
destination = Path(sys.argv[2])
text = source.read_text()
sha = lambda data: hashlib.sha256(data).hexdigest()


def project(label):
    begin = f"RAW_{label}_BEGIN\n"
    end = f"RAW_{label}_END\n"
    start = text.index(begin)
    finish = text.index(end, start) + len(end)
    block = text[start:finish]
    path = destination / (label + ".rawexprdag.txt")
    path.write_text(block)
    root = re.search(rf"^RAW_{label}_ROOT (\d+) nodes=(\d+)$", block, re.M)
    body = block[len(begin):block.index(f"RAW_{label}_ROOT")]
    nodes = {
        int(m.group(1)): m.group(2).rstrip()
        for m in re.finditer(r"^RAW_NODE (\d+) (.*?)(?=^RAW_NODE |\Z)", body, re.M | re.S)
    }
    assert len(nodes) == int(root.group(2))
    return {
        "file": str(path), "sha256": sha(block.encode()), "bytes": len(block.encode()),
        "root": int(root.group(1)), "structural_dag_nodes": len(nodes),
    }, nodes


def spine(nodes, index):
    arguments = []
    while nodes[index].startswith("app "):
        match = re.fullmatch(r"app fn=(\d+) arg=(\d+)", nodes[index])
        arguments.append(int(match.group(2)))
        index = int(match.group(1))
    return index, list(reversed(arguments))


def brief(nodes, index):
    head, arguments = spine(nodes, index)
    payload = nodes[head]
    data = {
        "node": index, "kind": nodes[index].split()[0], "head_node": head,
        "head_payload": payload, "application_argument_count": len(arguments),
    }
    if payload.startswith("const "):
        data["head_constant"] = re.match(r"const name=`([^ ]+)", payload).group(1)
        data["head_levels_repr"] = payload.split(" levels=", 1)[1]
    return data


def application(nodes, index):
    result = brief(nodes, index)
    _, arguments = spine(nodes, index)
    result["immediate_arguments"] = [brief(nodes, value) for value in arguments]
    return result


actual, actual_nodes = project("ACTUAL")
expected, expected_nodes = project("EXPECTED")
diff_actual, diff_actual_nodes = project("DIFF_ACTUAL")
diff_expected, diff_expected_nodes = project("DIFF_EXPECTED")
status = re.search(r"^RAW_EQUALITY alpha=(\w+) structural=(\w+)$", text, re.M)
pair = re.search(r"^PAIR_RETAINED actualHasMVars=(\w+) expectedHasMVars=(\w+)$", text, re.M)
diff = re.search(r"^FIRST_DIFF path=([^ ]+) reason=(.*)$", text, re.M)
path = diff.group(1)
steps = re.findall(r"\.(arg\[\d+\]|head)", path)
assert "root" + "".join("." + step for step in steps) == path
actual_index, expected_index = actual["root"], expected["root"]
walk = [{"path": "root", "actual": application(actual_nodes, actual_index),
         "expected": application(expected_nodes, expected_index)}]
prefix = "root"
for step in steps:
    actual_head, actual_arguments = spine(actual_nodes, actual_index)
    expected_head, expected_arguments = spine(expected_nodes, expected_index)
    if step == "head":
        actual_index, expected_index = actual_head, expected_head
    else:
        position = int(step[4:-1])
        actual_index = actual_arguments[position]
        expected_index = expected_arguments[position]
    prefix += "." + step
    walk.append({"path": prefix, "actual": application(actual_nodes, actual_index),
                 "expected": application(expected_nodes, expected_index)})

assert actual_nodes[actual_index] == diff_actual_nodes[diff_actual["root"]]
assert expected_nodes[expected_index] == diff_expected_nodes[diff_expected["root"]]
context = [line for line in text.splitlines()
           if line.startswith(("PRODUCER_LEVELS ", "ORIGINAL_BINDER ", "ORIGINAL_LOCAL ",
                               "EXPECTED_BINDER ", "ACTUAL_INFER_START "))]
context_path = destination / "ALIGNED_CONTEXT.txt"
context_path.write_text("\n".join(context) + "\n")
output = {
    "input_stdout": str(source), "input_stdout_sha256": sha(source.read_bytes()),
    "actual": actual, "expected": expected,
    "actual_has_mvars": pair.group(1) == "true",
    "expected_has_mvars": pair.group(2) == "true",
    "raw_alpha_equal": status.group(1) == "true",
    "raw_structural_equal": status.group(2) == "true",
    "first_difference_path": path, "first_difference_reason": diff.group(2),
    "first_difference_actual": diff_actual, "first_difference_expected": diff_expected,
    "difference_path_walk": walk, "aligned_context": str(context_path),
    "aligned_context_sha256": sha(context_path.read_bytes()),
    "original_local_count": sum(line.startswith("ORIGINAL_LOCAL ") for line in context),
    "expected_binder_mapping_count": sum(line.startswith("EXPECTED_BINDER ") for line in context),
    "evidence_boundary": "Raw structural projection of existing output; no Lean execution, "
                         "normalization, definitional equality, or mathematical interpretation.",
}
output_path = destination / "RAW_PAIR_PROJECTION.json"
output_path.write_text(json.dumps(output, ensure_ascii=False, indent=2) + "\n")
print(json.dumps({"projection": str(output_path), "actual": actual, "expected": expected,
                  "first_difference_path": path, "last_application_pair": walk[-2]},
                 ensure_ascii=False, indent=2))
