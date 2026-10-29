"""Project the existing fixed local-W type capture without Lean execution."""
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import re
import sys

source = Path(sys.argv[1])
destination = Path(sys.argv[2])
text = source.read_text()
sha = lambda data: hashlib.sha256(data).hexdigest()
standard = "CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard"
generic = ("CategoryTheory.GrothendieckTopology."
           "instWEqualsLocallyBijectiveOfHasWeakSheafifyOfHasSheafComposeOfPreserves"
           "SheafificationOfReflectsIsomorphismsForget")
graphs, metadata, blocks = {}, {}, {}
for match in re.finditer(r"^RAW_(\w+)_BEGIN$", text, re.M):
    label = match.group(1)
    finish = text.index(f"RAW_{label}_END\n", match.start()) + len(f"RAW_{label}_END\n")
    block = text[match.start():finish]
    root = re.search(rf"^RAW_{label}_ROOT (\d+) nodes=(\d+)$", block, re.M)
    body = block[block.index("\n") + 1:block.index(f"RAW_{label}_ROOT")]
    nodes = {int(m.group(1)): m.group(2).rstrip() for m in re.finditer(
        r"^RAW_NODE (\d+) (.*?)(?=^RAW_NODE |\Z)", body, re.M | re.S)}
    assert len(nodes) == int(root.group(2))
    blocks[label], graphs[label] = block, nodes
    metadata[label] = {"root": int(root.group(1)), "nodes": len(nodes),
                       "sha256": sha(block.encode()), "bytes": len(block.encode())}
    names = [re.match(r"const name=`([^ ]+)", payload).group(1)
             for payload in nodes.values() if payload.startswith("const ")]
    metadata[label]["standard_unique_const_nodes"] = names.count(standard)
    metadata[label]["generic_unique_const_nodes"] = names.count(generic)

counts = {}
for label, a, b in re.findall(
        r"^W_HEADS (\w+) standardUniqueConstNodes=(\d+) genericUniqueConstNodes=(\d+)$",
        text, re.M):
    counts[label] = {"standard": int(a), "generic": int(b)}
    assert metadata[label]["standard_unique_const_nodes"] == int(a)
    assert metadata[label]["generic_unique_const_nodes"] == int(b)

for label, filename in [("ACTUAL", "ACTUAL.rawexprdag.txt"),
                        ("EXPECTED_CLOSED_BINDER_20", "EXPECTED_CLOSED_GOAL.rawexprdag.txt")]:
    path = destination / filename
    path.write_text(blocks[label])
    metadata[label]["file"] = str(path)

bundle = bytearray()
bundle_path = destination / "CLOSED_BINDER_TYPES.rawexprdag.txt"
for label in blocks:
    if label in ("ACTUAL", "EXPECTED_CLOSED_BINDER_20"):
        continue
    metadata[label]["file"] = str(bundle_path)
    metadata[label]["bundle_byte_offset"] = len(bundle)
    bundle.extend(blocks[label].encode())
bundle_path.write_bytes(bundle)


def spine(nodes, index):
    args = []
    while nodes[index].startswith("app "):
        m = re.fullmatch(r"app fn=(\d+) arg=(\d+)", nodes[index])
        args.append(int(m.group(2)))
        index = int(m.group(1))
    return index, list(reversed(args))


def brief(nodes, index):
    head, args = spine(nodes, index)
    return {"node": index, "kind": nodes[index].split()[0],
            "head_node": head, "head_payload": nodes[head], "argument_count": len(args)}


def parts(payload):
    kind = payload.split()[0]
    keys = {"app": ("fn", "arg"), "lambda": ("type", "body"),
            "forall": ("type", "body"), "let": ("type", "value", "body"),
            "metadata": ("body",), "projection": ("body",)}.get(kind, ())
    refs = []
    for key in keys:
        m = re.search(rf"\b{key}=(\d+)\b", payload)
        refs.append((key, int(m.group(1))))
    primitive = payload
    for key, value in refs:
        primitive = re.sub(rf"\b{key}={value}\b", f"{key}=<node>", primitive)
    return primitive, refs


def compare(label_a, label_b):
    a, b = graphs[label_a], graphs[label_b]

    @lru_cache(None)
    def equal(ia, ib):
        pa, ra = parts(a[ia])
        pb, rb = parts(b[ib])
        return (pa == pb and len(ra) == len(rb)
                and all(ka == kb and equal(va, vb) for (ka, va), (kb, vb) in zip(ra, rb)))

    def difference(ia, ib, path="root", fuel=32):
        if equal(ia, ib):
            return None
        if fuel == 0:
            return {"path": path, "reason": "bounded-depth",
                    "producer": brief(a, ia), "expected": brief(b, ib)}
        if a[ia].startswith("app ") and b[ib].startswith("app "):
            ha, aa = spine(a, ia)
            hb, ab = spine(b, ib)
            found = difference(ha, hb, path + ".head", fuel - 1)
            if found:
                return found
            for i, (va, vb) in enumerate(zip(aa, ab)):
                found = difference(va, vb, f"{path}.arg[{i}]", fuel - 1)
                if found:
                    return found
        else:
            pa, ra = parts(a[ia])
            pb, rb = parts(b[ib])
            if pa == pb:
                for (key, va), (_, vb) in zip(ra, rb):
                    found = difference(va, vb, path + "." + key, fuel - 1)
                    if found:
                        return found
        return {"path": path, "reason": "raw-constructor-payload-or-arity",
                "producer": brief(a, ia), "expected": brief(b, ib)}

    ra, rb = metadata[label_a]["root"], metadata[label_b]["root"]
    return {"producer_graph": label_a, "expected_graph": label_b,
            "raw_structural_equal": equal(ra, rb), "first_difference": difference(ra, rb)}


comparisons = [dict(index=index, **compare(f"PRODUCER_CLOSED_BINDER_{index}",
                                          f"EXPECTED_CLOSED_BINDER_{index}"))
               for index in range(6, 14)]
closed_names = re.findall(r"^CLOSED_BINDER (\w+) index=(\d+) name=(.*?) info=(.*)$", text, re.M)
matches = re.findall(r"^BINDER_TYPE_MATCH index=(\d+) name=(.*?) alpha=(\w+) structural=(\w+)$",
                     text, re.M)
context = [line for line in text.splitlines() if line.startswith(
    ("PRODUCER_LEVELS ", "ORIGINAL_BINDER ", "ORIGINAL_LOCAL ", "CLOSED_BINDER ",
     "CLOSED_BINDERS_COMPLETE ", "EXPECTED_BINDER ", "BINDER_TYPE_MATCH ", "ACTUAL_INFER_START "))]
gap = [line for line in text.splitlines() if "error:" in line]
context_path = destination / "CAPTURE_CONTEXT.txt"
context_path.write_text("\n".join(context) + "\n")
result = {
    "input_stdout": str(source), "input_stdout_sha256": sha(source.read_bytes()),
    "graphs": metadata, "raw_graph_count": len(graphs), "w_head_counts": counts,
    "closed_binder_names": [{"side": a, "index": int(b), "name": c, "binder_info": d}
                            for a, b, c, d in closed_names],
    "closed_hasdc_comparisons": comparisons,
    "successful_alignment_matches": [{"index": int(i), "name": n, "alpha": a == "true",
                                       "structural": b == "true"} for i, n, a, b in matches],
    "raw_alignment_completed": "PAIR_RETAINED " in text,
    "post_alignment_expected_emitted": "RAW_EXPECTED_BEGIN\n" in text,
    "gap_diagnostics": gap, "binder_bundle": str(bundle_path),
    "binder_bundle_sha256": sha(bytes(bundle)), "binder_bundle_bytes": len(bundle),
    "capture_context": str(context_path), "capture_context_sha256": sha(context_path.read_bytes()),
    "postprocessing_boundary": "Mechanical raw DAG structural comparisons only, identical closed "
                               "binder ordinal contexts; no normalization, rebinding or Lean execution.",
}
output = destination / "RAW_CAPTURE_PROJECTION.json"
output.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
print(json.dumps({"projection": str(output), "raw_graph_count": len(graphs),
                  "w_head_counts": counts, "closed_hasdc_comparisons": comparisons,
                  "raw_alignment_completed": result["raw_alignment_completed"],
                  "gap_diagnostics": gap}, ensure_ascii=False, indent=2))
