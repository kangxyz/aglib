"""Small native recipe builder using the existing task dictionary interface."""
from pathlib import Path

from .build import native_targets
from .state import digest


def native_recipe(root, directory, *, source_checks=(), prepare=(), provider_gate=None,
                  root_workspace=None, clients=(), exports=(), phase='check'):
    """Order accepted groups, leaving graph scheduling to Lake.

    Workspace fields: id, cwd, modules (bare names), selection (module/library),
    checks (existing task dictionaries), and optional build/identity_modules.
    `exports` is an ordered list of workspace ids; its first member is primary.
    One optional provider gate precedes the root graph. It is a workspace group,
    not a per-module scheduler. Root and client groups use their own Lake cwd.
    """
    root, directory = Path(root).resolve(), Path(directory).resolve()
    if phase not in ('source', 'native', 'check'):
        raise ValueError('Unknown native recipe phase: ' + phase)
    result, seen, workspaces = [], set(), set()

    def append(task, cwd=root):
        task = dict(task)
        task.setdefault('cwd', str(cwd))
        task['cwd'] = str((root / task['cwd']).resolve())
        task.setdefault('kind', 'process')
        if not Path(task['cwd']).is_relative_to(root):
            raise ValueError('Recipe workspace escaped its repository')
        # Same command alone does not establish redundant check semantics.
        key = digest({k: v for k, v in task.items() if k != 'id'})
        if key not in seen:
            result.append(task)
            seen.add(key)

    if phase in ('source', 'check'):
        for task in source_checks:
            append(dict(task, native=False))
    if phase == 'source':
        return result
    for task in prepare:
        append(dict(task, native=True))

    def workspace(group):
        if not group:
            return
        name = group['id']
        if name in workspaces:
            raise ValueError('Duplicate recipe workspace id: ' + name)
        workspaces.add(name)
        cwd = (root / group.get('cwd', '.')).resolve()
        modules = list(dict.fromkeys(group.get('modules', ())))
        selection = group.get('selection', 'module')
        selectors = native_targets(modules, selection)
        for task in group.get('before', ()):
            append(task, cwd)
        if group.get('build_task') is not None:
            task = dict(group['build_task'])
            task.setdefault('cwd', str(cwd))
            if name in exports:
                mapping = directory / (name.replace('/', '-') + '-outputs.jsonl')
                task.update(mapping=str(mapping), export_order=list(exports).index(name), export_label=name)
                task['command'] = [*task['command'], '-o', str(mapping)]
            append(task, cwd)
        elif modules and group.get('build', True):
            command = ['lake', '--rehash', 'build', *selectors]
            task = {'id': name + '/build', 'kind': 'build', 'cwd': str(cwd),
                    'command': command, 'modules': modules, 'build_selection': selection}
            if name in exports:
                mapping = directory / (name.replace('/', '-') + '-outputs.jsonl')
                task.update(mapping=str(mapping), export_order=list(exports).index(name),
                            export_label=name)
                task['command'] += ['-o', str(mapping)]
            if group.get('identity_modules'):
                task['identity_modules'] = group['identity_modules']
            append(task)
        elif name in exports:
            raise ValueError('Export workspace requires a native build: ' + name)
        if any(task.get('kind') == 'check' and not task.get('input_boundary')
               for task in group.get('checks', ())):
            append({'id': name + '/environment', 'kind': 'environment', 'cwd': str(cwd),
                    'command': ['lake', 'env', 'printenv', 'LEAN_PATH'],
                    'environment_output': str(directory / (name.replace('/', '-') + '-search.txt'))})
        for task in group.get('checks', ()):
            append(task, cwd)

    workspace(provider_gate)
    workspace(root_workspace)
    for group in clients:
        workspace(group)
    if set(exports) - workspaces:
        raise ValueError('Unknown export workspace: ' + ', '.join(sorted(set(exports) - workspaces)))
    return result
