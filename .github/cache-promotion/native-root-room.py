#!/usr/bin/env python3
"""Small resource gate for the existing flat native root-release transport."""
import json
import os
from pathlib import Path
import re
import sys
import tarfile

def check(extra, entries):
    for root in (Path.cwd(), Path(os.environ['RUNNER_TEMP'])):
        s = os.statvfs(root)
        print(json.dumps({'path':str(root),'free_bytes':s.f_bavail*s.f_frsize,
                          'required_extra_bytes':extra+3_000_000_000,
                          'free_inodes':s.f_favail,'required_inodes':entries+100000}))
        if s.f_frsize != 4096 or s.f_bavail*s.f_frsize < extra+3_000_000_000 or s.f_favail < entries+100000:
            raise SystemExit('Native root transport resource gate failed; no cleanup/cold fallback')
    fields = dict(line.split(':',1) for line in Path('/proc/meminfo').read_text().splitlines())
    available = int(fields['MemAvailable'].split()[0])*1024
    if available < 2_000_000_000: raise SystemExit('Insufficient available RAM for root import')

if sys.argv[1] == 'download':
    check(((int(sys.argv[2])+4095)//4096)*4096,2)
elif sys.argv[1] == 'extract':
    names=set(); allocated=0
    with tarfile.open(sys.argv[2],mode='r:') as archive:
        for m in archive:
            name=m.name.removeprefix('./').rstrip('/')
            if m.isdir() and m.name in ('.','./'): continue
            if (not m.isreg() or name in names or not re.fullmatch(
                r'outputs[.]jsonl|producer[.]json|[0-9a-f]{16}([.][A-Za-z0-9_.+-]+)?',name)):
                raise SystemExit('Expected existing native flat regular staging format')
            names.add(name); allocated+=((m.size+4095)//4096)*4096
            if len(names)>2_000_000: raise SystemExit('Native stage entry bound exceeded')
    if not {'outputs.jsonl','producer.json'} <= names: raise SystemExit('Missing root staging metadata')
    # Existing transport tar is already allocated. Cover staging, native artifact
    # copies and map slack. Conventional .lake/build restoration is separately
    # bounded by the trusted producer's measured complete root-build envelope.
    check(3*allocated+len(names)*8192*3,len(names)*3)
elif sys.argv[1] == 'unstage':
    metadata=Path(sys.argv[2]);p=json.loads(metadata.read_text())
    n=p.get('root_build_bytes'); count=p.get('root_build_entries')
    if type(n) is not int or type(count) is not int or n<=0 or count<=0:
        raise SystemExit('Strict cache-only import requires measured root build envelope')
    staged=list(metadata.parent.iterdir())
    allocated=sum(((f.stat().st_size+4095)//4096)*4096 for f in staged)
    check(2*allocated+n+(count+2*len(staged))*8192,count+2*len(staged))
elif sys.argv[1] == 'save':
    # SDK installation allowance before checkout/npm ci; Node action rechecks
    # CAP+reserve after install, and the kernel enforces CAP on all descendants.
    check(10_000_000_000+1_000_000_000,100000)
else: raise SystemExit('Unknown native root resource phase')
