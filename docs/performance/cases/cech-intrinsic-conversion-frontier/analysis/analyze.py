from pathlib import Path
import hashlib,json,re
S=Path(__file__).resolve().parent
R=S.parents[2]
D=R/'incremental-compiler/diagnostics/cech-profile-6536a791'
if not D.exists():
 D=Path('/Users/kang/Documents/New project/tmp/work/etale-abstract-core-research-20261025/migration/incremental-compiler/diagnostics/cech-profile-6536a791')
delivery=json.loads((D/'delivery.json').read_text());runtime=json.loads((D/'profile.json').read_text())
source=(D/'source.lean').read_text();sha=hashlib.sha256(source.encode()).hexdigest()
assert sha==delivery['source_sha256']=='a9ff484188f60dc58dfe142249bc28ed0cf9fbde1280020dba63d2c5b9a76e8a'
assert hashlib.sha256((D/'Comparison.setup.json').read_bytes()).hexdigest()==delivery['setup_sha256']
assert delivery['profile_invocations']==1 and delivery['preparation_compiler_starts']==0
pat=re.compile(r'([^\[]*)\[([^\]]+)\] \[([0-9.]+)\] (.*)')
namepat=re.compile(r'AlgebraicGeometry\.Scheme\.Cohomology\.([A-Za-z_0-9₀π]+)')
frames=[];stack=[]
with (D/'profile.stdout.log').open() as f:
 for lineno,line in enumerate(f,1):
  m=pat.match(line)
  if not m:continue
  depth=len(m[1]);phase=m[2];msg=m[4].strip()
  while stack and stack[-1]['depth']>=depth:stack.pop()
  owner=next((x['owner'] for x in reversed(stack) if x.get('owner')),None)
  if phase in ['Elab.definition.header','Elab.definition.value','Kernel']:
   n=namepat.search(msg)
   if n:owner=n[1]
  entry={'trace_line':lineno,'phase':phase,'seconds':float(m[3]),'message':msg[:500],
         'owner':owner,'depth':depth}
  stack.append(entry);frames.append(entry)
def loc(name):
 if not name:return None
 p=re.compile(r'^(?:@\[[^\n]*\]\s*)?(?:def|abbrev|theorem|lemma|instance)\s+'+re.escape(name)+r'\b')
 return next((i for i,line in enumerate(source.splitlines(),1) if p.match(line)),None)
def top(phase,n):
 out=[]
 for e in sorted((x for x in frames if x['phase']==phase),key=lambda x:x['seconds'],reverse=True)[:n]:
  out.append({**e,'source_line':loc(e['owner'])})
 return out
result={
 'question':'Dominant declarations/phases in the passed Scheme Comparison a9ff, and whether a bounded existing-proof repair is justified.',
 'source_sha256':sha,'source_path':str(D/'source.lean'),'production_module':runtime['module'],
 'native_run':delivery['native_run'],'setup_kind':delivery['setup_kind'],
 'regenerated_setup_sha256':delivery['setup_sha256'],'original_setup_byte_identity':False,
 'profile_invocations':1,'preparation_compiler_starts':0,'exit_code':delivery['profile_exit_code'],
 'wall_seconds':delivery['wall_seconds'],'native_resource_observation':delivery['native_resource_observation'],
 'trace_bytes':(D/'profile.stdout.log').stat().st_size,'recorded_timed_frames':len(frames),
 'recorded_kernel_frames':sum(x['phase']=='Kernel' for x in frames),
 'top_kernel':top('Kernel',12),'top_elaboration_value':top('Elab.definition.value',8),
 'top_elaboration_header':top('Elab.definition.header',8),'top_instance_search':top('Meta.synthInstance',8),
 'direct_conversion_evidence':[
  {'trace_lines':[142,174],'finding':'The AddEquiv alias compares original Scheme HPrime/Ext expressions over Opens of the Scheme carrier against Opens of X.toTopCat.'},
  {'trace_lines':[179,1130],'finding':'That elaboration conversion descends through the Ext additive structure, Ext.homEquiv, Localization.SmallHom.equiv and equivShrink. These are nested inclusive frames, not per-constant timing.'},
  {'trace_lines':[71175,71220],'finding':'The module-resolution proof synthesizes F.PreservesZeroMorphisms while comparing the sheaf full-subcategory zero dictionary with the preadditive zero dictionary; one observed nested comparison is about2.33s.'}
 ],
 'repair_judgment':[
  {'priority':1,'status':'A bounded existing-proof attempt is justified; not implemented or measured in this diagnostic phase.',
   'scope':['moduleResolution_openKernelSections_surjective','subsingleton_sheafHPrime_of_moduleResolution_sections_exact'],
   'proposal':'Provide the already proved zero-preservation dictionaries at the literal Scheme/module and additive-sheaf category/zero heads, once in the smallest local scope that also covers the theorem headers. Reuse the original sectionsFunctor and SheafOfModules.additiveEvaluation_preservesZeroMorphisms API; do not add hypotheses, new functors or global-priority changes.',
   'support':'Three observed sectionsFunctor/G preservation searches are about5.01–5.04s, with explicit source/target zero-head conversion in the same existing resolution proof. The native evaluation dictionary method is already documented and the precise producer exists.'},
  {'priority':2,'status':'The cohomology-adapter boundary warrants a targeted one-wrapper plus actual scalar-consumer pilot; exact kernel mechanism and cost relocation are unresolved.',
   'scope':['sheafHPrimeTopAddEquiv','moduleHPrimeTopAddEquiv_scalar'],
   'proposal':'Inspect and align the one native site/Ext/additive-structure presentation at this boundary; consider preserving the whole existing generic comparison head rather than reconstructing a second fully annotated AddEquiv type. Keep literal maps, public types up to their required conversion, HPrime/H normalization and the actual scalar consumer. Do not blindly drop result types, replace all defs/abbrevs, or add a universal transport package.',
   'support':'Kernel intervals16.485/16.698s despite very short wrappers, plus the actual elaboration conversion through Ext add-structure/small-Hom machinery. The profile does not prove which constant causes kernel time or that changing presentation would reduce rather than move cost.'}
 ],
 'interpretation_limits':['The641.305s wall time and66.8MB trace describe an instrumented diagnostic, not a matched comparison with the earlier155s ordinary pass or a speedup/regression ratio.',
  'Nested and async timings overlap. No frame sums or wall-time percentages are used.',
  'Large Elab.command/Elab.async intervals may include waiting for async kernel work; the named Kernel frames are reported separately.',
  'No sufficiently labelled import/serialization phase breakdown was observed. Absence of such a frame does not establish zero cost.',
  'No production source changed, no second profile ran, and the settled all-nine native compiler/source-review evidence is unaffected.'],
 'evidence':{'delivery':str(D/'delivery.json'),'runtime':str(D/'profile.json'),'preparation':str(D/'preparation.json'),
             'stdout':str(D/'profile.stdout.log'),'stderr':str(D/'profile.stderr.log'),'setup':str(D/'Comparison.setup.json'),
             'native_receipt':delivery['native_receipt'],'events':delivery['events'],
             'source_archive':delivery['source_archive'],'source_archive_sha256':delivery['source_archive_sha256']},
 'reproduce_analysis':'python3 '+str(Path(__file__).resolve()),
 'remaining_gap':'A source-preserving performance repair and its ordinary changed-input validation are a next assignment, not an achieved speedup or a missing mathematical proof. No further profiling is authorized by this packet.'
}
(S/'result.json').write_text(json.dumps(result,indent=2)+'\n')
print('Top kernel:')
for e in result['top_kernel'][:6]:print(e['owner'],e['source_line'],e['seconds'],e['trace_line'])
print('Top instance search:')
for e in result['top_instance_search'][:5]:print(e['owner'],e['seconds'],e['trace_line'],e['message'][:95])
