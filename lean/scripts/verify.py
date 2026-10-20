"""Build and audit the complete distributed project; optionally replay selected modules."""
from pathlib import Path
from datetime import datetime, timezone
from zoneinfo import ZoneInfo
import argparse,hashlib,json,os,re,subprocess,time

ROOT=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(name):return json.loads((ROOT/name).read_text())
def dump(p,data):p.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--cache',action='store_true',help='obtain the pinned upstream Mathlib cache')
    ap.add_argument('--replay',action='store_true',help='independently replay the listed result and supporting modules')
    ap.add_argument('--incremental',action='store_true',help='allow existing project proof objects and record their reuse')
    args=ap.parse_args();inputs=read('verification/BUILD_INPUTS.json')
    actual_sources={str(p.relative_to(ROOT)) for p in ROOT.rglob('*.lean') if '.lake'not in p.parts}
    if actual_sources!=set(inputs['lean_sources']):raise SystemExit('The proof-source inventory differs from the release.')
    for name,digest in inputs['source_sha256'].items():
        if not(ROOT/name).is_file()or sha(ROOT/name)!=digest:raise SystemExit('Release input differs: '+name)
    old=list((ROOT/'.lake/build').rglob('*.olean'))
    if old and not args.incremental:raise SystemExit('Fresh verification requires an empty project build directory; --incremental permits recorded reuse.')
    start=datetime.now(timezone.utc);out=ROOT/'verification/reproduction'/start.strftime('%Y%m%dT%H%M%SZ');out.mkdir(parents=True,exist_ok=False)
    env=os.environ.copy();env.setdefault('LEAN_NUM_THREADS','2');env['LAKE_ARTIFACT_CACHE']='false'
    commands=[]
    def run(cmd,name):
        began=datetime.now(timezone.utc)
        with(out/name).open('w')as log:p=subprocess.run(cmd,cwd=ROOT,env=env,stdout=log,stderr=subprocess.STDOUT)
        commands.append({'command':cmd,'exit_code':p.returncode,'log':name,'started_utc':began.isoformat(),'completed_utc':datetime.now(timezone.utc).isoformat()});dump(out/'COMMANDS.json',commands)
        if p.returncode:raise SystemExit('Check failed; see '+str(out/name))
    if args.cache:run(['lake','exe','cache','get'],'dependency_cache.log')
    for i in range(0,len(inputs['module_order']),2):
        run(['lake','build']+['+'+n+':olean'for n in inputs['module_order'][i:i+2]],'source_%03d.log'%(i//2+1))
    run(['lake','build','MainPaperAudit','SupplementAudit'],'default_targets.log')
    run(['lake','env','lean','MainPaperAudit.lean'],'main_audit.log')
    run(['lake','env','lean','SupplementAudit.lean'],'supplement_audit.log')
    inventories={};axiom_sets={}
    for prefix,logname,key in [('PAPER','main_audit.log','main'),('SUPPLEMENT','supplement_audit.log','supplement')]:
        text=(out/logname).read_text();statements=dict(re.findall(prefix+r'_STATEMENT_BEGIN (\S+)\n(.*?)\n'+prefix+r'_STATEMENT_END',text,re.S))
        axioms={n:[a.strip()for a in xs.split(',')if a.strip()]for n,xs in re.findall(prefix+r'_AXIOM_RECEIPT (\S+) \[([^]]*)\]',text)}
        if statements!=read('verification/'+key.upper()+'_ELABORATED_STATEMENTS.json'):raise SystemExit(key+' declaration types differ from the saved reference.')
        if statements.keys()!=axioms.keys():raise SystemExit(key+' axiom inventory is incomplete.')
        if any(set(xs)-{'propext','Classical.choice','Quot.sound'}for xs in axioms.values()):raise SystemExit('Unsupported '+key+' axiom.')
        inventories[key]=statements;axiom_sets[key]=axioms;dump(out/(key.upper()+'_ELABORATED_STATEMENTS.json'),statements);dump(out/(key.upper()+'_TRANSITIVE_AXIOMS.json'),axioms)
    text=(out/'supplement_audit.log').read_text();m=re.search(r'WHOLE_RELEASE_AXIOMS \[([^]]*)\]',text)
    if not m:raise SystemExit('Whole retained mathematical declaration audit is missing.')
    whole_axioms=[x.strip()for x in m[1].split(',')if x.strip()]
    if set(whole_axioms)-{'propext','Classical.choice','Quot.sound'}:raise SystemExit('Unsupported whole-release axiom.')
    count=int(re.search(r'WHOLE_RELEASE_PROJECT_DECLARATIONS (\d+)',text)[1])
    pins={}
    for p in read('lake-manifest.json')['packages']:
        head=subprocess.check_output(['git','-C',str(ROOT/'.lake/packages'/p['name']),'rev-parse','HEAD'],text=True).strip()
        if head!=p['rev']:raise SystemExit('Dependency pin differs: '+p['name'])
        pins[p['name']]=head
    replayed=[]
    if args.replay:
        for i in range(0,len(inputs['replay_modules']),2):
            name='replay_%03d.log'%(i//2+1);run(['lake','env','leanchecker','-v']+inputs['replay_modules'][i:i+2],name)
            replayed+=re.findall(r'^replaying (\S+)',(out/name).read_text(),re.M)
        if set(inputs['replay_modules'])-set(replayed):raise SystemExit('Incomplete requested kernel replay.')
    objroot=ROOT/'.lake/build/lib/lean';objects={str(p.relative_to(objroot)):sha(p)for p in objroot.rglob('*.olean')}
    if set(objects)!={n.replace('.','/')+'.olean'for n in inputs['module_order']}:raise SystemExit('Project object inventory differs from the distributed module inventory.')
    dump(out/'OBJECT_SHA256.json',objects);finish=datetime.now(timezone.utc)
    summary={'status':'PASS','started_utc':start.isoformat(),'completed_utc':finish.isoformat(),'completed_America_Chicago':finish.astimezone(ZoneInfo('America/Chicago')).isoformat(),'fresh_project_objects':not old,'existing_project_objects_at_start':len(old),'source_modules':len(inputs['module_order']),'project_objects':len(objects),'main_declaration_checks':len(inventories['main']),'supplement_declaration_checks':len(inventories['supplement']),'distinct_audited_declarations':len(set(inventories['main'])|set(inventories['supplement'])),'whole_retained_mathematical_declarations':count,'whole_retained_mathematical_axioms':sorted(whole_axioms),'dependency_pins':pins,'replayed_modules':sorted(set(replayed)),'full_upstream_rebuild':False,'full_upstream_kernel_replay':False,'complete_formalization_of_every_printed_supplementary_statement':False,'source_sha256':inputs['source_sha256']}
    dump(out/'SUMMARY.json',summary);print(json.dumps({k:v for k,v in summary.items()if k not in['source_sha256','dependency_pins','replayed_modules']},indent=2))

if __name__=='__main__':main()
