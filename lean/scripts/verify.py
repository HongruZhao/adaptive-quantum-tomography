"""Reproduce the release source, statement, axiom and selected kernel checks."""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, json, os, re, subprocess, time

ROOT = Path(__file__).resolve().parents[1]
INPUTS = json.loads((ROOT/'verification/BUILD_INPUTS.json').read_text())
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cache', action='store_true', help='fetch the pinned mathlib cache')
    parser.add_argument('--replay', action='store_true', help='replay the selected current-paper modules')
    parser.add_argument('--incremental', action='store_true', help='allow existing project objects')
    args = parser.parse_args()
    for name, expected in INPUTS['source_sha256'].items():
        if sha(ROOT/name) != expected:
            raise SystemExit('Release source differs: '+name)
    old_objects = list((ROOT/'.lake/build').rglob('*.olean'))
    if old_objects and not args.incremental:
        raise SystemExit('Use a clean checkout for a fresh run, or explicitly add --incremental.')
    out = ROOT/'verification/reproduction'/datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')
    out.mkdir(parents=True, exist_ok=False)
    env = os.environ.copy()
    env.setdefault('LEAN_NUM_THREADS','2')
    commands = []
    start = time.monotonic()
    def run(command, filename):
        with (out/filename).open('w') as log:
            p = subprocess.run(command, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT)
        commands.append({'command':command,'exit_code':p.returncode,'log':filename})
        (out/'COMMANDS.json').write_text(json.dumps(commands,indent=2)+'\n')
        if p.returncode:
            raise SystemExit('Check failed: '+str(out/filename))
    if args.cache:
        run(['lake','exe','cache','get'],'dependency_cache.log')
    for i in range(0,len(INPUTS['module_order']),4):
        run(['lake','build']+['+'+n+':olean' for n in INPUTS['module_order'][i:i+4]],
            'source_%03d.log' % (i//4+1))
    run(['lake','build','MainPaper','MainPaperAudit'],'selected_targets.log')
    run(['lake','env','lean','MainPaperAudit.lean'],'statement_audit.log')
    text = (out/'statement_audit.log').read_text()
    statements = dict(re.findall(r'PAPER_STATEMENT_BEGIN (\S+)\n(.*?)\nPAPER_STATEMENT_END',text,re.S))
    axioms = {n:[a.strip() for a in xs.split(',') if a.strip()]
              for n,xs in re.findall(r'PAPER_AXIOM_RECEIPT (\S+) \[([^]]*)\]',text)}
    expected = json.loads((ROOT/'verification/EXPECTED_DECLARATIONS.json').read_text())
    if set(expected) != statements.keys() or statements.keys() != axioms.keys():
        raise SystemExit('The selected statement inventory differs from the release.')
    expected_types = json.loads((ROOT/'verification/ELABORATED_STATEMENTS.json').read_text())
    if statements != expected_types:
        raise SystemExit('A selected elaborated declaration type differs from the saved reference.')
    if any(set(xs)-{'propext','Classical.choice','Quot.sound'} for xs in axioms.values()):
        raise SystemExit('A selected declaration uses an unsupported axiom.')
    pins = {}
    for package in json.loads((ROOT/'lake-manifest.json').read_text())['packages']:
        head = subprocess.check_output(['git','-C',str(ROOT/'.lake/packages'/package['name']),
                                        'rev-parse','HEAD'],text=True).strip()
        if head != package['rev']:
            raise SystemExit('Dependency revision differs: '+package['name'])
        pins[package['name']] = head
    replayed = []
    if args.replay:
        modules=INPUTS['replay_modules']
        for i in range(0,len(modules),3):
            filename='replay_%02d.log' % (i//3+1)
            run(['lake','env','leanchecker','-v']+modules[i:i+3],filename)
            replayed += re.findall(r'^replaying (\S+)',(out/filename).read_text(),re.M)
        if not set(modules) <= set(replayed):
            raise SystemExit('Incomplete selected kernel replay.')
    objects={str(p.relative_to(ROOT/'.lake/build/lib/lean')):sha(p)
             for p in (ROOT/'.lake/build/lib/lean').rglob('*.olean')}
    for filename,data in [('ELABORATED_STATEMENTS.json',statements),('TRANSITIVE_AXIOMS.json',axioms),
                          ('OBJECT_SHA256.json',objects)]:
        (out/filename).write_text(json.dumps(data,indent=2)+'\n')
    summary={'status':'PASS','checked_utc':datetime.now(timezone.utc).isoformat(),
             'seconds':time.monotonic()-start,'fresh_project_objects':not old_objects,
             'project_modules':len(INPUTS['module_order']),'selected_declarations':len(statements),
             'selected_axioms_standard_only':True,'dependency_pins':pins,
             'replayed_modules':sorted(set(replayed)),
             'whole_project_dependency_closure_replayed':False}
    (out/'SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))

if __name__=='__main__':
    main()
