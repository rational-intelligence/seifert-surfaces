#!/usr/bin/env python3
"""Validate the exact fixed actual-common kernel audit; successful process exit is insufficient."""
from __future__ import annotations
import argparse
from collections import Counter, defaultdict, deque
import hashlib
import json
from pathlib import Path
import sys

MANIFEST_SHA256 = '50941714bb5f1466d2bf1468be90c0a5ae76f2a51e996d22e36b14ae5a9bf2de'
ROLE_COUNTS = {'replay':318,'safe':143,'family':32,'partial':8,'capture':3,'whole_original':1,'graph':2}

def canonical(value):
    return json.dumps(value,sort_keys=True,separators=(',',':'))

def key(record):
    return record.get('role'),canonical(record.get('name')),record.get('source')

def validate(base: Path, results: Path, boundary: Path, manifest_path: Path):
    errors=[]
    def require(condition,message):
        if not condition:errors.append(message)
    def check_failure_values(value,path):
        if isinstance(value,dict):
            for k,v in value.items():
                require(k!='FAIL',f'{path}: explicit FAIL result')
                check_failure_values(v,f'{path}.{k}')
        elif isinstance(value,list):
            for i,v in enumerate(value):check_failure_values(v,f'{path}[{i}]')
        elif isinstance(value,str):
            require(not value.startswith('FAIL'),f'{path}: {value[:160]}')
    raw=manifest_path.read_bytes()
    require(hashlib.sha256(raw).hexdigest()==MANIFEST_SHA256,'expected manifest hash mismatch')
    if errors:return {'status':'FAIL','errors':errors}
    manifest=json.loads(raw)
    require(manifest['expected_total']==507 and manifest['expected_role_counts']==ROLE_COUNTS,'manifest fixed scope mismatch')
    expected=manifest['records']
    require(len(expected)==507 and dict(Counter(r['role'] for r in expected))==ROLE_COUNTS,'expected record coverage mismatch')
    require(len(manifest['approved_two_theorem_choices'])==2,'two theorem choice boundary mismatch')
    require(sum('operative_equality' in r['pass_fields'] for r in expected if r['role']=='safe')==48,'expected safe operative coverage mismatch')
    for filename,digest in manifest['required_artifact_sha256'].items():
        p=base/filename
        require(p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==digest,f'fixed artifact hash mismatch: {filename}')
    records=[json.loads(line) for line in results.read_text().splitlines() if line.strip()]
    require(len(records)==507,f'expected 507 results, got {len(records)}')
    counts=Counter(r.get('role') for r in records)
    require(dict(counts)==ROLE_COUNTS,f'role coverage mismatch: {dict(counts)}')
    queues=defaultdict(deque)
    for r in expected:queues[key(r)].append(r)
    choices={canonical(n) for n in manifest['approved_two_theorem_choices']}
    safe_operative=0
    for i,record in enumerate(records):
        location=f'record {i} {record.get("role")} {canonical(record.get("name"))}'
        check_failure_values(record,location)
        queue=queues[key(record)]
        if not queue:
            errors.append(f'{location}: unexpected or excessive record identity')
            continue
        required=queue.popleft()
        if 'actual_name' in required:
            require(record.get('actual_name')==required['actual_name'],f'{location}: actual target identity mismatch')
        for field in required['true_fields']:
            require(record.get(field) is True,f'{location}: {field} must be boolean true')
        for field in required['pass_fields']:
            require(record.get(field)=='PASS',f'{location}: {field} must be PASS')
        if record['role']=='safe' and 'operative_equality' in required['pass_fields']:
            safe_operative+=record.get('operative_equality')=='PASS'
        if required.get('replay_body_identity_or_exact_approved_choice'):
            approved=canonical(record['name']) in choices
            require(record.get('approved_two_theorem_choice') is approved,f'{location}: exact two-theorem choice flag mismatch')
            body=record.get('body_literal_identity')
            require(type(body) is bool,f'{location}: literal body identity result missing')
            require(body is True or approved,f'{location}: unapproved literal replay body change')
        if 'recursor_rule_count' in required:
            rules=record.get('recursor_rules')
            require(isinstance(rules,list) and len(rules)==required['recursor_rule_count'],f'{location}: full recursor rule coverage mismatch')
            if isinstance(rules,list):
                for j,rule in enumerate(rules):
                    require(rule.get('ctor_fields_exact') is True,f'{location} rule {j}: constructor/fields mismatch')
                    require(rule.get('full_rule_rhs_defeq')=='PASS',f'{location} rule {j}: full RHS equality not PASS')
    missing=sum(len(queue) for queue in queues.values())
    require(missing==0,f'{missing} exact expected record identities missing')
    require(safe_operative==48,f'expected 48 safe operative equality PASS, got {safe_operative}')
    boundary_record=json.loads(boundary.read_text())
    check_failure_values(boundary_record,'safe partial boundary')
    require(boundary_record.get('scope')==manifest['boundary_scope'],'boundary actual MainTheorems scope mismatch')
    require(Counter(canonical(n) for n in boundary_record.get('partial_names',[]))==Counter(canonical(n) for n in manifest['partial_names']),'boundary exact eight partial names mismatch')
    count=boundary_record.get('safe_declarations_scanned')
    require(type(count) is int and count>0,'complete safe expression scan count missing/empty')
    require(boundary_record.get('incoming_safe_expression_references')==[],'safe expression references to partial implementations present or scan result missing')
    return {'status':'FAIL' if errors else 'PASS','expected_records':507,'actual_records':len(records),'role_counts':dict(counts),'safe_operative_equality_PASS':safe_operative,'safe_declarations_scanned':count,'errors':errors,'manifest_sha256':MANIFEST_SHA256,'results_sha256':hashlib.sha256(results.read_bytes()).hexdigest(),'boundary_sha256':hashlib.sha256(boundary.read_bytes()).hexdigest()}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parent)
    parser.add_argument('--results',type=Path)
    parser.add_argument('--boundary',type=Path)
    parser.add_argument('--manifest',type=Path)
    parser.add_argument('--receipt',type=Path)
    args=parser.parse_args()
    try:
        receipt=validate(args.base,args.results or args.base/'ACTUAL_COMMON_KERNEL_RESULTS.jsonl',args.boundary or args.base/'ACTUAL_COMMON_SAFE_PARTIAL_BOUNDARY.json',args.manifest or args.base/'ACTUAL_COMMON_EXPECTED_MANIFEST.json')
    except (OSError,ValueError,KeyError,TypeError,AttributeError) as exc:
        receipt={'status':'FAIL','errors':[f'{type(exc).__name__}: {exc}']}
    if args.receipt:args.receipt.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,sort_keys=True))
    return 0 if receipt['status']=='PASS' else 1

if __name__=='__main__':sys.exit(main())
