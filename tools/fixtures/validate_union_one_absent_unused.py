#!/usr/bin/env python3
"""Validate exactly 928 present kernel checks plus one reviewed absent unused auxiliary."""
from pathlib import Path
from collections import Counter
import argparse,hashlib,json,sys
MANIFEST_SHA256='40afd9a05123c98adada6197b89c7ffa590643dc277469ddc830f644dbf2af13'
def validate(base,repository,audit_file=None):
    errors=[]
    def require(ok,message):
        if not ok:errors.append(message)
    mp=base/'UNION_ONE_ABSENT_UNUSED_MANIFEST.json';data=mp.read_bytes();require(hashlib.sha256(data).hexdigest()==MANIFEST_SHA256,'fixed applicability manifest SHA mismatch')
    if errors:return {'status':'FAIL','errors':errors}
    m=json.loads(data)
    for filename,digest in m['required_bundle_sha256'].items():
        p=base/filename;require(p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==digest,f'fixed bundle SHA mismatch: {filename}')
    active_audit=audit_file or repository/'tools/audits/AuditCommonUnionLiteralReceiving.lean'
    require(active_audit.is_file() and hashlib.sha256(active_audit.read_bytes()).hexdigest()==m['required_bundle_sha256']['AuditCommonUnionOneAbsentUnusedCandidate.lean'],'executed public audit source SHA mismatch')
    for filename,digest in m['original_provider_source_sha256'].items():
        p=repository/filename;require(p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==digest,f'original provider SOURCE SHA mismatch: {filename}')
    fixture=[json.loads(l) for l in (base/'COMMON_UNION_APPROVED_LITERAL_GUARDS.jsonl').read_text().splitlines() if l]
    resultfile=base/'COMMON_UNION_LITERAL_RECEIVING_KERNEL.jsonl';rs=[json.loads(l) for l in resultfile.read_text().splitlines() if l]
    require(len(fixture)==929 and len(rs)==929,'exact929 total coverage mismatch')
    require(Counter(r.get('name') for r in rs)==Counter(r['name'] for r in fixture),'all929 exact name/multiplicity mismatch')
    absent=present=operative=rules=0
    for i,r in enumerate(rs):
        label=f'row {i} {r.get("name")}'
        if r.get('coverage')=='ABSENT_UNUSED_AUXILIARY':
            absent+=1;require(r.get('name')==m['exact_one_name'],label+': unapproved missing name')
            for k in ['exact_original_source_bindings','both_provider_modules_absent','raw_missing_retained']:require(r.get(k) is True,label+': '+k+' must be true')
            require(r.get('old_type_actual_Main_PASS_claimed') is False,label+': inactive oldtype must not claim Main PASS')
            continue
        present+=1
        require(r.get('name')!=m['exact_one_name'],label+': approved absence changed')
        require(r.get('metadata_dimensions_pass') is True,label+': metadata dimensions not true')
        require(r.get('old_type_selected_current',{}).get('status')=='PASS',label+': full oldtype kernel result not PASS')
        matching=[f for f in fixture if f['name']==r.get('name')]
        hasvalue=all('old_value' in f for f in matching)
        if hasvalue:
            operative+=1
            require(r.get('old_value_typing',{}).get('status')=='PASS',label+': oldbody typing not PASS')
            require(r.get('old_value_current_closed_equality',{}).get('status')=='PASS',label+': operative Eq not PASS')
        elif any('old_value' in f for f in matching):require(False,label+': ambiguous fixture value multiplicity')
        hasrules=all('recursor_rules' in f for f in matching)
        if hasrules:
            counts={len(f['recursor_rules']) for f in matching};check=r.get('recursor_rhs_identities')
            require(len(counts)==1 and isinstance(check,list) and len(check) in counts,label+': complete recursor RHS coverage mismatch')
            if isinstance(check,list):
                rules+=len(check)
                for j,v in enumerate(check):require(v.get('status')=='PASS',label+f': recursor RHS{j} not PASS')
        # No raw FAIL is allowed in the operative present results or classified absence record.
        require('"FAIL"' not in json.dumps(r),label+': raw FAIL in accepted present/absence record')
    require((present,absent,operative,rules)==(928,1,396,39),f'exact scope counter mismatch: present={present}, absent={absent}, operative={operative}, RHS={rules}')
    receiptfile=base/'COMMON_UNION_ONE_ABSENT_UNUSED_RECEIPT.json';receipt=json.loads(receiptfile.read_text())
    for k in ['total_records','present_full_type_PASS','absent_unused_original_auxiliary','operative_closed_equality_PASS','complete_recursor_RHS_PASS','scope']:
        require(receipt.get(k)==m.get(k,929 if k=='total_records' else None),f'coverage receipt {k} mismatch')
    inactive=['anonymous']
    for component in m['exact_one_name'].split('.'):inactive=['str',inactive,component]
    require(receipt.get('inactive_name')==inactive,'exact inactive literal name mismatch')
    require(receipt.get('raw_missing_retained') is True,'raw missing classification not retained')
    require(receipt.get('incoming_type_value_recursor_references')==[],'incoming fulltype/body/recursor refs to unused missing theorem or scan absent')
    scanned=receipt.get('environment_declarations_scanned');require(type(scanned) is int and scanned>0,'complete actual environment scan missing')
    return {'status':'FAIL' if errors else 'PASS','coverage':'928present_full_type_PASS_plus1absent_unused_original_auxiliary','present_full_type_PASS':present,'absent_unused':absent,'operative_closed_equality_PASS':operative,'complete_recursor_RHS_PASS':rules,'environment_declarations_scanned':scanned,'raw929PASS_claimed':False,'errors':errors,'manifest_sha256':MANIFEST_SHA256,'results_sha256':hashlib.sha256(resultfile.read_bytes()).hexdigest(),'receipt_sha256':hashlib.sha256(receiptfile.read_bytes()).hexdigest()}
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--base',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--repository',type=Path,default=Path.cwd());ap.add_argument('--receipt',type=Path);ap.add_argument('--audit-file',type=Path);a=ap.parse_args()
    try:r=validate(a.base,a.repository,a.audit_file)
    except (OSError,ValueError,KeyError,TypeError,AttributeError) as e:r={'status':'FAIL','errors':[f'{type(e).__name__}: {e}']}
    if a.receipt:a.receipt.write_text(json.dumps(r,indent=2)+'\n')
    print(json.dumps(r,sort_keys=True));return 0 if r['status']=='PASS' else 1
if __name__=='__main__':sys.exit(main())
