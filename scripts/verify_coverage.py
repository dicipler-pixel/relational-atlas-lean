#!/usr/bin/env python3
"""Validate evidence integrity and inventory, not the truth of prose-to-Lean mappings."""
from pathlib import Path
import argparse, collections, copy, hashlib, json, re, zipfile
ROOT=Path(__file__).resolve().parents[1]
DIRECTORY=ROOT/'atlas/coverage'
LOCAL='dicipler-pixel/relational-atlas-lean'
def strip_comments(s):
 out=[];i=0;depth=0
 while i<len(s):
  if s[i:i+2]=='/-':depth+=1;i+=2
  elif depth and s[i:i+2]=='-/':depth-=1;i+=2
  elif not depth and s[i:i+2]=='--':
   j=s.find('\n',i);i=len(s)if j<0 else j
  else:
   if not depth:out.append(s[i])
   elif s[i]=='\n':out.append('\n')
   i+=1
 if depth:raise ValueError('Unclosed Lean comment')
 return ''.join(out)
def names(p):return set(re.findall(r'^\s*(?:protected\s+)?(?:theorem|lemma)\s+([^\s:({\[]+)',strip_comments(p.read_text()),re.M))
def declaration_names(p):
 return set(re.findall(r'^\s*(?:noncomputable\s+)?(?:protected\s+)?(?:theorem|lemma|def)\s+([^\s:({\[]+)',strip_comments(p.read_text()),re.M))
def require(ok,msg):
 if not ok:raise ValueError(msg)
def validate(d,archive=None):
 cards=d['cards'];require([c['id']for c in cards]==[f'B{i}'for i in range(1,208)],'207 ordered unique card IDs required')
 require(d['publication_doi']=='10.5281/zenodo.23590925','Wrong edition DOI')
 require(d['publication_url']=='https://doi.org/'+d['publication_doi'],'DOI URL mismatch')
 require(len(d['source_files'])==2,'Published source provenance missing')
 ext=json.loads((DIRECTORY/'external_sources.json').read_text())
 for e in ext:
  p=ROOT/e['snapshot_path'];raw=p.read_bytes()
  blob=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
  require(blob==e['blob_sha'],'External snapshot mismatch: '+str(p))
 nn=ROOT/'atlas/coverage/external/nonnormality-connection-energy-lean'
 report=json.loads((nn/'verification/report.json').read_text())
 for path in ['NonNormality/SelfCommutator.lean','NonNormality/Holonomy.lean']:
  require(hashlib.sha256((nn/path).read_bytes()).hexdigest()==report['sha256'][path],'Committed verification report hash mismatch')
 config=json.loads((ROOT/'scripts/config.json').read_text());inventory=[];all_local=set()
 for m in config['modules']:
  p=ROOT/m['path'];ns=names(p);all_local|={(m['path'],n)for n in ns}
  s=strip_comments(p.read_text())
  require(not re.search(r'\b(?:sorry|axiom)\b',s),'Local source placeholder/axiom')
  inventory.append(dict(path=m['path'],sha256=hashlib.sha256(p.read_bytes()).hexdigest(),theorems=sorted(ns)))
 require(len(all_local)==config['expected_theorems']==37,'Local theorem inventory changed; review coverage')
 mapped=set()
 for c in cards:
  require(c['source_grade']in {'theorem','derived','measured','conjecture','reading'},'Unrecognized source grade')
  require(c['full_card_certified']is False,'Whole-card proof certification requires a new audited schema')
  require(c['claim']and c['assumptions']and c['source_reference'],'Missing original claim/context: '+c['id'])
  require(re.fullmatch('[a-f0-9]{64}',c['source_sha256'])is not None,'Bad source digest')
  refs=c['proof_references'];expected='local_kernel_mapped'if any(r['repository']==LOCAL for r in refs)else'external_kernel_mapped'if refs else'not_mapped_in_audited_scope'
  require(c['coverage_status']==expected,'Coverage status does not follow references')
  for r in refs:
   p=ROOT/r['snapshot_path'];ns=declaration_names(p)
   require(r['scope']and r['declarations'],'Empty proof scope or names')
   require(set(r['declarations'])<=ns,'Unknown theorem: '+c['id']+' '+str(set(r['declarations'])-ns))
   require(r['url']==f"https://github.com/{r['repository']}/blob/{r['commit']}/{r['path']}",'Unpinned proof URL')
   if r['repository']==LOCAL:mapped|={(r['path'],n)for n in r['declarations']}
   else:require(any(e['repo']==r['repository']and e['path']==r['path']and e['head']==r['commit']and e['snapshot_path']==r['snapshot_path']for e in ext),'External commit provenance mismatch')
 require(mapped==all_local,'Every one of the 37 local declarations needs a ledger mapping')
 if archive:
  require(hashlib.sha256(archive.read_bytes()).hexdigest()==d['source_archive_sha256'],'Published archive SHA mismatch')
  published=next(x for x in d['source_files']if x['key']=='atlas_cards_v7_html.zip')
  require('md5:'+hashlib.md5(archive.read_bytes()).hexdigest()==published['checksum'],'Zenodo archive checksum mismatch')
  with zipfile.ZipFile(archive)as z:
   for c in cards:require(hashlib.sha256(z.read(c['source_file'])).hexdigest()==c['source_sha256'],'Original card checksum mismatch '+c['id'])
 return dict(cards=len(cards),coverage=dict(collections.Counter(c['coverage_status']for c in cards)),source_grades=dict(collections.Counter(c['source_grade']for c in cards)),local_theorems=len(all_local),external_source_snapshots=len(ext),archive_verified=bool(archive),local_inventory=inventory)
def self_test(d):
 cases=[]
 x=copy.deepcopy(d);x['cards'].pop();cases.append(('missing_card',x))
 x=copy.deepcopy(d);next(c for c in x['cards']if c['proof_references'])['proof_references'][0]['declarations'].append('invented_proof');cases.append(('nonexistent_proof',x))
 x=copy.deepcopy(d);x['cards'][0]['full_card_certified']=True;cases.append(('unsupported_whole_card_upgrade',x))
 x=copy.deepcopy(d);x['publication_doi']='10.5281/zenodo.21972561';cases.append(('wrong_edition',x))
 for name,x in cases:
  try:validate(x)
  except ValueError:continue
  raise ValueError('Negative control accepted: '+name)
 return [n for n,_ in cases]
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--source-archive',type=Path);p.add_argument('--self-test',action='store_true');p.add_argument('--output',type=Path);a=p.parse_args()
 d=json.loads((DIRECTORY/'coverage.json').read_text());report=validate(d,a.source_archive)
 if a.self_test:report['rejected_metadata_controls']=self_test(d)
 result=json.dumps(report,indent=2)+'\n'
 if a.output:a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(result)
 print(result)
