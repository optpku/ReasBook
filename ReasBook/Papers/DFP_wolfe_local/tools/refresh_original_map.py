"""Refresh the retained original graph from a checksum-verified compiled export.

Reuses the SDK's private-proof export without another Lean process. Mathematical
sources must be byte-identical to that export's committed source identity.
The original selection, numbering and quoted manuscript statements are retained.
"""
import argparse,hashlib,json,re,subprocess,sys
from bisect import bisect_left
from pathlib import Path

p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--paper',required=True,type=Path);p.add_argument('--sdk-root',required=True,type=Path)
p.add_argument('--evidence',required=True,type=Path);a=p.parse_args()
paper=a.paper.resolve();repo=paper.parents[2];graph=paper/'theorem-map'
sys.path[:0]=[str(a.sdk_root/'src'),str(a.sdk_root.parent/'common/src'),str(paper/'tools')]
from theorem_graph_sdk.analysis import contract_dependencies
from generate_theorem_map import mask_comments
from generate_paper_graph import project_graph,attach_statements,verify
prov=json.loads((a.evidence/'provenance.json').read_text());raw_bytes=(a.evidence/'raw.json').read_bytes()
assert hashlib.sha256(raw_bytes).hexdigest()==prov['rawSha256']
changes=subprocess.check_output(['git','diff',prov['sourceCommit'],'HEAD','--','ReasBook/Papers/DFP_wolfe_local/**/*.lean','ReasBook/Papers/DFP_wolfe_local/*.lean'],cwd=repo,text=True)
assert not changes,'The mathematical sources differ from the compiled export'
raw={r['name']:r for r in json.loads(raw_bytes)}
data=json.loads((graph/'data.json').read_text());heads={};sources={}
pattern=re.compile(r'^[ \t]*(?:@\[[\s\S]*?\]\s*)*(?P<modifiers>(?:(?:private|protected|public|noncomputable)\s+)*)(?P<kind>theorem|lemma)\s+(?P<name>[^\s({:\[=]+)',re.M)
for item in data['items']:
 name=item['declaration'];row=raw[name];assert row['kind']=='theorem'
 file=row['moduleName'].replace('.','/')+'.lean';assert file==item['file']
 source=(paper/file).read_text();sources[file]=source
 if file not in heads:
  heads[file]=[(source.count('\n',0,m.start('kind'))+1,m['name'].strip('«»')) for m in pattern.finditer(mask_comments(source))]
 records=heads[file];i=bisect_left([r[0] for r in records],row['line'])
 line,short=records[i];assert name==short or name.endswith('.'+short)
 item.update(line=line,statement=row['docString'],dependencyEvidence='compiled',sourceSha256=hashlib.sha256(source.encode()).hexdigest())
chosen={r['declaration']:r['id'] for r in data['items']}
for item in data['items']:
 for field in ['statementDependencies','proofDependencies','dependencies']:
  item[field]=sorted(set(contract_dependencies(item['declaration'],raw,chosen,field))-{item['id']})
 assert set(item['dependencies'])==set(item['statementDependencies'])|set(item['proofDependencies'])
commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip()
data['project']['commit']=commit
source_hash=hashlib.sha256(json.dumps({f:hashlib.sha256(t.encode()).hexdigest() for f,t in sorted(sources.items())},sort_keys=True).encode()).hexdigest()
data['generation'].update(compiledItemCount=len(data['items']),sourceInventoryItemCount=len(data['items']),sourceOnlyItemCount=0,mergedItemCount=len(data['items']),dependencyCoverage='complete',sourceSha256=source_hash,compiledExportSourceCommit=prov['sourceCommit'],compiledExportSha256=prov['rawSha256'],selection='Retained original-proof public theorem/lemma inventory, refreshed through compiled private proof bodies; v21 has a separate graph')
(graph/'data.json').write_text(json.dumps(data,indent=2,ensure_ascii=False)+'\n')
metadata=dict(schemaVersion=1,project=data['project'],nodes=len(data['items']),edges=sum(len(r['dependencies']) for r in data['items']),generation=data['generation'])
(graph/'metadata.json').write_text(json.dumps(metadata,indent=2,ensure_ascii=False)+'\n')
(graph/'release-context.json').write_text(json.dumps(dict(schemaVersion=1,project=data['project']),indent=2,ensure_ascii=False)+'\n')
mapping=json.loads((paper/'tools/paper_results.json').read_text());projected=project_graph(data,mapping)
attach_statements(projected,json.loads((graph/'paper-statements.json').read_text()));verify(data,projected)
(graph/'paper-data.json').write_text(json.dumps(projected,indent=2,ensure_ascii=False)+'\n')
code=json.loads((graph/'paper-lean.json').read_text())
for record in code['declarations'].values():
 assert hashlib.sha256((paper/record['file']).read_bytes()).hexdigest()==record['sourceSha256'],record['file']
code['sourceCommit']=commit
(graph/'paper-lean.json').write_text(json.dumps(code,indent=2,ensure_ascii=False)+'\n')
print(json.dumps(dict(nodes=metadata['nodes'],edges=metadata['edges'],numberedNodes=len(projected['items']),sourceCommit=commit)))
