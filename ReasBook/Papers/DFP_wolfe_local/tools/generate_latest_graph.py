#!/usr/bin/env python3
import argparse, hashlib, html, json, re
from pathlib import Path

RESULTS = [
 ("latest-direction-update","Lemma 1","Polar direction update","lem:polar-direction-update","construction",["DFP.Polar.General.Parameters.matrix_step"],[]),
 ("latest-endpoint-wolfe","Lemma 2","Polar endpoint Wolfe ratios","lem:polar-endpoint-wolfe","construction",["DFP.Polar.General.WolfeRatios.sourceStrongWolfe_of_phaseMargins"],["latest-direction-update"]),
 ("latest-realization","Proposition 3","Polar DFP realization","prop:polar-realization","construction",["DFP.Polar.General.PlanarCounterexample.existsSourceCertificate"],["latest-direction-update","latest-endpoint-wolfe"]),
 ("latest-limiting-cycle","Lemma 4","Limiting two-cycle","lem:polar-limiting-cycle","construction",["DFP.Polar.General.cycleMatchingEven","DFP.Polar.General.cycleMatchingOdd"],["latest-realization"]),
 ("latest-parameter-choice","Lemma 5","Admissible parameter choice","lem:polar-parameter-choice","construction",["DFP.Polar.General.strictWolfeBaseExists"],["latest-limiting-cycle"]),
 ("latest-cycle-estimates","Lemma 6","Two-cycle estimates","lem:polar-cycle-estimates","construction",["DFP.Polar.General.Continuation.existsTrajectoryBounds"],["latest-limiting-cycle","latest-parameter-choice"]),
 ("latest-continuation","Lemma 7","Infinite polar continuation","lem:polar-continuation","construction",["DFP.Polar.General.Continuation.existsContinuationEstimates"],["latest-cycle-estimates"]),
 ("latest-geometry","Lemma 8","Polar geometry and separation","lem:polar-geometry","construction",["DFP.Polar.General.ActualGeometry.existsSourceGeometry"],["latest-continuation"]),
 ("latest-interpolation","Lemma 9","Explicit polar interpolation","lem:polar-interpolation","construction",["DFP.Polar.General.Objective.existsSourceObjectiveData"],["latest-geometry"]),
 ("latest-main","Theorem 10","Strong-Wolfe counterexample","thm:main","main",["DFPWolfe.Latest.main","DFPWolfe.Latest.mainWithSource","DFPWolfe.Latest.mainWithSequenceProperties","DFPWolfe.Latest.not_globalWeakWolfeConvergenceAt","DFPWolfe.Latest.not_levelSetGlobalWeakWolfeConvergenceAt"],["latest-continuation","latest-geometry","latest-interpolation"]),
 ("latest-identity","Corollary 11","Identity initialization","cor:identity-initialization","main",["DFPWolfe.Latest.identityInitialization","DFPWolfe.Latest.identityInitializationQuantitative"],["latest-main"]),
 ("latest-degeneration","Lemma 12","Planar secant degeneration","lem:planar-degeneration","convergence",["DFPWolfe.Latest.planarDegeneration"],[]),
 ("latest-convergence","Theorem 13","Planar convergence","thm:planar-convergence","main",["DFPWolfe.Latest.planarConvergenceCases"],["latest-degeneration"]),
]
FILES = {
 "DFP.Polar.General.Parameters.matrix_step":"ReasLib/Optimization/DFP/Polar/General/PhysicalRecurrence.lean",
 "DFP.Polar.General.WolfeRatios.sourceStrongWolfe_of_phaseMargins":"ReasLib/Optimization/DFP/Polar/General/WolfeRatios.lean",
 "DFP.Polar.General.PlanarCounterexample.existsSourceCertificate":"ReasLib/Optimization/DFP/Polar/General/PlanarCounterexample.lean",
 "DFP.Polar.General.cycleMatchingEven":"ReasLib/Optimization/DFP/Polar/General/CycleFamily.lean",
 "DFP.Polar.General.cycleMatchingOdd":"ReasLib/Optimization/DFP/Polar/General/CycleFamily.lean",
 "DFP.Polar.General.strictWolfeBaseExists":"ReasLib/Optimization/DFP/Polar/General/CycleFamily.lean",
 "DFP.Polar.General.Continuation.existsTrajectoryBounds":"ReasLib/Optimization/DFP/Polar/General/Continuation.lean",
 "DFP.Polar.General.Continuation.existsContinuationEstimates":"ReasLib/Optimization/DFP/Polar/General/Continuation.lean",
 "DFP.Polar.General.ActualGeometry.existsSourceGeometry":"ReasLib/Optimization/DFP/Polar/General/ActualGeometry.lean",
 "DFP.Polar.General.Objective.existsSourceObjectiveData":"ReasLib/Optimization/DFP/Polar/General/Objective.lean",
 "DFPWolfe.Latest.main":"DFPWolfe/Latest/Main.lean",
 "DFPWolfe.Latest.mainWithSource":"DFPWolfe/Latest/Main.lean",
 "DFPWolfe.Latest.mainWithSequenceProperties":"DFPWolfe/Latest/Sequences.lean",
 "DFPWolfe.Latest.not_globalWeakWolfeConvergenceAt":"DFPWolfe/Latest/Main.lean",
 "DFPWolfe.Latest.not_levelSetGlobalWeakWolfeConvergenceAt":"DFPWolfe/Latest/Main.lean",
 "DFPWolfe.Latest.identityInitialization":"DFPWolfe/Latest/Main.lean",
 "DFPWolfe.Latest.identityInitializationQuantitative":"DFPWolfe/Latest/Main.lean",
 "DFPWolfe.Latest.planarDegeneration":"DFPWolfe/Latest/SecantDegeneration.lean",
 "DFPWolfe.Latest.planarConvergenceCases":"DFPWolfe/Latest/PlanarConvergence.lean",
}
def locate(path, short):
 lines=path.read_text().splitlines(keepends=True)
 pat=re.compile(r"\b(?:theorem|lemma|def)\s+"+re.escape(short)+r"\b")
 for i,line in enumerate(lines):
  if pat.search(line):
   end=min(len(lines),i+24)
   for j in range(i+1,min(len(lines),i+80)):
    if re.match(r"\s*(?:theorem|lemma|def)\s+[A-Za-z0-9_'.]+",lines[j]): end=j; break
   return i+1,''.join(lines[i:end])
 raise ValueError((path,short))
def block_html(latex):
 text=re.sub(r"\\label\{[^}]+\}","",latex)
 text=re.sub(r"\\begin\{[^}]+\}|\\end\{[^}]+\}","",text)
 text=re.sub(r"\\(?:ref|eqref)\{([^}]+)\}",r"[\1]",text)
 text=re.sub(r"\s+"," ",text).strip()
 return '<p><code>'+html.escape(text)+'</code></p>'
def main():
 ap=argparse.ArgumentParser(); ap.add_argument('--manuscript',type=Path,required=True); ap.add_argument('--source-root',type=Path,required=True); ap.add_argument('--commit',required=True); a=ap.parse_args()
 s=a.manuscript.read_text(); blocks=list(re.finditer(r"\\begin\{(theorem|lemma|corollary|proposition)\}([\s\S]*?)\\end\{\1\}",s))
 if len(blocks)!=13: raise SystemExit(f'expected 13 blocks, got {len(blocks)}')
 labels=[re.findall(r"\\label\{([^}]+)\}",b.group(2))[0] for b in blocks]
 if labels != [r[3] for r in RESULTS]: raise SystemExit(f'label order mismatch: {labels}')
 digest=hashlib.sha256(a.manuscript.read_bytes()).hexdigest(); items=[]
 for idx,(item_id,label,title,tex,section,declarations,deps) in enumerate(RESULTS):
  b=blocks[idx]; latex=b.group(2).strip(); start=s.count('\n',0,b.start())+1; end=s.count('\n',0,b.end())+1; related=[]; excerpts=[]
  for decl in declarations:
   path=a.source_root/FILES[decl]; line,code=locate(path,decl.rsplit('.',1)[1]); rel=path.relative_to(a.source_root).as_posix(); related.append({'declaration':decl,'file':rel,'line':line}); excerpts.append({'declaration':decl,'file':rel,'line':line,'leanCode':code})
  items.append({'id':item_id,'label':label,'title':title,'type':label.split()[0],'section':section,'declaration':declarations[0],'file':related[0]['file'],'line':related[0]['line'],'endLine':related[0]['line']+max(1,excerpts[0]['leanCode'].count('\n')),'statement':latex,'statementHtml':block_html(latex),'statementSha256':hashlib.sha256(latex.encode()).hexdigest(),'statementSource':{'manuscript':'20251117-DFP/arXiv.tex','manuscriptSha256':digest,'startLine':start,'endLine':end},'texLabel':tex,'paperMapping':'Paper-numbered result with reviewed Lean declarations and source links.','relatedDeclarations':related,'leanExcerpts':excerpts,'dependencies':deps,'statementDependencies':deps,'proofDependencies':[],'dependencyEvidence':'curated','sourceSha256':hashlib.sha256((a.source_root/FILES[declarations[0]]).read_bytes()).hexdigest()})
 sections=[{'id':'construction','label':'Polar construction','short':'Construction','color':'#23745d','wash':'#e4f2ed'},{'id':'main','label':'Main results','short':'Main results','color':'#315fb5','wash':'#e9effa'},{'id':'convergence','label':'Convergence','short':'Convergence','color':'#7654a6','wash':'#eee8f8'}]
 project={'id':'DFP_wolfe_local','title':'DFP 20251117 polar proof','kind':'papers','branch':'latest-20251117','commit':a.commit,'repository':'https://github.com/imathwy/DFP_wolfe_local','sourceRoot':''}
 gen={'mode':'curated-paper-numbered','rootModule':'DFPWolfe.Latest.Paper','compiledItemCount':13,'sourceInventoryItemCount':13,'sourceOnlyItemCount':0,'mergedItemCount':13,'dependencyCoverage':'reviewed-paper-dependencies','dependencyModel':'paper-order-v1','scope':'20251117-DFP/arXiv.tex; shared amsthm counter gives Lemmas 1–2, Proposition 3, Lemmas 4–9, Theorem 10, Corollary 11, Lemma 12 and Theorem 13.','sourceSnapshot':a.commit,'manuscriptSha256':digest,'numbering':'Shared theorem counter in source order; 13 theorem-like results.','edges':sum(len(x['dependencies']) for x in items),'nodes':13}
 data={'schemaVersion':2,'project':project,'sections':sections,'items':items,'generation':gen}; out=a.source_root/'theorem-map/latest'; out.mkdir(parents=True,exist_ok=True)
 for name,obj in [('data.json',data),('overview-data.json',{**data,'generation':{**gen,'view':'paper-numbered','selection':'All theorem-like results in 20251117-DFP/arXiv.tex, in shared-counter order.'}}),('metadata.json',{'schemaVersion':1,'project':project,'nodes':13,'edges':gen['edges'],'generation':gen}),('release-context.json',{'schemaVersion':1,'project':project,'generation':gen})]: (out/name).write_text(json.dumps(obj,ensure_ascii=False,indent=2)+'\n')
 paper={'schemaVersion':1,'manuscriptName':'20251117-DFP/arXiv.tex','manuscriptSha256':digest,'referenceNumbering':'Shared amsthm theorem counter; theorem-like blocks are numbered in source order.','formulaCount':0,'rendering':'Verbatim statement excerpts; raw LaTeX preserved in a safe code block for reproducibility.','items':[{'id':x['id'],'label':x['label'],'texLabel':x['texLabel'],'statementLatex':x['statement'],'statementSha256':x['statementSha256'],'sourceStartLine':x['statementSource']['startLine'],'sourceEndLine':x['statementSource']['endLine'],'references':{},'equationNumbers':{},'statementHtml':x['statementHtml'],'formulaCount':0} for x in items]}
 (out/'paper-statements.json').write_text(json.dumps(paper,ensure_ascii=False,indent=2)+'\n'); print(json.dumps({'nodes':13,'edges':gen['edges'],'manuscriptSha256':digest,'labels':labels},ensure_ascii=False))
if __name__=='__main__': main()
