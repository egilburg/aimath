from pathlib import Path
import re,json,hashlib,sys,argparse
parser=argparse.ArgumentParser(description='Compare retained mortality declarations against the original published sources.')
parser.add_argument('original_lean_root',type=Path)
parser.add_argument('refactored_lean_root',type=Path)
parser.add_argument('--mapping',type=Path,required=True)
parser.add_argument('--output',type=Path,required=True)
args=parser.parse_args()
old=args.original_lean_root/'SierpinskiFormal'
new=args.refactored_lean_root/'FiniteMonoidMortality'
mapping=json.loads(args.mapping.read_text())
rename={x['old'].split('.')[-1]:x['new'].split('.')[-1] for x in mapping}
rename['IndependentZeroBlocks']='FiniteMonoidMortality'
pat=re.compile(r'\b('+ '|'.join(re.escape(x) for x in sorted(rename,key=len,reverse=True))+r')\b')
def strip_comments(s):
 out=[];i=0;depth=0
 while i<len(s):
  if s[i:i+2]=='/-':depth+=1;out.extend('  ');i+=2
  elif depth and s[i:i+2]=='-/':depth-=1;out.extend('  ');i+=2
  elif not depth and s[i:i+2]=='--':
   j=s.find('\n',i);j=len(s) if j<0 else j;out.extend(' '*(j-i));i=j
  else:out.append(s[i] if not depth or s[i]=='\n' else ' ');i+=1
 return ''.join(out)
def declarations(path):
 s=strip_comments(path.read_text())
 # Source top-level commands in this development start in column zero.
 chunks=re.split(r'(?m)(?=^(?:@\[|private |theorem |def |abbrev |omit |section |end |variable |namespace |open |noncomputable |set_option |import ))',s)
 result={}
 for chunk in chunks:
  m=re.match(r'(?:@\[[^\n]*\]\s*)?(?:private )?(?:theorem|def|abbrev) (\w+)',chunk)
  if m:result[m[1]]=chunk.strip()
 return result
original={}
for p in old.glob('*.lean'):
 for name,chunk in declarations(p).items():original[name]=(p,chunk)
focused={}
for p in new.glob('*.lean'):
 for name,chunk in declarations(p).items():focused[name]=(p,chunk)
results=[]
for entry in mapping:
 oldname=entry['old'].split('.')[-1];newname=entry['new'].split('.')[-1]
 p,a=original[oldname];q,b=focused[newname]
 a=pat.sub(lambda m:rename[m[0]],a)
 norm=lambda t: re.sub(r'\s+','',t)
 a,b=norm(a),norm(b)
 ok=a==b
 results.append({**entry,'original_file':str(p.relative_to(old.parent)),'match_after_identifier_renaming_and_comment_whitespace_removal':ok,'normalized_sha256':hashlib.sha256(a.encode()).hexdigest()})
 if not ok:print('MISMATCH',oldname,repr(a[:100]),repr(b[:100]))
report={'method':'Extract top-level declaration bodies; strip comments and whitespace; apply explicit simultaneous identifier renaming; compare exact text. This is textual provenance, not a complete semantic comparison: surrounding section-variable contexts are not compared by this script. The compiled Lean Specification.lean separately checks all endpoint statements and their two custom definitions.','all_retained_declarations_equal':all(r['match_after_identifier_renaming_and_comment_whitespace_removal'] for r in results),'declarations':results}
args.output.write_text(json.dumps(report,indent=2)+'\n')
print('Source comparisons:',sum(r['match_after_identifier_renaming_and_comment_whitespace_removal'] for r in results),'/',len(results))
sys.exit(0 if report['all_retained_declarations_equal'] else 1)
