import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { resolve } from "node:path";
// 输入为 ScopeTrace.rs_proof 导出的原 Hilbert 树。这里只产生候选分配，须交回 Lean 验证。
// 重复公式先合并量词范围；其余要求化为 L(v) ≥ L(u)+d，严格正环表示当前策略无解。
// 当前理论叶支持原收集模式；未覆盖的理论公理直接拒绝。split 使用已证明的输入 guard。
export function sr_solve(source,policy="split"){
 if(!["split","shared"].includes(policy))throw Error("未知范围策略");
 const labels=[],parent=[],rank=[],edges=[],equalities=[],nodes=[],collections=[];
 const fresh=label=>{let i=labels.length;labels.push(label);parent.push(i);rank.push(0);return i};
 const find=i=>parent[i]===i?i:(parent[i]=find(parent[i]));
 function eqv(a,b,why){equalities.push([a,b,why]);a=find(a);b=find(b);if(a===b)return;if(rank[a]<rank[b])[a,b]=[b,a];parent[b]=a;if(rank[a]===rank[b])rank[a]++}
 const le=(a,b,d,why)=>edges.push([a,b,d,why]);
 function ann(f,n,path="r"){const t=f[0],a={t,raw:f,k:[],n,path};
  if(t==="all"||t==="ex"){a.q=fresh(`n${n}.q:${path}:${t}`);a.k=[ann(f[1],n,path+"0")]}
  else if(t==="not")a.k=[ann(f[1],n,path+"0")];
  else if(["and","or","imp","iff"].includes(t))a.k=[ann(f[1],n,path+"0"),ann(f[2],n,path+"1")];return a}
 function same(a,b,why){if(a.t!==b.t||a.k.length!==b.k.length)throw Error(`shape mismatch ${why}`);if(a.q!==undefined)eqv(a.q,b.q,why);a.k.forEach((c,i)=>same(c,b.k[i],why))}
 const at=(a,p)=>{for(const i of p)a=a.k[i];return a};
 function qs(a,out=[]){if(a.q!==undefined)out.push(a.q);for(const b of a.k)qs(b,out);return out}
 const termLevel=(n,t)=>{if(t?.[0]!=="f"||t[1]>=n.v.length)throw Error("Unexpected term");return n.v[t[1]]};
 function normalize(f,drop,depth=0){const t=f[0],tm=v=>{if(v[0]!=="b"||v[1]<depth)return v;const k=v[1]-depth;if(drop.includes(k))throw Error("Fresh binder in matrix");return["b",v[1]-drop.filter(j=>j<k).length]};
  if(t==="eq"||t==="mem")return[t,tm(f[1]),tm(f[2])];
  if(t==="all"||t==="ex")return[t,normalize(f[1],drop,depth+1)];
  if(t==="not")return[t,normalize(f[1],drop,depth)];
  if(["imp","iff","and","or"].includes(t))return[t,normalize(f[1],drop,depth),normalize(f[2],drop,depth)];return f}
 function collect(n){let a=n.a,prefix=[];while(a.t==="all"){prefix.push(a.q);a=a.k[0]}
  if(a.t!=="imp"||!prefix.length)throw Error("Unsupported theory axiom");const l=a.k[0],r=a.k[1];
  if(l.t!=="all"||l.k[0].t!=="imp"||l.k[0].k[1].t!=="ex"||r.t!=="ex"||r.k[0].t!=="all"||
     r.k[0].k[0].t!=="imp"||r.k[0].k[0].k[1].t!=="ex"||r.k[0].k[0].k[1].k[0].t!=="and")throw Error("Not Collection");
  const pm=at(l,[0,1,0]),post=at(r,[0,0,1,0,1]);if(JSON.stringify(normalize(pm.raw,[2]))!==JSON.stringify(normalize(post.raw,[2,3])))throw Error("Matrix mismatch");
  const E=r.q,I=l.q,W=at(l,[0,1]).q,J=at(r,[0]).q,A=prefix.at(-1);
  prefix.slice(0,-1).forEach(q=>eqv(q,E,`n${n.id}:parameter range`));
  eqv(A,policy==="shared"?E:I,`n${n.id}:input set range`);
  if(policy==="shared")eqv(I,J,`n${n.id}:shared input range`);
  eqv(W,at(r,[0,0,1]).q,`n${n.id}:witness range`);same(pm,post,`n${n.id}:matrix copies`);
  const matrix=qs(pm);matrix.slice(1).forEach(q=>eqv(matrix[0],q,`n${n.id}:body range`));
  le(W,E,1,`n${n.id}:P(W) included in E`);collections.push({node:n.id,A,E,I,J,W,R:matrix[0]??null})}
 const patterns={
  0:[[[0,0],[1,0,0]],[[0,0],[1,1,0]],[[0,1,0],[1,0,1]],[[0,1,1],[1,1,1]]],
  1:[[[0],[1,0]],[[0],[1,1]]],2:[[[0],[1,1]]],3:[[[0],[1,0,0]]],
  4:[[[0,0,0],[0,1]],[[0,1],[1]]],5:[[[0,0],[1,0]]],
  6:[[[0,0],[1,0,0,0]],[[0,1],[1,0,1]],[[0,1],[1,1]]],7:[],8:[],
  9:[[[0,0],[1,0]]],10:[[[0],[1,0,0]]],11:[[[0],[1,1,0]],[[1,0],[1,1,1]]],
  12:[[[0,0],[1]]],13:[[[0,1],[1]]],14:[[[0],[1,0]]],15:[[[0],[1,1]]],
  16:[[[0,0],[1,1,0,0]],[[1,0,0],[1,1,0,1]],[[0,1],[1,0,1]],[[0,1],[1,1,1]]],
  17:[[[0,0],[1,0,1]],[[0,0],[1,1,0]],[[0,1],[1,0,0]],[[0,1],[1,1,1]]],
  18:[[[0,0],[1,0]],[[0,1],[1,1]]],19:[[[0,1],[1,0]],[[0,0],[1,1]]],
  20:[[[0,0],[1]]],21:[[[0,0,0],[1,0,0]],[[0,0,1],[1,1,0]]],
  22:[[[0],[1,0]]],23:[[[0],[1,0]]],24:[[[0,0,0],[1,0,0]],[[0,0,1],[1,1]]],
  25:[[[1,0],[1,1]]],26:[]};
 function ax(n,tag,term){const a=n.a,why=`n${n.id}:axiom ${tag}`;if(!patterns[tag])throw Error("Unknown axiom");
  for(const [p,q]of patterns[tag])same(at(a,p),at(a,q),why);
  if(tag===20)le(termLevel(n,term),at(a,[0]).q,0,why+":specialization");
  if(tag===23)le(termLevel(n,term),at(a,[1]).q,0,why+":existential witness");
  if(tag===21){le(at(a,[1,1]).q,at(a,[0]).q,0,why+":forall implication");le(at(a,[1,1]).q,at(a,[1,0]).q,0,why+":forall premise")}
  if(tag===24)le(at(a,[1,0]).q,at(a,[0]).q,0,why+":exists elimination")}
 function build(p){const id=nodes.length,n={id,kind:p[2],v:Array.from({length:p[0]},(_,j)=>fresh(`n${id}.v${j}`)),a:ann(p[1],id)};nodes.push(n);
  function env(c,offset=0){if(n.v.length+offset!==c.v.length)throw Error("Free-context mismatch");n.v.forEach((v,j)=>le(v,c.v[j+offset],0,`n${id}->n${c.id}:environment`))}
  if(p[2]==="L")ax(n,p[3],p[4]);else if(p[2]==="T")collect(n);
  else if(p[2]==="M"){const c=build(p[3]),d=build(p[4]);env(c);env(d);same(c.a,d.a.k[0],`n${id}:MP premise`);same(n.a,d.a.k[1],`n${id}:MP result`)}
  else if(p[2]==="G"){const c=build(p[3]);env(c,1);le(n.a.q,c.v[0],0,`n${id}:generalization binder`);same(n.a.k[0],c.a,`n${id}:generalization body`)}
  else if(p[2]==="W"){const c=build(p[3]);env(c,1);same(n.a,c.a,`n${id}:strengthening`)}
  else if(p[2]==="S"){const c=build(p[4]);if(p[3].length!==c.v.length)throw Error("Substitution size");p[3].forEach((t,j)=>le(termLevel(n,t),c.v[j],0,`n${id}:substitution ${j}`));same(n.a,c.a,`n${id}:substitution body`)}
  else throw Error("Unknown rule");return n}
 const root=build(source),zero=fresh("base-domain");root.v.forEach(v=>le(v,zero,0,"root old parameter"));
 const representatives=[...new Set(labels.map((_,i)=>find(i)))],index=new Map(representatives.map((r,i)=>[r,i]));
 const es=edges.map(([a,b,d,why])=>[index.get(find(a)),index.get(find(b)),d,why,a,b]),values=representatives.map(()=>0),pred=representatives.map(()=>null);
 let changed=-1,iterations=0;for(let k=0;k<representatives.length;k++){changed=-1;for(let j=0;j<es.length;j++){const[a,b,d]=es[j];if(values[b]<values[a]+d){values[b]=values[a]+d;pred[b]=j;changed=b}}iterations=k+1;if(changed<0)break}
 let cycle=null;if(changed>=0){let x=changed;for(let i=0;i<representatives.length;i++)x=es[pred[x]][0];const start=x;cycle=[];do{const e=es[pred[x]];cycle.push({from:labels[e[4]],to:labels[e[5]],step:e[2],why:e[3]});x=e[0]}while(x!==start&&cycle.length<=representatives.length)}
 const val=i=>values[index.get(find(i))];const out={policy,feasible:cycle===null,nodes:nodes.length,variables:labels.length,equalities:equalities.length,inequalities:edges.length,components:representatives.length,iterations,maxLevel:cycle?null:Math.max(...values),rootFree:cycle?null:root.v.map(val),rootQuantifiers:cycle?null:qs(root.a).map(val),collections:collections.map(c=>({node:c.node,levels:cycle?null:Object.fromEntries(["A","E","I","J","W","R"].map(k=>[k,c[k]===null?null:val(c[k])]))})),cycle};
 return{labels,parents:parent.map(find),edges,equalities,nodes,collections,values:labels.map((_,i)=>val(i)),out};
}
if (process.argv[1] && fileURLToPath(import.meta.url) === resolve(process.argv[1])) {
 const [file,...flags]=process.argv.slice(2);
 if(!file||flags.some(f=>f!=="--shared-inputs"))throw Error("用法：node scripts/scope_ranges.mjs 证明.json [--shared-inputs]");
 // 旧的共用输入范围策略仅用于复现冲突；默认前件与结论分别分配 I、J。
 const result=sr_solve(JSON.parse(readFileSync(file,"utf8")),flags.includes("--shared-inputs")?"shared":"split");
 process.stdout.write(JSON.stringify(result.out,null,2)+"\n");
}
