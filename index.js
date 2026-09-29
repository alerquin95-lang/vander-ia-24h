// ============================================================
// VANDER IA 24/7 — robô que coleta resultados e detecta sinais
// sozinho no servidor, mesmo com seu celular desligado.
// Deploy: Render (Web Service, plano Free) + UptimeRobot
// ============================================================
import express from 'express';
import path from 'path';
import fs from 'fs';
import { fileURLToPath } from 'url';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const app = express();
app.use(express.json());

const PORT = process.env.PORT || 10000;
const DATA_API = 'https://football-studio-real-1.onrender.com';
const COOLDOWN_MS = 20000;
const STATE_FILE = path.join(__dirname, 'signals.json');

// ---------------- estado do robô ----------------
let history = [];
let lastRoundSeenAt = 0;
let lastRoundId = null;
let lastUpdate = null;
let activeSignal = null;
let sigHistory = [];
let iaStats = { greens: 0, reds: 0, g0: 0, g1: 0, g2: 0, tieGreens: 0 };
let lastSignalAt = 0;
let lastKey = '';
let resolvedFlash = null;
const startedAt = Date.now();

//__BRAIN_START__
function detectarRegime(s){const sl=s.slice(0,20).filter(function(x){return x==='HOME'||x==='AWAY';});if(sl.length<8)return{modo:'INDEFINIDO',alt:0,streak:0,n:sl.length};let t=0;for(let i=0;i<sl.length-1;i++)if(sl[i]!==sl[i+1])t++;const al=t/(sl.length-1);let rn=[],c=1;for(let i=1;i<sl.length;i++){if(sl[i]===sl[i-1])c++;else{rn.push(c);c=1;}}rn.push(c);const md=rn.reduce(function(a,b){return a+b;},0)/rn.length;let mo='NEUTRO';if(al>=0.62)mo='ALTERNADO';else if(al<=0.38&&md>=2.2)mo='ESTICADO';return{modo:mo,alt:al,streak:md,n:sl.length};}
function deckBounds(h){const b=[];for(let i=0;i<h.length-1;i++){const a=getTs(h[i]),p=getTs(h[i+1]);if(!a||!p)continue;let g=a-p;if(g<0)g+=86400000;if(g>55000)b.push(i);}return b;}
function galeAt_A(A,k,p){for(let g=0;g<=2;g++){if(k+g>=A.length)return-1;const w=A[k+g].w;if(w===p||w==='TIE')return g;}return-1;}
function galeAt_seq(s,i0,p){for(let g=0;g<=2;g++){const ix=i0-g;if(ix<0)return-1;const w=s[ix];if(w===p||w==='TIE')return g;}return-1;}
function galeScore(h0,h1){return(h0*2+h1)/3;}
const VRULES=[
{kind:'V2UP',label:'2 acima',fire:function(W,k){if(k%6<2)return null;const a=W(k-1),b=W(k-2);return(a&&b&&a===b&&a!=='TIE')?a:null;}},
{kind:'V3UP',label:'3 acima',fire:function(W,k){if(k%6<3)return null;const a=W(k-1);return(a&&a!=='TIE'&&W(k-2)===a&&W(k-3)===a)?a:null;}},
{kind:'H2LEFT',label:'2 à esquerda',fire:function(W,k){if(Math.floor(k/6)<2)return null;const a=W(k-6),b=W(k-12);return(a&&b&&a===b&&a!=='TIE')?a:null;}},
{kind:'DIAG',label:'diagonal',fire:function(W,k){if(k%6<1||Math.floor(k/6)<1)return null;const a=W(k-1),b=W(k-7);return(a&&b&&a===b&&a!=='TIE')?a:null;}},
{kind:'ROWCHOP',label:'zigue na linha',fire:function(W,k){if(Math.floor(k/6)<4)return null;const a=W(k-6),b=W(k-12),d=W(k-18),e=W(k-24);if(!a||!b||!d||!e)return null;if(a==='TIE'||b==='TIE'||d==='TIE'||e==='TIE')return null;return(a!==b&&b!==d&&d!==e)?(a==='HOME'?'AWAY':'HOME'):null;}}];
function btVisual(A,ds){const W=function(i){return(i>=0&&i<A.length)?A[i].w:null;};const o=[];for(const ru of VRULES){let n=0,w0=0,w1=0;for(let k=Math.max(18,ds);k<A.length-2;k++){const p=ru.fire(W,k);if(!p)continue;n++;const g=galeAt_A(A,k,p);if(g===0)w0++;if(g>=0&&g<=1)w1++;}if(n>=6){const cu=ru.fire(W,A.length);if(cu){const h0=w0/n,h1=w1/n;o.push({kind:ru.kind,label:ru.label,n:n,pred:cu,hit:h1,h0:h0,h1:h1,gale:galeScore(h0,h1),visual:true});}}}return o;}
function btSeq(s,L,de){const cu=s.slice(0,L).join(',');const hh=[];const lim=Math.min(s.length-L,de);for(let i=L;i<lim;i++){if(s.slice(i,i+L).join(',')===cu)hh.push(i);}if(hh.length<4)return null;let h=0,a=0;for(const i of hh){const w=s[i-1];if(w==='HOME')h++;else if(w==='AWAY')a++;}const pr=h>=a?'HOME':'AWAY';let n=0,w0=0,w1=0;for(const i of hh){if(i-3<0)continue;n++;const g=galeAt_seq(s,i-1,pr);if(g===0)w0++;if(g>=0&&g<=1)w1++;}if(n<4)return null;const h0=w0/n,h1=w1/n;return{kind:'SEQ'+L,label:'padrão '+L+'x',n:n,pred:pr,hit:h1,h0:h0,h1:h1,gale:galeScore(h0,h1)};}
function btStreak(s,de){const t=s[0];let L=0;for(const w of s){if(w===t)L++;else break;}if(L<3||(t!=='HOME'&&t!=='AWAY'))return null;let n=0,w0=0,w1=0;const lim=Math.min(s.length-L,de);for(let i=1;i<lim;i++){let ok=true;for(let k=0;k<L;k++){if(s[i+k]!==t){ok=false;break;}}if(!ok)continue;if(i-3<0)continue;n++;const g=galeAt_seq(s,i-1,t);if(g===0)w0++;if(g>=0&&g<=1)w1++;}if(n<4)return null;const h0=w0/n,h1=w1/n;return{kind:'STREAK',label:'streak x'+L,n:n,pred:t,hit:h1,h0:h0,h1:h1,gale:galeScore(h0,h1)};}
function btRegime(s,de){const lim=Math.min(s.length-1,de);let n=0,w0=0,w1=0;for(let i=12;i<lim;i++){const mo=regimeLocal(s,i,12);if(!mo||mo==='NEUTRO')continue;const la=s[i];if(la!=='HOME'&&la!=='AWAY')continue;if(i-3<0)continue;const pr=mo==='ALTERNADO'?(la==='HOME'?'AWAY':'HOME'):la;n++;const g=galeAt_seq(s,i-1,pr);if(g===0)w0++;if(g>=0&&g<=1)w1++;}const ma=regimeLocal(s,0,12);if(!ma||ma==='NEUTRO')return null;const l0=s[0];if(l0!=='HOME'&&l0!=='AWAY')return null;const pa=ma==='ALTERNADO'?(l0==='HOME'?'AWAY':'HOME'):l0;if(n<6)return null;const h0=w0/n,h1=w1/n;return{kind:'REGIME',label:ma==='ALTERNADO'?'segue o zigue':'segue a esticada',n:n,pred:pa,hit:h1,h0:h0,h1:h1,gale:galeScore(h0,h1),modo:ma};}
function pickPattern(h){const seq=h.map(function(x){return x.winner;});const bo=deckBounds(h);const de=bo.length?bo[0]+1:h.length;const A=h.slice().reverse().map(function(x){return{w:x.winner,time:x.time||'',id:x.round_id};});const ds=A.length-de;const cd=btVisual(A,ds);for(const L of[2,3,4,5]){const r=btSeq(seq,L,de);if(r)cd.push(r);}const st=btStreak(seq,de);if(st)cd.push(st);const rg=btRegime(seq,de);if(rg)cd.push(rg);cd.forEach(function(x){x.adj=(x.gale||x.hit)-0.9/Math.sqrt(x.n);});cd.sort(function(a,b){return b.adj-a.adj;});return{best:cd[0]||null,cands:cd.slice(0,6),regime:detectarRegime(seq),A:A,deckEnd:de,deckRounds:de,deckChanged:bo.length>0&&bo[0]===0,deckCount:bo.length+1};}
function findConsensus(cd){const v=cd.filter(function(x){return x.n>=6&&(x.pred==='HOME'||x.pred==='AWAY');});const bc={};v.forEach(function(x){(bc[x.pred]=bc[x.pred]||[]).push(x);});let be=null;for(const co in bc){const ar=bc[co];if(ar.length>=2){const tn=ar.reduce(function(s,x){return s+x.n;},0);if(!be||tn>be.totalN)be={pred:co,count:ar.length,totalN:tn,labels:ar.map(function(x){return x.label;})};}}return be;}
function avaliarChance(o){const mo=[];let sc=0,pr=null;
if(o.consensus){pr=o.consensus.pred;sc+=3;mo.push(o.consensus.count+' análises apontam '+pr);if(o.consensus.totalN>=30){sc+=2;mo.push('muito testado');}else if(o.consensus.totalN>=15){sc+=1;mo.push('bem testado');}}
else if(o.best&&(o.best.pred==='HOME'||o.best.pred==='AWAY')){pr=o.best.pred;if(o.best.n>=12){sc+=2;mo.push('padrão '+o.best.label+' bem testado');}else{sc+=1;mo.push('padrão isolado ('+o.best.label+')');}}
if(!pr)return{boa:false};
if(o.surf){if(o.surf.side!==pr)return{boa:false,bloqueado:true};sc+=2;mo.push('a favor do surf ('+o.surf.len+'x)');}
if(o.pull&&o.pull.pulls&&o.pull.pulls[0].side===pr&&o.pull.pulls[0].gap>0.02){sc+=1;mo.push('lado puxando nos 400');}
if(o.minSide&&o.minSide===pr){sc+=1;mo.push('minuto puxa '+pr);}
if(o.regime&&o.regime.modo!=='NEUTRO'&&o.regime.modo!=='INDEFINIDO'&&o.lastRes){const ea=pr!==o.lastRes;if(o.regime.modo==='ALTERNADO'&&ea){sc+=2;mo.push('mesa alternando — segue o zigue');}else if(o.regime.modo==='ESTICADO'&&!ea){sc+=2;mo.push('mesa esticada — segue a sequência');}}
const gc=(o.cands||[]).filter(function(x){return x.pred===pr&&(x.gale||0)>0;});
if(gc.length){const ag=gc.reduce(function(s,x){return s+x.gale;},0)/gc.length;if(ag>=0.60){sc+=2;mo.push('padrões resolvem no G0/G1');}else if(ag>=0.50){sc+=1;mo.push('padrões bons até o G1');}}
if(o.deckRounds<8)sc-=2;
const ct=(o.cands||[]).filter(function(x){return(x.pred==='HOME'||x.pred==='AWAY')&&x.pred!==pr&&x.n>=6;});
if(ct.length>=2)sc-=1;
return{boa:sc>=4,pred:pr,score:sc,motivos:mo};}
function getTs(h){if(h&&h.ts)return h.ts;if(h&&h.time){const m=/^(\d{1,2}):(\d{2})(?::(\d{2}))?/.exec(String(h.time).trim());if(m){const d=new Date();d.setHours(+m[1],+m[2],+(m[3]||0),0);return d.getTime();}}return 0;}
function regimeLocal(s,st,w){const sl=s.slice(st,st+w).filter(function(x){return x==='HOME'||x==='AWAY';});if(sl.length<6)return null;let t=0;for(let i=0;i<sl.length-1;i++)if(sl[i]!==sl[i+1])t++;const al=t/(sl.length-1);if(al>=0.62)return'ALTERNADO';if(al<=0.38)return'ESTICADO';return'NEUTRO';}
function minuteMap(h){const m={};for(const x of h){const ts=getTs(x);if(!ts)continue;const mn=new Date(ts).getMinutes();const e=m[mn]||(m[mn]={HOME:0,AWAY:0,TIE:0,n:0});if(e[x.winner]!==undefined){e[x.winner]++;e.n++;}}return m;}
function tieIntel(A,ds){const map={};for(let i=Math.max(3,ds);i<A.length-3;i++){const k=A[i].w+','+A[i+1].w+','+A[i+2].w;const e=map[k]||(map[k]={n:0,tie:0});e.n++;if(A[i+3]&&A[i+3].w==='TIE')e.tie++;}const top=Object.entries(map).filter(function(x){return x[1].n>=4;}).map(function(x){return{k:x[0],p:x[1].tie/x[1].n,n:x[1].n};}).sort(function(a,b){return b.p-a.p;}).slice(0,3);const ti=[];A.forEach(function(x,i){if(x.w==='TIE')ti.push(i);});let avg=null;if(ti.length>=2){let s=0;for(let i=1;i<ti.length;i++)s+=ti[i]-ti[i-1];avg=Math.round(s/(ti.length-1));}return{top:top,avgGap:avg,sinceTie:ti.length?(A.length-1-ti[ti.length-1]):null};}
function fullPull(h){const seq=h.map(function(x){return x.winner;});const total=seq.length||1;const cnt=function(a){const r={HOME:0,AWAY:0,TIE:0};a.forEach(function(x){if(r[x]!==undefined)r[x]++;});return r;};const cA=cnt(seq),c3=cnt(seq.slice(0,30));const n3=Math.min(30,seq.length)||1;const pl=['HOME','AWAY'].map(function(s){return{side:s,gap:(c3[s]/n3)-(cA[s]/total)};}).sort(function(a,b){return b.gap-a.gap;});return{pulls:pl,total:seq.length};}
function analyzeAI(h){
if(h.length<10)return{ready:false,msg:'Aguardando dados ('+h.length+'/10)'};
const pk=pickPattern(h),best=pk.best,A=pk.A,cd=pk.cands,cs=findConsensus(cd),seq=h.map(function(x){return x.winner;});
const co=function(a){const r={HOME:0,AWAY:0,TIE:0};a.forEach(function(x){if(r[x]!==undefined)r[x]++;});return r;};
const c10=co(seq.slice(0,10)),c20=co(seq.slice(0,20)),c50=co(seq.slice(0,50));
let st=seq[0],sl=0;for(const w of seq){if(w===st)sl++;else break;}
let surf=null;if((st==='HOME'||st==='AWAY')&&sl>=4)surf={side:st,len:sl};
const pa={};for(let i=0;i<seq.length-1;i++){const k=seq[i]+' > '+seq[i+1];pa[k]=(pa[k]||0)+1;}
const tp=Object.entries(pa).sort(function(a,b){return b[1]-a[1];}).slice(0,4);
let mT='',mS=null;const mH=[];const mM=minuteMap(h),nM=new Date().getMinutes(),me=mM[nM];
if(me&&me.n>=6){const pH=me.HOME/me.n,pA=me.AWAY/me.n;mS=pH>=pA?'HOME':'AWAY';const p=Math.max(pH,pA);if(p>=0.58)mT=':'+String(nM).padStart(2,'0')+' puxa '+mS+' '+Math.round(p*100)+'%';}
Object.entries(mM).forEach(function(x){const v=x[1];if(v.n>=6){const pH=v.HOME/v.n,pA=v.AWAY/v.n,p=Math.max(pH,pA);if(p>=0.58)mH.push({min:+x[0],n:v.n,side:pH>=pA?'HOME':'AWAY',p:p});}});
mH.sort(function(a,b){return b.p-a.p;});if(mH.length>4)mH.length=4;
const ti=tieIntel(A,A.length-pk.deckEnd);
const fc=btVisual(A,0);fc.forEach(function(x){x.adj=(x.gale||x.hit)-0.9/Math.sqrt(x.n);});fc.sort(function(a,b){return b.adj-a.adj;});
const pu=fullPull(h),rg=pk.regime,lr=(seq[0]==='HOME'||seq[0]==='AWAY')?seq[0]:null;
const ch=avaliarChance({cands:cd,consensus:cs,best:best,surf:surf,pull:pu,minSide:mS,deckRounds:pk.deckRounds,regime:rg,lastRes:lr});
let sg='OBSERVANDO',et=null;
if(ch.boa){sg='CHANCE BOA';et={pred:ch.pred,motivos:ch.motivos,label:'Chance boa: '+ch.pred};}
return{ready:true,signal:sg,entry:et,chance:ch,consensus:cs,regime:rg,surf:surf,c10:c10,c20:c20,c50:c50,topPairs:tp,best:best,cands:cd,deckRounds:pk.deckRounds,deckChanged:pk.deckChanged,deckCount:pk.deckCount,minTxt:mT,minSide:mS,minHot:mH,tieTop:ti.top,tieAvg:ti.avgGap,tieSince:ti.sinceTie,fullBest:fc[0]||null,pull:pu};}
function betWindow(){const l=10000-(Date.now()-lastRoundSeenAt);return{open:l>0,leftMs:Math.max(0,l)};}
//__BRAIN_END__

// ---------------- ciclo de sinais (memória, sem navegador) ----------------
function saveState(){
  try{ fs.writeFileSync(STATE_FILE, JSON.stringify({sigHistory, iaStats, lastSignalAt, lastKey, savedAt: Date.now()})); }catch(e){}
}
function loadState(){
  try{
    if(fs.existsSync(STATE_FILE)){
      const s = JSON.parse(fs.readFileSync(STATE_FILE,'utf-8'));
      sigHistory = s.sigHistory||[]; iaStats = Object.assign(iaStats, s.iaStats||{});
      lastSignalAt = s.lastSignalAt||0; lastKey = s.lastKey||'';
      console.log('[robô] histórico recuperado:', sigHistory.length, 'sinais');
    }
  }catch(e){}
}
function persistIA(){ saveState(); }

function maybeCreateSignal(ai,h){
  if(activeSignal) return;
  if(resolvedFlash && Date.now()-resolvedFlash.at <= 12000) return;
  if(!ai.ready || !h.length) return;
  const et = ai.entry;
  if(!et) return;
  if(ai.surf && et.pred !== ai.surf.side) return;
  if(!betWindow().open) return;
  if(Date.now()-lastSignalAt < COOLDOWN_MS) return;
  const key = 'chance:'+et.pred;
  if(key === lastKey) return;
  activeSignal = {id: Date.now(), entry: et.pred, time: new Date().toLocaleTimeString('pt-BR'), afterRoundId: h[0].round_id, gales: 0, label: et.label, motivos: et.motivos};
  lastSignalAt = Date.now(); lastKey = key;
  console.log('[SINAL 24/7] '+et.pred+' — '+et.label);
  persistIA();
}

function processSignals(h){
  const now = Date.now();
  if(!activeSignal) return;
  if(now-activeSignal.id > 1200000){
    sigHistory.unshift(Object.assign({}, activeSignal, {status:'EXPIRED', result:'—', galesUsed: activeSignal.gales, endedAt: now}));
    sigHistory = sigHistory.slice(0,50); activeSignal = null; persistIA(); return;
  }
  const ix = h.findIndex(function(x){ return String(x.round_id)===String(activeSignal.afterRoundId); });
  if(ix <= 0) return;
  const nw = h.slice(0, ix);
  const rs = nw.find(function(x){ return x.winner==='HOME'||x.winner==='AWAY'||x.winner==='TIE'; });
  if(!rs) return;
  const w = rs.winner;
  if(w === activeSignal.entry || w === 'TIE'){
    const g = activeSignal.gales;
    iaStats.greens++;
    if(g===0) iaStats.g0++; else if(g===1) iaStats.g1++; else iaStats.g2++;
    if(w==='TIE') iaStats.tieGreens = (iaStats.tieGreens||0)+1;
    sigHistory.unshift(Object.assign({}, activeSignal, {status:'GREEN', result:w, galesUsed:g, endedAt:now}));
    sigHistory = sigHistory.slice(0,50);
    console.log('[GREEN 24/7] '+activeSignal.entry+' no G'+g+' ('+w+')');
    resolvedFlash = {signal: sigHistory[0], at: now};
    activeSignal = null; persistIA();
  }
  else if(activeSignal.gales < 2){
    activeSignal.gales++;
    activeSignal.afterRoundId = rs.round_id;
    console.log('[GALE 24/7] '+activeSignal.entry+' → G'+activeSignal.gales);
    persistIA();
  }
  else{
    iaStats.reds++;
    sigHistory.unshift(Object.assign({}, activeSignal, {status:'RED', result:w, galesUsed:2, endedAt:now}));
    sigHistory = sigHistory.slice(0,50);
    console.log('[RED 24/7] '+activeSignal.entry+' (saiu '+w+')');
    resolvedFlash = {signal: sigHistory[0], at: now};
    activeSignal = null; persistIA();
  }
}

// ---------------- coletor de rodadas ----------------
function normRound(r){
  let winner = r.winner;
  if(!winner && r.result){
    const v = String(r.result).toUpperCase();
    if(v.includes('BANKER')||v==='HOME'||v==='H') winner='HOME';
    else if(v.includes('PLAYER')||v==='AWAY'||v==='P') winner='AWAY';
    else winner='TIE';
  }
  const round_id = r.round_id ?? r.round ?? r.id ?? r.round_number;
  let ts = r.ts;
  if(!ts && r.created_at){ const t = Date.parse(r.created_at); if(!isNaN(t)) ts = t; }
  if(!winner || round_id==null) return null;
  return { round_id, winner, time: r.time, ts };
}

async function collect(){
  try{
    const r = await fetch(DATA_API+'/api/rounds');
    if(!r.ok){ console.log('[coleta] API respondeu', r.status); return; }
    const j = await r.json();
    const h = (j.data||j.history||[]).map(normRound).filter(Boolean);
    if(!h.length) return;
    const topId = String(h[0].round_id);
    if(topId !== String(lastRoundId)){
      lastRoundId = topId;
      lastRoundSeenAt = Date.now();
      history = h;
      lastUpdate = new Date().toISOString();
      onNewRound();
    }
  }catch(e){ console.log('[coleta] erro:', e.message); }
}

function onNewRound(){
  const h = history;
  if(h.length < 10) return;
  processSignals(h);
  try{ maybeCreateSignal(analyzeAI(h), h); }
  catch(e){ console.log('[análise] erro:', e.message); }
}
setInterval(collect, 5000);

// ---------------- API do robô ----------------
app.get('/api/health', (req,res)=>{
  res.json({ online:true, service:'vander-ia-24h',
    uptime_min: Math.round((Date.now()-startedAt)/60000),
    lastUpdate, totalRounds: history.length,
    activeSignal: !!activeSignal, totalSignals: sigHistory.length, stats: iaStats });
});
app.get('/api/signals', (req,res)=>{
  res.json({ signals: sigHistory, active: activeSignal, stats: iaStats, lastUpdate });
});
app.get('/api/rounds', (req,res)=>{ res.json({ data: history, lastUpdate }); });
app.get('/api/stats', (req,res)=>{
  const c = {HOME:0, AWAY:0, TIE:0};
  history.forEach(function(x){ if(c[x.winner]!==undefined) c[x.winner]++; });
  res.json({ stats: c, total: history.length, lastUpdate });
});

// ---------------- site (dashboard + admin) ----------------
app.use(express.static(__dirname));

loadState();
collect();
app.listen(PORT, ()=>{
  console.log('==========================================');
  console.log('🤖 VANDER IA 24/7 no ar! porta '+PORT);
  console.log('📡 Coletando de: '+DATA_API);
  console.log('==========================================');
});
